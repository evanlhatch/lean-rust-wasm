//! mandate-rt — the wasmi standalone runtime (D1's third duel leg).
//!
//! THE DISCIPLINE, NOT THE CODE (notes/design-wave-30.md D1 — the
//! port of legacy guestlang-rt's determinism contract onto the new
//! tree's shared profile): a pure-Rust, fuel-metered interpreter
//! running the COMPILER LINE's output — core wasm only; the component
//! wrapper (canonical ABI + WIT) is the wasmtime host's job.
//!
//! THE PROFILE AS THE ENGINE'S CONFIG (WasmCore.Profile — the one
//! table): `Runtime::new` builds the wasmi config FROM the committed
//! `gen/wasm-duel/profile.txt` (parsed in [`profile`]) — fuel on,
//! floats off, memory64/multi-memory/wide-arithmetic/custom-page-sizes
//! off, lazy-translation pinned, the simd axis carried by the
//! dependency edge (no `simd` crate feature). A spec bug that starts
//! emitting outside the closed fragment = a LOAD refusal here, never
//! silent nondeterminism.
//!
//! THE STABLE-FUEL PIN: wasmi 2.0's stable fuel metering — identical
//! module + args → identical fuel consumption across runs (the
//! conformance test asserts it; an upstream fuel-accounting change
//! becomes a noticed gate failure, never a silent ABI drift).
//!
//! THE IMPORT BOUNDARY: the standalone rt provides NO host
//! functionality — every import the module declares is linked as a
//! LOUD trap (sync exports never call them; an async fn traps at its
//! first task-intrinsic call — the honest boundary; async requires a
//! wasi 0.3 host: wasmtime / the later host lane).
//!
//! ERROR DISCIPLINE (12 §8): no panics on real error paths, no
//! unsafe — every failure is a [`RtError`].

pub mod profile;

use wasmi::{Val, ValType};

pub use profile::{
    CompilationMode, DeterministicProfile, ProfileError, load_profile, parse_profile,
};

/// The typed error surface (the one-writer stringification: wasmi's
/// Display carries the cause chain).
#[derive(Debug)]
pub struct RtError(pub String);

impl std::fmt::Display for RtError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for RtError {}

impl From<wasmi::Error> for RtError {
    fn from(e: wasmi::Error) -> Self {
        Self(format!("wasmi: {e}"))
    }
}

impl From<ProfileError> for RtError {
    fn from(e: ProfileError) -> Self {
        Self(format!("profile: {e}"))
    }
}

/// The repo's gen directory (the committed universe — the duel lane's
/// artifacts + the profile; the crate is a consumer of the artifact
/// spine, never a second emitter).
pub fn repo_gen_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../gen")
}

/// THE ENGINE CONFIG FROM THE SHARED PROFILE (the one table — the
/// wasmi face of WasmCore.Profile): every axis of the parsed profile
/// is APPLIED or the axis is named in an honest refusal — a new
/// profile field breaks this function's compile until it is applied
/// (the never-two-hand-synced-configs discipline's compile tooth).
fn wasmi_config(p: &DeterministicProfile) -> Result<wasmi::Config, RtError> {
    // The FEATURE axis first: simd is a compile-time crate feature
    // (NOT a config knob — the dependency edge carries its absence).
    // A profile demanding simd would need a rebuilt dependency; the
    // runtime refuses loudly rather than run an unprofiled engine.
    if p.simd {
        return Err(RtError(
            "profile: simd demanded — the wasmi dependency edge carries simd OFF \
             (WasmCore.Profile: the feature axis, not a config knob); rebuild the \
             dependency deliberately, never implicitly"
                .into(),
        ));
    }
    let mut cfg = wasmi::Config::default();
    // THE fuel knob: the deterministic resource bound.
    cfg.consume_fuel(p.consume_fuel);
    // THE memory + arithmetic axes: the engine refuses the feature at
    // load when the profile turns it off.
    cfg.wasm_memory64(p.memory64);
    cfg.wasm_multi_memory(p.multi_memory);
    cfg.wasm_wide_arithmetic(p.wide_arithmetic);
    cfg.wasm_custom_page_sizes(p.custom_page_sizes);
    // THE floats axis: OFF — the f64 in the WIT world is a TYPE; the
    // core module has zero f64 instructions (the f64-refusal negative
    // control pins the refusal).
    cfg.floats(p.floats);
    // THE compilation pin: lazy-translation is wasmi 2.0's
    // deterministic mode (`Lazy` may diverge across implementations).
    cfg.compilation_mode(match p.compilation {
        CompilationMode::LazyTranslation => wasmi::CompilationMode::LazyTranslation,
        CompilationMode::Eager => wasmi::CompilationMode::Eager,
        CompilationMode::Lazy => wasmi::CompilationMode::Lazy,
    });
    Ok(cfg)
}

/// Build the wasmi engine from the parsed profile (the ONE construction
/// per engine — callers compose, never re-walk Config → Engine).
pub fn profile_engine(p: &DeterministicProfile) -> Result<wasmi::Engine, RtError> {
    Ok(wasmi::Engine::new(&wasmi_config(p)?))
}

/// Compile + invoke one export on the wasmi engine, fuel-metered (the
/// one-shot face; the scalar-ABI `i64` args are COERCED to the
/// export's param types — the introspection, not a per-fn table).
pub fn invoke_core(wasm: &[u8], func: &str, args: &[i64], fuel: u64) -> Result<Vec<i64>, RtError> {
    invoke_core_fueled(wasm, func, args, fuel).map(|(r, _)| r)
}

/// `invoke_core` + the fuel actually consumed (wasmi 2.0's STABLE fuel
/// metering: identical module + args → identical fuel across runs AND
/// across wasmi versions — the pin the conformance test asserts).
pub fn invoke_core_fueled(
    wasm: &[u8],
    func: &str,
    args: &[i64],
    fuel: u64,
) -> Result<(Vec<i64>, u64), RtError> {
    Runtime::new(wasm, fuel)?.call(func, args, fuel)
}

/// The duel's observation face (the triangle's wasmi leg): run the
/// module's ONE export (`() -> i64`) in a fresh engine and report the
/// OBSERVATION — a value, the typed trap code, or a load refusal.
/// The engine config rides the shared profile (never a hand config).
pub fn observe(wasm: &[u8]) -> Result<Result<i64, String>, RtError> {
    let profile = load_profile(&repo_gen_dir())?;
    let engine = profile_engine(&profile)?;
    let module = wasmi::Module::new(&engine, wasm)?;
    let mut store = wasmi::Store::new(&engine, ());
    if profile.consume_fuel {
        store.set_fuel(u64::MAX / 2)?;
    }
    let mut linker = <wasmi::Linker<()>>::new(&engine);
    stub_imports(&module, &mut linker)?;
    let instance = linker.instantiate_and_start(&mut store, &module)?;
    let f = instance
        .get_export(&store, "answer")
        .and_then(wasmi::Extern::into_func)
        .ok_or_else(|| RtError("no export: answer".into()))?;
    let params: Vec<ValType> = f.ty(&store).params().to_vec();
    if !params.is_empty() {
        return Err(RtError(format!(
            "the duel's entry takes no params, got {}",
            params.len()
        )));
    }
    let n = f.ty(&store).results().len();
    let mut results = vec![Val::I64(0); n];
    match f.call(&mut store, &[], &mut results) {
        // THE typed runtime trap — the duel's `.trap` vocabulary.
        Err(e) => match e.as_trap_code() {
            Some(code) => Ok(Err(format!("trap: {code}"))),
            None => Err(RtError(format!("call: {e}"))),
        },
        Ok(()) => {
            if n != 1 {
                return Err(RtError(format!("expected one result, got {n}")));
            }
            Ok(Ok(match &results[0] {
                Val::I64(x) => *x,
                Val::I32(x) => *x as i64,
                v => return Err(RtError(format!("unexpected result val: {v:?}"))),
            }))
        }
    }
}

/// The import boundary: every declared import is linked as a LOUD trap
/// (generic over the module's OWN import table — new intrinsics need
/// no rt change; a non-func import is a hard error).
fn stub_imports(module: &wasmi::Module, linker: &mut wasmi::Linker<()>) -> Result<(), RtError> {
    for import in module.imports() {
        let Some(ft) = import.ty().func() else {
            return Err(RtError(format!(
                "mandate-rt: non-func import `{}::{}` — not supported standalone",
                import.module(),
                import.name()
            )));
        };
        linker
            .func_new(import.module(), import.name(), ft.clone(), |_, _, _| {
                Err(wasmi::Error::new(
                    "mandate-rt: async task-intrinsic called — async \
                     requires a wasi 0.3 host (wasmtime / the host lane)",
                ))
            })
            .map_err(|e| RtError(format!("wasmi: {e}")))?;
    }
    Ok(())
}

/// A RETAINED wasmi instance: the same heap across calls (the pooled
/// allocator's free-lists persist between `call`s — unlike the
/// one-shot `invoke_core`). Built under THE deterministic profile
/// (the shared profile file — never a hand config).
pub struct Runtime {
    store: wasmi::Store<()>,
    instance: wasmi::Instance,
}

impl Runtime {
    /// Build a retained instance under THE DETERMINISTIC PROFILE,
    /// ENFORCED (the engine's feature set = the profile's closed
    /// universe, parsed from the committed profile file).
    pub fn new(wasm: &[u8], fuel: u64) -> Result<Self, RtError> {
        let profile = load_profile(&repo_gen_dir())?;
        let engine = profile_engine(&profile)?;
        let module = wasmi::Module::new(&engine, wasm)?;
        let mut store = wasmi::Store::new(&engine, ());
        store.set_fuel(fuel)?;
        let mut linker = <wasmi::Linker<()>>::new(&engine);
        stub_imports(&module, &mut linker)?;
        let instance = linker.instantiate_and_start(&mut store, &module)?;
        Ok(Self { store, instance })
    }

    /// Invoke one export on the RETAINED instance, fuel-metered for
    /// this call (the heap PERSISTS across calls).
    pub fn call(
        &mut self,
        func: &str,
        args: &[i64],
        fuel: u64,
    ) -> Result<(Vec<i64>, u64), RtError> {
        let store = &mut self.store;
        let instance = &self.instance;
        let f = instance
            .get_export(&*store, func)
            .and_then(wasmi::Extern::into_func)
            .ok_or_else(|| RtError(format!("no export: {func}")))?;
        // Coerce the scalar-ABI i64 args into the export's param types.
        let params: Vec<ValType> = f.ty(&*store).params().to_vec();
        if params.len() != args.len() {
            return Err(RtError(format!(
                "arity: {func} expects {} args, got {}",
                params.len(),
                args.len()
            )));
        }
        let vals: Vec<Val> = params
            .iter()
            .zip(args.iter())
            .map(|(t, a)| match t {
                ValType::I32 => Val::I32(*a as i32),
                _ => Val::I64(*a),
            })
            .collect();
        let mut results = vec![Val::I64(0); f.ty(&*store).results().len()];
        store.set_fuel(fuel)?;
        f.call(&mut *store, &vals, &mut results)?;
        let remaining = store.get_fuel()?;
        let out = results
            .iter()
            .map(|v| match v {
                Val::I64(x) => *x,
                Val::I32(x) => *x as i64,
                _ => 0,
            })
            .collect();
        Ok((out, fuel - remaining))
    }

    /// Fuel remaining in the store right now.
    pub fn fuel(&self) -> Result<u64, RtError> {
        Ok(self.store.get_fuel()?)
    }
}

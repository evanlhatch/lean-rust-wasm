//! guestlang-rt — the standalone embeddable WASM interpreter.
//!
//! wasmi 2.0: pure-Rust, deterministic, fuel-metered. CORE wasm only —
//! the component wrapper (canonical ABI + WIT) is the wasmtime host's
//! job; this runtime runs the COMPILER LINE's output directly.
//!
//! Resource story: fuel (deterministic instruction counting) + the
//! pooled allocator in the guest itself. Snapshot/restore = the honest
//! v1 memory-image contract (`Runtime` / `Snapshot` below): linear
//! memory + fuel remaining. rkyv lands next; the worker pool (the
//! "Monty pattern" — thread-pool + engine-level limits in v1, the
//! subprocess mode documented as the follow-up) is `pool` below.

mod pool;

pub use pool::{Job, Pool, PoolError};

use wasmi::{Val, ValType};

/// Compile + invoke one export on the wasmi engine, fuel-metered.
/// Any arity: args/results flow as i64 (the guestlang scalar ABI);
/// i64 args are COERCED to the export's param types (the canonical-ABI
/// flat bool param is I32 — the introspection here, not a per-fn table).
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

/// A RETAINED wasmi instance: the same heap across calls (the pooled
/// allocator's free-lists + the `$alloc`/`$rc_inc`/`$rc_dec` object
/// model persist between `call`s — unlike the one-shot `invoke_core`).
/// `snapshot()` captures the honest v1 state; `Snapshot::restore`
/// rebuilds it into a fresh instance.
pub struct Runtime {
    store: wasmi::Store<()>,
    instance: wasmi::Instance,
}

/// The honest v1 snapshot: the guest's LINEAR MEMORY image + the fuel
/// remaining at capture. THE GLOBALS GAP (documented, deliberate):
/// wasmi 2.0's public API reaches globals only through export names
/// (`Instance::get_global(store, name)` — export-table lookup), and the
/// compiler line's modules export NO globals — the adapter stash
/// (`$wr_g`/`$arr_g`/`$n_g`) and the allocator cursors (`heap`,
/// `heap-end`) are non-exported, i.e. UNREACHABLE from outside the
/// store. Consequence: a restored instance = a FRESH instance whose
/// memory was pre-dirtied by the image — the allocator re-bumps from
/// its init cursor, so POINTER IDENTITY ACROSS RESTORE IS NOT
/// GUARANTEED (only results-coherence, which the tests pin). The fix
/// is upstream API surface (a globals iterator), not a hack here.
#[derive(Debug, Clone)]
pub struct Snapshot {
    memory: Vec<u8>,
    fuel: u64,
}

impl Runtime {
    /// Build a retained instance under THE DETERMINISTIC PROFILE,
    /// ENFORCED (seam-contract #10's runtime mirror): the engine's
    /// feature set = the SPEC's closed universe.
    // The Lean spec's compiled fragment = integer-only structured
    // control flow — so the ENGINE REFUSES everything else at module
    // load: no floats (the f64 in the WIT world is a TYPE, the core
    // module has zero f64 instructions), no simd/memory64/multi-memory/
    // relaxed-simd/extended-const. A spec bug that starts emitting
    // outside the fragment = a LOAD failure here, not silent
    // nondeterminism. LazyTranslation (the default) = the deterministic
    // compilation mode (wasmi 2.0: `Lazy` is the one that may diverge
    // across implementations); consume_fuel = the deterministic bound.
    pub fn new(wasm: &[u8], fuel: u64) -> Result<Self, RtError> {
        let mut cfg = wasmi::Config::default();
        cfg.consume_fuel(true);
        cfg.compilation_mode(wasmi::CompilationMode::LazyTranslation);
        cfg.floats(false);
        // simd/relaxed-simd = compile-time crate features (NOT config knobs) —
        // already absent from the default feature set: the engine CANNOT
        // translate simd, so the closed-instruction-universe guarantee for
        // that axis = the Cargo.toml (check the lockfile, not the config).
        cfg.wasm_memory64(false);
        cfg.wasm_multi_memory(false);
        cfg.wasm_wide_arithmetic(false);
        cfg.wasm_custom_page_sizes(false);
        let engine = wasmi::Engine::new(&cfg);
        let module = wasmi::Module::new(&engine, wasm)?;
        let mut store = wasmi::Store::new(&engine, ());
        store.set_fuel(fuel)?;
        let mut linker = <wasmi::Linker<()>>::new(&engine);
        // The standalone rt provides NO host functionality: every import the
        // module declares (the WASI 0.3 task intrinsics the async-lowered
        // fns call — waitable-set/task-return/stream-*) is linked as a LOUD
        // trap. Sync exports never call them, so the SYNC spec subset runs
        // anywhere; an async fn traps at its first intrinsic call — the
        // honest boundary (async requires a wasi 0.3 host: wasmtime /
        // steel-host). Generic over the module's OWN import table, so new
        // intrinsics need no rt change; a non-func import is a hard error.
        for import in module.imports() {
            let Some(ft) = import.ty().func() else {
                return Err(RtError(format!(
                    "guestlang-rt: non-func import `{}::{}` — not supported standalone",
                    import.module(),
                    import.name()
                )));
            };
            linker
                .func_new(import.module(), import.name(), ft.clone(), |_, _, _| {
                    Err(wasmi::Error::new(
                        "guestlang-rt: async task-intrinsic called — async \
                         requires a wasi 0.3 host (wasmtime / steel-host)",
                    ))
                })
                .map_err(|e| RtError(format!("wasmi: {e}")))?;
        }
        let instance = linker.instantiate_and_start(&mut store, &module)?;
        Ok(Self { store, instance })
    }

    /// Invoke one export on the RETAINED instance, fuel-metered for this
    /// call (the same coercion + fuel semantics as `invoke_core_fueled`,
    /// but the heap PERSISTS across calls).
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

    /// The instance's linear memory export — the SAME one the compiler
    /// line's modules always export (the guest's own heap lives here:
    /// the pooled free-lists, the RC'd objects, everything but the
    /// bump/RC globals).
    fn memory(&self) -> Result<wasmi::Memory, RtError> {
        self.instance
            .get_memory(&self.store, "memory")
            .ok_or_else(|| {
                RtError(
                    "guestlang-rt: no `memory` export — snapshot/restore requires it \
                 (the compiler line's modules export it)"
                        .into(),
                )
            })
    }

    /// Capture the honest v1 snapshot: the full memory image + the fuel
    /// remaining. See `Snapshot` for the globals gap.
    pub fn snapshot(&self) -> Result<Snapshot, RtError> {
        let memory = self.memory()?.data(&self.store).to_vec();
        Ok(Snapshot {
            memory,
            fuel: self.store.get_fuel()?,
        })
    }
}

impl Snapshot {
    /// The captured memory image (the guest heap's bytes at capture).
    pub fn memory(&self) -> &[u8] {
        &self.memory
    }

    /// Fuel remaining at capture.
    pub fn fuel(&self) -> u64 {
        self.fuel
    }

    /// Rebuild a `Runtime` from this snapshot: a FRESH instance of
    /// `wasm` (same deterministic profile) with the memory image
    /// restored and the fuel state set. See `Snapshot`'s doc for what
    /// this does and does not preserve.
    pub fn restore(&self, wasm: &[u8]) -> Result<Runtime, RtError> {
        let mut rt = Runtime::new(wasm, self.fuel)?;
        let mem = rt.memory()?;
        let cur = mem.data(&rt.store).len();
        if self.memory.len() > cur {
            // The captured run grew memory beyond the fresh instance's
            // initial size — grow to fit the image before writing it.
            let pages = (self.memory.len() - cur).div_ceil(0x1_0000) as u64;
            mem.grow(&mut rt.store, pages)
                .map_err(|e| RtError(format!("snapshot restore: memory grow: {e}")))?;
        }
        mem.write(&mut rt.store, 0, &self.memory)
            .map_err(|e| RtError(format!("snapshot restore: memory write: {e}")))?;
        Ok(rt)
    }
}

/// The Val-level API: mixed-type args (e.g. the canonical-ABI adapters'
/// flat bool params are I32, u64 params are I64).
pub fn invoke_core_vals(
    wasm: &[u8],
    func: &str,
    args: &[Val],
    fuel: u64,
) -> Result<Vec<i64>, RtError> {
    // Route through the fueled path: Vals are untyped at this seam, so
    // consume-nothing coercion is impossible — reuse the machinery by
    // wrapping the Vals via a tiny inline clone of the call path is NOT
    // worth it; the fueled path + coercion covers every scalar caller.
    // This Val-level variant stays for mixed-type callers (the pick bool).
    let coerced: Vec<i64> = args
        .iter()
        .map(|v| match v {
            Val::I64(x) => *x,
            Val::I32(x) => *x as i64,
            _ => 0,
        })
        .collect();
    invoke_core(wasm, func, &coerced, fuel)
}

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

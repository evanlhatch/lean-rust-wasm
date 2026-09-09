//! guestlang-rt — the standalone embeddable WASM interpreter.
//!
//! wasmi 2.0: pure-Rust, deterministic, fuel-metered. CORE wasm only —
//! the component wrapper (canonical ABI + WIT) is the wasmtime host's
//! job; this runtime runs the COMPILER LINE's output directly.
//!
//! Resource story: fuel (deterministic instruction counting) + the
//! pooled allocator in the guest itself. Snapshot/restore (rkyv over our
//! own object model) and the worker pool (Monty pattern) land next.

use wasmi::Val;

/// Compile + invoke one export on the wasmi engine, fuel-metered.
/// Any arity: args/results flow as i64 (the guestlang scalar ABI).
pub fn invoke_core(wasm: &[u8], func: &str, args: &[i64], fuel: u64) -> Result<Vec<i64>, RtError> {
    let vals: Vec<Val> = args.iter().map(|a| Val::I64(*a)).collect();
    invoke_core_vals(wasm, func, &vals, fuel)
}

/// The Val-level API: mixed-type args (e.g. the canonical-ABI adapters'
/// flat bool params are I32, u64 params are I64).
pub fn invoke_core_vals(
    wasm: &[u8],
    func: &str,
    args: &[Val],
    fuel: u64,
) -> Result<Vec<i64>, RtError> {
    let mut cfg = wasmi::Config::default();
    cfg.consume_fuel(true);
    let engine = wasmi::Engine::new(&cfg);
    let module = wasmi::Module::new(&engine, wasm)?;
    let mut store = wasmi::Store::new(&engine, ());
    store.set_fuel(fuel)?;
    let mut linker = <wasmi::Linker<()>>::new(&engine);
    let instance = linker.instantiate_and_start(&mut store, &module)?;
    let f = instance
        .get_export(&store, func)
        .and_then(wasmi::Extern::into_func)
        .ok_or_else(|| RtError(format!("no export: {func}")))?;
    let mut results = vec![Val::I64(0); f.ty(&store).results().len()];
    f.call(&mut store, args, &mut results)?;
    Ok(results
        .iter()
        .map(|v| match v {
            Val::I64(x) => *x,
            Val::I32(x) => *x as i64,
            _ => 0,
        })
        .collect())
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

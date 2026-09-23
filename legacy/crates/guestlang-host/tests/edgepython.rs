//! EdgePython conformance — the wasmtime half of the THREE-ENGINE duel.
//!
//! The SECOND FRONTEND (notes/full-remaining-work.md "EdgePython
//! frontend"): a Python subset compiled by the lean/edgepython package
//! to the SAME typed WAT AST the LCNF backend emits (zero new
//! constructors), binary-ized by the same wasm-tools pipeline. This
//! test runs the compiled module under wasmtime (guestlang-host's engine);
//! crates/guestlang-rt/tests/edgepython.rs runs the SAME module under
//! wasmi; the Lean tests pin the SAME values against the Python
//! reference semantics. Same fixtures → same results across engines —
//! the IR seam is frontend-neutral.

use wasmtime::{Engine, Instance, Module, Store};

mod common;

fn py_wasm() -> Vec<u8> {
    std::fs::read(std::fs::canonicalize(common::py_wasm_path()).expect("run `just edgepython`")).unwrap()
}

/// Instantiate the core module (no imports: the scalars-only subset
/// needs no runtime — no alloc, no RC, no task intrinsics).
fn instantiate(wasm: &[u8]) -> (Store<()>, Instance) {
    let engine = Engine::default();
    let module = Module::from_binary(&engine, wasm).expect("py.wasm: valid binary");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate");
    (store, instance)
}

fn call1(store: &mut Store<()>, f: &Instance, name: &str, arg: i64) -> i64 {
    f.get_typed_func::<i64, i64>(&mut *store, name)
        .unwrap_or_else(|_| panic!("export {name} missing"))
        .call(store, arg)
        .unwrap_or_else(|_| panic!("{name} trapped"))
}

fn call2(store: &mut Store<()>, f: &Instance, name: &str, a: i64, b: i64) -> i64 {
    f.get_typed_func::<(i64, i64), i64>(&mut *store, name)
        .unwrap_or_else(|_| panic!("export {name} missing"))
        .call(store, (a, b))
        .unwrap_or_else(|_| panic!("{name} trapped"))
}

#[test]
fn edgepython_runs_under_wasmtime() {
    let wasm = py_wasm();
    let (mut store, instance) = instantiate(&wasm);

    // the duel constants — the Lean tests (EdgePython.Parity) and the
    // wasmi test pin the SAME numbers
    assert_eq!(call1(&mut store, &instance, "double", 21), 42);
    assert_eq!(call2(&mut store, &instance, "adder", 40, 2), 42);
    assert_eq!(call1(&mut store, &instance, "dec1", 5), 4);
    assert_eq!(call1(&mut store, &instance, "loop_sum", 10), 45);
    assert_eq!(call1(&mut store, &instance, "loop_sum", 0), 0);
    assert_eq!(call2(&mut store, &instance, "if_max", 3, 9), 9);
    assert_eq!(call2(&mut store, &instance, "if_max", 9, 3), 9);
}

#[test]
fn edgepython_module_shape_is_the_runtime_shape() {
    // the guestlang module shape, minus the runtime splice: the
    // scalars-only subset allocates nothing, so NO imports — the same
    // core module runs standalone (the parity with the guestlang
    // line's import-free core-ABI surface)
    let wasm = py_wasm();
    let (mut store, instance) = instantiate(&wasm);
    // every fixture exported by name (the multi-frontend conformance
    // surface: the runtime invokes by export name, frontend-blind)
    for name in ["double", "adder", "dec1", "loop_sum", "if_max"] {
        assert!(
            instance.get_func(&mut store, name).is_some(),
            "export {name} missing"
        );
    }
}

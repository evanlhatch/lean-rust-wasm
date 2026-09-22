//! EdgePython conformance — the wasmi half of the THREE-ENGINE duel.
//!
//! The SAME compiled py.wasm (lean/edgepython → WasmBackend.Wat →
//! wasm-tools) runs under the standalone rt (wasmi, core wasm,
//! fuel-metered) with the SAME results the wasmtime test (guestlang-host's
//! edgepython.rs) and the Lean parity theorems pin. The IR seam is
//! frontend-neutral AND engine-agnostic: the runtime never learns what
//! language produced the module.

use guestlang_rt::invoke_core;
use guestlang_rt::invoke_core_fueled;

fn py_wasm() -> Vec<u8> {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/edgepython/target/py.wasm");
    std::fs::read(std::fs::canonicalize(&p).expect("run `just edgepython`")).unwrap()
}

#[test]
fn edgepython_runs_under_wasmi() {
    let wasm = py_wasm();
    // the duel constants — Lean (EdgePython.Parity) + wasmtime pin the
    // SAME numbers
    assert_eq!(
        invoke_core(&wasm, "double", &[21], 1_000_000).unwrap(),
        vec![42]
    );
    assert_eq!(
        invoke_core(&wasm, "adder", &[40, 2], 1_000_000).unwrap(),
        vec![42]
    );
    assert_eq!(
        invoke_core(&wasm, "dec1", &[5], 1_000_000).unwrap(),
        vec![4]
    );
    assert_eq!(
        invoke_core(&wasm, "loop_sum", &[10], 1_000_000).unwrap(),
        vec![45]
    );
    assert_eq!(
        invoke_core(&wasm, "loop_sum", &[0], 1_000_000).unwrap(),
        vec![0]
    );
    assert_eq!(
        invoke_core(&wasm, "if_max", &[3, 9], 1_000_000).unwrap(),
        vec![9]
    );
    assert_eq!(
        invoke_core(&wasm, "if_max", &[9, 3], 1_000_000).unwrap(),
        vec![9]
    );
}

#[test]
fn fuel_bounds_the_python_guest_deterministically() {
    let wasm = py_wasm();
    // plenty of fuel: the loop-guest completes
    let r = invoke_core(&wasm, "loop_sum", &[10], 1_000_000).unwrap();
    assert_eq!(r, vec![45]);
    // 1 fuel cannot even START a call — the deterministic bound (the
    // same discipline the guestlang conformance test pins)
    let err = invoke_core(&wasm, "double", &[21], 1).unwrap_err();
    assert!(err.0.contains("wasmi"), "{err}");
    // the fuel CONSUMED is stable across runs (the conformance gate's
    // metering pin, mirrored)
    let (_, f1) = invoke_core_fueled(&wasm, "loop_sum", &[10], 1_000_000).unwrap();
    let (_, f2) = invoke_core_fueled(&wasm, "loop_sum", &[10], 1_000_000).unwrap();
    assert_eq!(f1, f2, "fuel must be deterministic");
    assert!(f1 > 0, "fuel must have been consumed");
}

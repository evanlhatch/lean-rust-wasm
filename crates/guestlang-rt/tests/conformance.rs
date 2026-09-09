//! ENGINE-PORTABILITY CONFORMANCE: the SAME compiled wasm runs under
//! wasmi (this crate — the standalone rt) AND wasmtime (steel-host's
//! engine) with IDENTICAL results. The compiler line's output is engine-
//! agnostic: the IR seam holds.

use guestlang_rt::invoke_core;

fn demo_wasm() -> Vec<u8> {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..//lean/wasm-backend/target/demo.wasm");
    std::fs::read(std::fs::canonicalize(&p).expect("run `just wasm-compile`")).unwrap()
}

#[test]
fn wasmi_runs_the_compiler_line_output() {
    let wasm = demo_wasm();
    // double 21 = 42
    assert_eq!(
        invoke_core(&wasm, "double", &[21], 1_000_000).unwrap(),
        vec![42]
    );
    // adder 40 2 = 42
    assert_eq!(
        invoke_core(&wasm, "adder", &[40, 2], 1_000_000).unwrap(),
        vec![42]
    );
    // run-paps 5 = 8 — closures + pooled allocator under wasmi
    assert_eq!(
        invoke_core(&wasm, "run-paps", &[5], 1_000_000).unwrap(),
        vec![8]
    );
    // double-area 5 = 100 — the full object lifecycle under wasmi
    assert_eq!(
        invoke_core(&wasm, "double-area", &[5], 1_000_000).unwrap(),
        vec![100]
    );
    // pick 1 3 4 = 7 — scalar cases + canonical ABI (the bool arg is the
    // flat I32; the adapter boxes it)
    let r = guestlang_rt::invoke_core_vals(
        &demo_wasm(),
        "pick",
        &[wasmi::Val::I32(1), wasmi::Val::I64(3), wasmi::Val::I64(4)],
        1_000_000,
    )
    .unwrap();
    assert_eq!(r, vec![7]);
}

#[test]
fn fuel_bounds_runaway_guests_deterministically() {
    let wasm = demo_wasm();
    // sum-list over a long list via total: 1M fuel is plenty for small n…
    let r = invoke_core(&wasm, "double", &[21], 1_000_000).unwrap();
    assert_eq!(r, vec![42]);
    // …but 1 fuel cannot even START a call — the deterministic bound.
    let err = invoke_core(&wasm, "double", &[21], 1).unwrap_err();
    assert!(err.0.contains("wasmi"), "{err}");
}

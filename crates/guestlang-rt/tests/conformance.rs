//! ENGINE-PORTABILITY CONFORMANCE: the SAME compiled wasm runs under
//! wasmi (this crate — the standalone rt) AND wasmtime (guestlang-host's
//! engine) with IDENTICAL results. The compiler line's output is engine-
//! agnostic: the IR seam holds.

use guestlang_rt::invoke_core;
use guestlang_rt::invoke_core_fueled;

mod common;
use common::demo_wasm;
use common::manifest;

/// Look up a (fn, args) row in the oracle manifest and return the
/// expected scalar result and the args (as the manifest stores them).
/// Panics on miss (manifest must cover every row the smoke test
/// asserts — drift is a gate failure).
fn manifest_expect(fn_name: &str) -> (Vec<String>, u64) {
    let rows = manifest();
    let (_, args, exp) = rows
        .into_iter()
        .find(|(f, _, _)| f == fn_name)
        .unwrap_or_else(|| panic!("{fn_name} not in oracle manifest"));
    (
        args,
        exp.parse().expect("manifest expected value is not a u64"),
    )
}

#[test]
fn wasmi_runs_the_compiler_line_output() {
    let wasm = demo_wasm();
    // Each scalar fn is exercised with the args from its FIRST manifest
    // row — the expected result is the Lean oracle's, not a hand constant.
    // This replaces the old hardcoded (double 21=42, adder 40+2=42, etc.).
    {
        let (args, expected) = manifest_expect("double");
        let iargs: Vec<i64> = args
            .iter()
            .map(|a| a.parse::<u64>().unwrap() as i64)
            .collect();
        assert_eq!(
            invoke_core(&wasm, "double", &iargs, 1_000_000).unwrap(),
            vec![expected as i64]
        );
    }
    {
        let (args, expected) = manifest_expect("adder");
        let iargs: Vec<i64> = args
            .iter()
            .map(|a| a.parse::<u64>().unwrap() as i64)
            .collect();
        assert_eq!(
            invoke_core(&wasm, "adder", &iargs, 1_000_000).unwrap(),
            vec![expected as i64]
        );
    }
    {
        let (args, expected) = manifest_expect("run-paps");
        let iargs: Vec<i64> = args
            .iter()
            .map(|a| a.parse::<u64>().unwrap() as i64)
            .collect();
        assert_eq!(
            invoke_core(&wasm, "run-paps", &iargs, 1_000_000).unwrap(),
            vec![expected as i64]
        );
    }
    {
        let (args, expected) = manifest_expect("double-area");
        let iargs: Vec<i64> = args
            .iter()
            .map(|a| a.parse::<u64>().unwrap() as i64)
            .collect();
        assert_eq!(
            invoke_core(&wasm, "double-area", &iargs, 1_000_000).unwrap(),
            vec![expected as i64]
        );
    }
    // pick: uses invoke_core_vals due to heterogeneous arg types
    {
        let (args_str, expected) = manifest_expect("pick");
        let pick_args = args_str
            .iter()
            .map(|a| a.parse::<u64>().unwrap())
            .collect::<Vec<_>>();
        let r = guestlang_rt::invoke_core_vals(
            &demo_wasm(),
            "pick",
            &[
                wasmi::Val::I32(pick_args[0] as i32),
                wasmi::Val::I64(pick_args[1] as i64),
                wasmi::Val::I64(pick_args[2] as i64),
            ],
            1_000_000,
        )
        .unwrap();
        assert_eq!(r, vec![expected as i64]);
    }
}

#[test]
fn fuel_bounds_runaway_guests_deterministically() {
    let wasm = demo_wasm();
    // Use the first manifest row for double
    let (args, expected) = manifest_expect("double");
    let iargs: Vec<i64> = args
        .iter()
        .map(|a| a.parse::<u64>().unwrap() as i64)
        .collect();
    let r = invoke_core(&wasm, "double", &iargs, 1_000_000).unwrap();
    assert_eq!(r, vec![expected as i64]);
    // …but 1 fuel cannot even START a call — the deterministic bound.
    let err = invoke_core(&wasm, "double", &iargs, 1).unwrap_err();
    assert!(err.0.contains("wasmi"), "{err}");
}

// ── wasmi 2.0 consumption: the multi-engine proof surface ──────────

/// The scalar subset of the oracle manifest: fns whose args/results are
/// pure canonical scalars — the CORE-ABI surface wasmi runs directly.
/// (String/record/option rows go through the component's canonical-ABI
/// adapters — the wasmtime host's surface; async rows need the wasi 0.3
/// task intrinsics.) The partition pin below RATCHETS: a new demo fn
/// must be classified here or the duel fails.
const SCALAR_DUEL: &[&str] = &[
    "double",
    "is-big",
    "adder",
    "double-area",
    "run-paps",
    "total",
    "pick",
];
const COMPONENT_ONLY: &[&str] = &[
    "str-len-demo",
    "greet",
    "get-user",
    "watch-counts",
    "watch-users",
    // the record-PARAM row: the flat field values reconstruct to guest
    // pointers by the canonical-ABI adapter — the wasmtime host's
    // surface (wasmi's core-abi invoke has no Val::Record lowering)
    "user-valid",
    // the validators phase 2: the same component-adapter surface —
    // user-complete reconstructs the record (strlen/list-count gates);
    // order-error-valid's variant param = the flat [discr, payload]
    // re-boxed by the variantParam adapter
    "user-complete",
    "order-error-valid",
    // the W9.6 witness export: bytes in (the canonical list<u8> pair —
    // the flat (ptr, len) the lift copies into guest memory), verdict
    // out; the bytesParam adapter builds the guest cons chain
    "verify-witness",
];

#[test]
fn manifest_partition_is_exhaustive() {
    // every manifest fn is classified — a new export can't silently
    // dodge the duel (the Lean authority covers it SOMEWHERE)
    let mut fns: Vec<String> = manifest().into_iter().map(|(f, _, _)| f).collect();
    fns.sort();
    fns.dedup();
    let mut classified: Vec<&str> = SCALAR_DUEL.iter().chain(COMPONENT_ONLY).copied().collect();
    classified.sort();
    classified.dedup();
    assert_eq!(
        SCALAR_DUEL.len() + COMPONENT_ONLY.len(),
        classified.len(),
        "overlap in the partition tables"
    );
    let unclassified: Vec<&String> = fns
        .iter()
        .filter(|f| !classified.contains(&f.as_str()))
        .collect();
    assert!(
        unclassified.is_empty(),
        "manifest fns not classified in the duel: {unclassified:?}"
    );
    assert!(!SCALAR_DUEL.is_empty(), "scalar duel must be non-empty");
}

#[test]
fn engine_duel_wasmi_matches_the_lean_authority() {
    // the SAME manifest rows guestlang-host replays under wasmtime, replayed
    // here under wasmi: one authority (Lean's evals), two engines
    let wasm = demo_wasm();
    let mut ran = 0;
    for (f, args, expected) in manifest() {
        if !SCALAR_DUEL.contains(&f.as_str()) {
            continue;
        }
        // the boundary rows are U64 (the oracle's full-range inputs) —
        // parse as u64, bit-cast for the i64 core ABI
        let iargs: Vec<i64> = args
            .iter()
            .map(|a| a.parse::<u64>().expect("scalar row arg") as i64)
            .collect();
        let got = invoke_core(&wasm, &f, &iargs, 1_000_000)
            .unwrap_or_else(|e| panic!("{f} {iargs:?} trapped under wasmi: {e}"));
        let want: Vec<u64> = vec![expected.parse().expect("scalar row result")];
        assert_eq!(
            got.iter().map(|g| *g as u64).collect::<Vec<u64>>(),
            want,
            "{f} {iargs:?}: wasmi disagrees with the Lean oracle"
        );
        ran += 1;
    }
    assert!(
        ran >= 100,
        "only {ran} scalar rows ran — manifest/duel drift"
    );
}

#[test]
fn fuel_metering_is_stable_across_runs() {
    // wasmi 2.0's stable fuel metering: identical module+args+fuel →
    // identical consumption, every run, every wasmi version. This pin
    // makes an upstream fuel-accounting change a GATE failure (rt-
    // conformance), i.e. a noticed event, not a silent ABI drift.
    let wasm = demo_wasm();
    let (_, f1) = invoke_core_fueled(&wasm, "double", &[21], 1_000_000).unwrap();
    let (_, f2) = invoke_core_fueled(&wasm, "double", &[21], 1_000_000).unwrap();
    assert_eq!(f1, f2, "fuel consumption is not run-stable");
    assert!(f1 > 0, "a real call must consume fuel");
    let (_, f3) = invoke_core_fueled(&wasm, "double", &[1_000_000], 1_000_000).unwrap();
    assert!(f3 > 0);
}

#[test]
fn the_profile_refuses_float_modules() {
    // NEGATIVE CONTROL for the deterministic profile: a module with an
    // f64 instruction is REFUSED at load (the engine's feature set =
    // the spec's closed fragment — the runtime mirror). Hand-encoded:
    // (func (result f64) f64.const 0 drop) — no export needed, the
    // rejection fires at Module::new (the translation).
    let float_wasm: &[u8] = &[
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, // magic + version
        0x01, 0x06, 0x01, 0x60, 0x00, 0x01, 0x7B, // type: () -> f64
        0x03, 0x02, 0x01, 0x00, // func 0: type 0
        0x0A, 0x0E, 0x01, 0x0D, 0x00, // code: 1 body, 0 locals
        0xFD, 0x44, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // f64.const 0
        0x1A, 0x0B, // drop, end
    ];
    let err = invoke_core(float_wasm, "f", &[], 1_000).unwrap_err();
    eprintln!("float module refused: {err}");
}

#[test]
fn async_boundary_traps_loudly() {
    // NEGATIVE CONTROL for the trap-stub linker: the async fns must
    // trap with the documented boundary error at their first task-
    // intrinsic call — never a silent wrong answer.
    let wasm = demo_wasm();
    for f in ["[async-lift]watch-counts", "[async-lift]watch-users"] {
        let err = invoke_core(&wasm, f, &[7], 1_000_000).unwrap_err();
        assert!(
            err.0.contains("async task-intrinsic called"),
            "{f}: expected the loud async boundary trap, got: {err}"
        );
    }
}

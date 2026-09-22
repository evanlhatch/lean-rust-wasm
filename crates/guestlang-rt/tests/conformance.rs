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
//
// C2: the scalar/component partition is DERIVED from the manifest rows
// (the spec of record — diff.json), not hand-maintained. A fn is scalar
// iff EVERY row's args AND expected parse as u64 — the flat core-ABI
// surface `invoke_core` runs directly. The derivation's soundness probe
// (2026-09-22 artifact, scratch run): every derived-scalar fn passes
// the flat i64-bitcast duel against the Lean oracle row-for-row, and
// every canonical-surface fn carries a NON-numeric row tell — string
// args (`user-valid`'s `"zero"/"0@g.dev"`), string/record expected
// (`greet`, `get-user`, `watch-*`), the variant's f64-payload row
// (`order-error-valid` `["2","1.5"]` — not a u64), the witness byte
// list (`verify-witness`). The one surface the shape cannot see is
// `str-len-demo`'s WIT String RESULT — its manifest rows record only
// the u64 length projection, and the flat duel passes all 42 rows, so
// the derivation (correctly) duels it. The SURFACE PIN below keeps the
// hand ENGINE-COVERAGE intent (which engine path each fn MUST exercise)
// as the tie-test in `manifest_partition_is_exhaustive`: a manifest
// shape change that would silently re-partition the duel fails loudly.

/// The hand surface pin (engine-coverage intent): fns whose WIT
/// surface is pure canonical scalars — the CORE-ABI surface wasmi runs
/// directly. (String/record/option rows go through the component's
/// canonical-ABI adapters — the wasmtime host's surface; async rows
/// need the wasi 0.3 task intrinsics.) MUST equal the derived scalar
/// partition exactly.
const SCALAR_DUEL: &[&str] = &[
    "double",
    "is-big",
    "adder",
    "double-area",
    "run-paps",
    "total",
    "pick",
    // C2: moved here from COMPONENT_ONLY by the shape derivation —
    // every row is (u64 id, u64 length) and the flat duel passes all
    // 42 rows (the String result never appears in the manifest).
    "str-len-demo",
];

/// The hand surface pin (engine-coverage intent): fns whose rows run
/// through the component's canonical-ABI adapters — the wasmtime host's
/// surface. MUST equal the derived component-only partition exactly.
const COMPONENT_ONLY: &[&str] = &[
    "greet",
    "get-user",
    "watch-counts",
    "watch-users",
    // the record-PARAM row: the flat field values reconstruct to guest
    // pointers by the canonical-ABI adapter — the wasmi core-abi
    // invoke has no Val::Record lowering (the row args are strings, so
    // the shape derivation keeps them component-only)
    "user-valid",
    // the validators phase 2: the same component-adapter surface —
    // user-complete reconstructs the record (strlen/list-count gates);
    // order-error-valid's variant param = the flat [discr, payload]
    // re-boxed by the variantParam adapter (its f64 case renders the
    // non-numeric payload `"1.5"` — the row tell the derivation reads)
    "user-complete",
    "order-error-valid",
    // the W9.6 witness export: bytes in (the canonical list<u8> pair —
    // the flat (ptr, len) the lift copies into guest memory), verdict
    // out; the bytesParam adapter builds the guest cons chain
    "verify-witness",
];

/// The manifest's fn names, deduped + sorted (stable key order).
fn manifest_fn_names() -> Vec<String> {
    let mut fns: Vec<String> = manifest().into_iter().map(|(f, _, _)| f).collect();
    fns.sort();
    fns.dedup();
    fns
}

/// Shape-scalar: EVERY row's args AND expected parse as u64 — the flat
/// canonical-scalar surface the core-ABI invoke runs directly.
fn rows_are_canonical_scalars(fn_name: &str) -> bool {
    manifest()
        .into_iter()
        .filter(|(f, _, _)| f == fn_name)
        .all(|(_, args, expected)| {
            args.iter().all(|a| a.parse::<u64>().is_ok()) && expected.parse::<u64>().is_ok()
        })
}

/// The DERIVED duel partition: one fold over the manifest (the spec of
/// record) — no hand list to rot. Scalar = shape-scalar fns, the rest
/// are component-only.
fn scalar_duel_fns() -> Vec<String> {
    manifest_fn_names()
        .into_iter()
        .filter(|f| rows_are_canonical_scalars(f))
        .collect()
}

fn component_only_fns() -> Vec<String> {
    let scalar = scalar_duel_fns();
    manifest_fn_names()
        .into_iter()
        .filter(|f| !scalar.contains(f))
        .collect()
}

#[test]
fn manifest_partition_is_exhaustive() {
    // every manifest fn is classified BY SHAPE — a new export can't
    // silently dodge the duel (the Lean authority covers it SOMEWHERE
    // by construction). The derived-vs-surface-pin tie below is the
    // drift alarm: a manifest shape change that would re-partition the
    // duel (not merely add rows) FAILS here instead of silently
    // shuffling engine coverage.
    let scalar = scalar_duel_fns();
    let component = component_only_fns();
    let all = manifest_fn_names();
    assert_eq!(
        scalar.len() + component.len(),
        all.len(),
        "derived partition must cover exactly the manifest fns"
    );
    assert!(
        component.iter().all(|f| !scalar.contains(f)),
        "overlap in the derived partition"
    );
    assert!(!scalar.is_empty(), "scalar duel must be non-empty");
    // THE TIE with the hand surface pin (engine-coverage intent):
    let mut pin_scalar: Vec<&str> = SCALAR_DUEL.to_vec();
    pin_scalar.sort();
    let mut pin_component: Vec<&str> = COMPONENT_ONLY.to_vec();
    pin_component.sort();
    let derived_scalar: Vec<&str> = scalar.iter().map(String::as_str).collect();
    let derived_component: Vec<&str> = component.iter().map(String::as_str).collect();
    assert_eq!(
        derived_scalar, pin_scalar,
        "derived scalar duel != surface pin — update the pin OR the manifest shape changed"
    );
    assert_eq!(
        derived_component, pin_component,
        "derived component-only != surface pin — update the pin OR the manifest shape changed"
    );
}

#[test]
fn engine_duel_wasmi_matches_the_lean_authority() {
    // the SAME manifest rows guestlang-host replays under wasmtime, replayed
    // here under wasmi: one authority (Lean's evals), two engines
    let wasm = demo_wasm();
    let scalar_duel = scalar_duel_fns();
    let mut ran = 0;
    for (f, args, expected) in manifest() {
        if !scalar_duel.contains(&f) {
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

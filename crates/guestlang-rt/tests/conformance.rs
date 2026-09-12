//! ENGINE-PORTABILITY CONFORMANCE: the SAME compiled wasm runs under
//! wasmi (this crate — the standalone rt) AND wasmtime (steel-host's
//! engine) with IDENTICAL results. The compiler line's output is engine-
//! agnostic: the IR seam holds.

use guestlang_rt::{invoke_core, invoke_core_fueled};

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
];

fn manifest() -> Vec<(String, Vec<String>, String)> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/wasm-backend/target/diff.json");
    let rows: Vec<serde_json::Value> =
        serde_json::from_str(&std::fs::read_to_string(&path).expect("run `just wasm-compile`"))
            .expect("diff.json");
    assert!(
        rows.len() >= 100,
        "oracle generated only {} rows — vacuous",
        rows.len()
    );
    rows.into_iter()
        .map(|r| {
            (
                r["fn"].as_str().unwrap().to_string(),
                r["args"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|a| a.as_str().unwrap().to_string())
                    .collect(),
                r["expected"].as_str().unwrap().to_string(),
            )
        })
        .collect()
}

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
    // the SAME manifest rows steel-host replays under wasmtime, replayed
    // here under wasmi: one authority (Lean's evals), two engines
    let wasm = demo_wasm();
    let mut ran = 0;
    for (f, args, expected) in manifest() {
        if !SCALAR_DUEL.contains(&f.as_str()) {
            continue;
        }
        let iargs: Vec<i64> = args
            .iter()
            .map(|a| a.parse().expect("scalar row arg"))
            .collect();
        let got = invoke_core(&wasm, &f, &iargs, 1_000_000)
            .unwrap_or_else(|e| panic!("{f} {iargs:?} trapped under wasmi: {e}"));
        let want: Vec<i64> = vec![expected.parse().expect("scalar row result")];
        assert_eq!(
            got, want,
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

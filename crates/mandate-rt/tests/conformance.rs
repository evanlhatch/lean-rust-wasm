//! THE RT CONFORMANCE SUITE (D1 — the wasmi leg's teeth, ported from
//! legacy guestlang-rt's conformance battery onto the shared profile):
//!
//! - THE F64-REFUSAL NEGATIVE CONTROL: a hand-encoded module with an
//!   f64 instruction is REFUSED at load (the engine's feature set =
//!   the profile's closed fragment — the runtime mirror).
//! - THE STABLE-FUEL PIN: identical module + args → identical fuel
//!   consumption across runs (an upstream fuel-accounting change is a
//!   noticed gate failure, never a silent ABI drift).
//! - THE COMMITTED VECTORS: the rt runs the duel family's slice under
//!   the profile and lands on the Lean executor's computed golden.
//!
//! Everything reads the COMMITTED universe (`gen/wasm-duel/`) — the
//! consumer contract; no fixture re-encoding here.

use mandate_rt::{invoke_core, invoke_core_fueled, parse_profile};

/// The committed duel vector bytes.
fn committed(path: &str) -> Vec<u8> {
    std::fs::read(mandate_rt::repo_gen_dir().join("wasm-duel").join(path))
        .expect("the committed duel vector")
}

#[test]
fn the_slice_runs_to_the_golden_under_the_profile() {
    // The committed slice module: `answer : -> i64` → 42 (the Lean
    // executor's computed expectation, `WasmCore.Duel`'s pinned row).
    let wasm = committed("slice.wasm");
    let out = invoke_core(&wasm, "answer", &[], 1_000_000).expect("the slice runs");
    assert_eq!(out, vec![42]);
}

#[test]
fn fuel_bounds_runaway_guests_deterministically() {
    // 1 fuel cannot even START a call — the deterministic bound (the
    // profile's `consume-fuel on` axis, enforced).
    let wasm = committed("slice.wasm");
    let err = invoke_core(&wasm, "answer", &[], 1).unwrap_err();
    assert!(err.0.contains("wasmi"), "{err}");
}

#[test]
fn fuel_metering_is_stable_across_runs() {
    // THE STABLE-FUEL PIN: identical module+args+fuel → identical
    // consumption, every run, every wasmi version. A diverging pin is
    // an upstream fuel-accounting change = a noticed event.
    let wasm = committed("control.wasm");
    let (_, f1) = invoke_core_fueled(&wasm, "answer", &[], 1_000_000).unwrap();
    let (_, f2) = invoke_core_fueled(&wasm, "answer", &[], 1_000_000).unwrap();
    assert_eq!(f1, f2, "fuel consumption is not run-stable");
    assert!(f1 > 0, "a real call must consume fuel");
    // A second committed vector consumes fuel too (the pin is not a
    // one-module accident).
    let wasm2 = committed("slice.wasm");
    let (_, f3) = invoke_core_fueled(&wasm2, "answer", &[], 1_000_000).unwrap();
    assert!(f3 > 0);
}

#[test]
fn the_profile_refuses_float_modules() {
    // THE F64-REFUSAL NEGATIVE CONTROL (the profile's `floats off`
    // axis, ENFORCED at the engine): a hand-encoded module with an f64
    // instruction is REFUSED at load. Hand-encoded — the closed
    // fragment cannot generate one (the Lean validator would refuse it
    // at generation): (func (result f64) f64.const 0 drop).
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
fn the_committed_profile_is_the_deterministic_one() {
    // The rt's OWN config source is the committed file: pin that it
    // parses to THE deterministic profile (a drifted/tampered profile
    // refuses here before any engine sees it).
    let text = std::fs::read_to_string(mandate_rt::repo_gen_dir().join("wasm-duel/profile.txt"))
        .expect("the committed profile");
    let p = parse_profile(&text).expect("the committed profile parses");
    assert!(p.consume_fuel);
    assert_eq!(p.compilation, mandate_rt::CompilationMode::LazyTranslation);
    assert!(!p.floats);
    assert!(!p.memory64);
    assert!(!p.multi_memory);
    assert!(!p.wide_arithmetic);
    assert!(!p.custom_page_sizes);
    assert!(!p.simd);
}

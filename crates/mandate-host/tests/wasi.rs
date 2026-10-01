//! THE WASI P3 LANE'S TEETH (D3): the capability valves as effect rows.
//!
//! - the MIRROR PINS: the Rust interface table carries the same rows as
//!   the Lean SSOT (`Effects.wasiRow`) for the same ids (the dual
//!   fixture; the rendered-table lane is the named follow-up);
//! - the WASI FACE's smoke: a component importing
//!   `wasi:cli/environment@0.3.0` (a sync p3 interface) RUNS against a
//!   served p3 linker (the sync-first lane);
//! - THE VALVE'S TOOTH: the SAME component against the DEFAULT-DENY
//!   (empty) allowance refuses at LOAD with the import + its missing
//!   atoms named — never a wasm trap, never instantiation;
//! - the undeclared tooth: an import outside the closed table refuses
//!   as `CapabilityUndeclared`;
//! - the committed component (zero imports) derives the EMPTY row and
//!   loads against the closed box (default-deny is a no-op for it).

use mandate_host::{
    EffectAtom, HostError, component_imports, derive_row, instantiate_wasi_component, row_le,
    wasi_row,
};
use wasmtime::component::Component;
use wasmtime::{Config, Engine};

use mandate_host::load_component;
use mandate_host::repo_gen_dir;

/// The WASI-import fixture: a component whose world imports
/// `wasi:cli/environment@0.3.0` (the p3 linker serves it; the sync
/// interface's three funcs are not `async func` — the sync-first
/// lane's face).
const WASI_ENV_COMPONENT: &str = r#"
(component
  (import "wasi:cli/environment@0.3.0" (instance $env
    (export "get-environment" (func (result (list (tuple string string)))))
    (export "get-arguments" (func (result (list string))))
    (export "get-initial-cwd" (func (result (option string))))
  ))
)
"#;

/// The undeclared-capability fixture: an import NO closed-table row
/// names — the derivation cannot even name its capability.
const UNDECLARED_COMPONENT: &str = r#"
(component
  (import "acme:widget/gadget@1.0.0" (instance))
)
"#;

fn component_bytes(wat: &str) -> Vec<u8> {
    wat::parse_str(wat).expect("fixture wat parses")
}

// ---------------------------------------------------------------------------
// The mirror pins (the Rust table ≡ the Lean SSOT's rows)
// ---------------------------------------------------------------------------

#[test]
fn effect_row_mirror_pins() {
    assert_eq!(wasi_row("wasi:cli/environment@0.3.0"), Some(vec![EffectAtom::HostIo]));
    assert_eq!(
        wasi_row("wasi:filesystem/types@0.3.0"),
        Some(vec![EffectAtom::Read, EffectAtom::Write, EffectAtom::HostIo])
    );
    assert_eq!(
        wasi_row("wasi:random/random@0.3.0"),
        Some(vec![EffectAtom::GuestCap, EffectAtom::HostIo])
    );
    assert_eq!(wasi_row("wasi:cli/exit@0.3.0"), Some(vec![EffectAtom::Fail]));
    // NOT in the table: nothing derivable — the undeclared face.
    assert_eq!(wasi_row("acme:widget/gadget@1.0.0"), None);
}

#[test]
fn derivation_is_the_fold_join() {
    // The env import alone: the boundary crossing alone.
    assert_eq!(
        derive_row(&["wasi:cli/environment@0.3.0".to_string()]).unwrap(),
        vec![EffectAtom::HostIo]
    );
    // Two imports JOIN (the join discipline — the set IS the rows' join).
    assert_eq!(
        derive_row(&[
            "wasi:cli/environment@0.3.0".to_string(),
            "wasi:clocks/monotonic-clock@0.3.0".to_string(),
        ])
        .unwrap(),
        vec![EffectAtom::HostIo, EffectAtom::Clock]
    );
    // The undeclared import refuses, named.
    match derive_row(&["acme:widget/gadget@1.0.0".to_string()]) {
        Err(HostError::CapabilityUndeclared(id)) => {
            assert_eq!(id, "acme:widget/gadget@1.0.0");
        }
        other => panic!("expected CapabilityUndeclared, got {other:?}"),
    }
    // The empty world derives the empty row (the pure discipline).
    assert_eq!(derive_row(&[]).unwrap(), vec![]);
}

#[test]
fn valve_order_decides() {
    // The empty allowance denies every non-empty required row (default-deny).
    assert!(!row_le(&[EffectAtom::HostIo], &[]));
    // The matching allowance passes.
    assert!(row_le(&[EffectAtom::HostIo], &[EffectAtom::HostIo]));
    // The under-allowance refuses (read beyond a hostIO-only grant).
    assert!(!row_le(&[EffectAtom::Read, EffectAtom::HostIo], &[EffectAtom::HostIo]));
}

// ---------------------------------------------------------------------------
// THE WASI FACE'S SMOKE: the p3-served import runs (the sync-first lane)
// ---------------------------------------------------------------------------

#[test]
fn wasi_import_runs_when_allowed() {
    let wasm = component_bytes(WASI_ENV_COMPONENT);
    let (_engine, _component, _store, _instance) =
        instantiate_wasi_component(&wasm, &[EffectAtom::HostIo])
            .expect("the env import's capability granted: the p3 linker serves it");
}

// ---------------------------------------------------------------------------
// THE VALVE'S TEETH: the load-time refusals (never traps, never runs)
// ---------------------------------------------------------------------------

#[test]
fn undeclared_allowance_denies_at_load() {
    let wasm = component_bytes(WASI_ENV_COMPONENT);
    match instantiate_wasi_component(&wasm, &[]) {
        Err(HostError::CapabilityDenied { import, missing }) => {
            assert_eq!(import, "wasi:cli/environment@0.3.0");
            assert_eq!(missing, "hostIO");
        }
        Err(other) => panic!("expected CapabilityDenied, got {other:?}"),
        Ok(_) => panic!("expected a load refusal, the component ran"),
    }
}

#[test]
fn under_allowance_denies_with_missing_atoms() {
    let wasm = component_bytes(WASI_ENV_COMPONENT);
    // write granted, env crossing NOT: the valve names the deficiency.
    match instantiate_wasi_component(&wasm, &[EffectAtom::Write]) {
        Err(HostError::CapabilityDenied { import, missing }) => {
            assert_eq!(import, "wasi:cli/environment@0.3.0");
            assert_eq!(missing, "hostIO");
        }
        Err(other) => panic!("expected CapabilityDenied, got {other:?}"),
        Ok(_) => panic!("expected a load refusal, the component ran"),
    }
}

#[test]
fn undeclared_import_refuses_at_load() {
    let wasm = component_bytes(UNDECLARED_COMPONENT);
    match instantiate_wasi_component(&wasm, &[EffectAtom::HostIo]) {
        Err(HostError::CapabilityUndeclared(id)) => {
            assert_eq!(id, "acme:widget/gadget@1.0.0");
        }
        Err(other) => panic!("expected CapabilityUndeclared, got {other:?}"),
        Ok(_) => panic!("expected a load refusal, the component ran"),
    }
}

// ---------------------------------------------------------------------------
// The committed component: zero imports → the empty required row → the
// closed box loads (default-deny is a no-op for the pure component).
// ---------------------------------------------------------------------------

#[test]
fn committed_component_loads_default_deny() {
    let wasm = load_component(&repo_gen_dir()).expect("the committed component loads");
    // Ground truth: the derivation sees ZERO imports.
    let engine = {
        let mut config = Config::new();
        config.wasm_component_model(true);
        Engine::new(&config).expect("engine")
    };
    let component = Component::from_binary(&engine, &wasm).expect("compile");
    assert!(component_imports(&engine, &component).is_empty());
    // The closed box: the empty allowance instantiates.
    let (_e, _c, _s, _i) =
        instantiate_wasi_component(&wasm, &[]).expect("zero imports pass the closed box");
}

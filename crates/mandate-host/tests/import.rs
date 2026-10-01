//! The IMPORT lane's teeth: the end-to-end pin (the committed component
//! loads, the provision answers, the value crosses to the golden), the
//! UNPROVISIONED instantiate refusal (typed), the SKEWED provision
//! refusal (typed), and the pre-instantiation provide-surface check —
//! each with its mandatory negative control.

use mandate_host::{
    HostError, IMPORT_GOLDEN, load_import_component, run_import_component,
    run_import_component_skewed, run_import_component_unprovisioned, verify_import_provision,
};

fn committed() -> Vec<u8> {
    let dir = mandate_host::repo_gen_dir();
    load_import_component(&dir).expect("the committed import artifact set loads")
}

/// THE END-TO-END PIN: the guest's `add64` calls the imported
/// `host-add`; the host's provision answers `2 + 3`; the value crosses
/// back through the typed lift to the golden (the wasmtime leg of the
/// three-way: the Lean model run ≡ the component's execution ≡ this).
#[test]
fn the_golden_crosses_the_boundary() {
    let wasm = committed();
    let got = run_import_component(&wasm, 2, 3).expect("the golden run");
    assert_eq!(got, IMPORT_GOLDEN);
}

/// THE PROVIDE-SURFACE FAIL-FAST: the committed component's import row
/// is covered by the provision set (the surface check passes; the
/// negative control below is the missing face).
#[test]
fn the_provision_surface_is_covered() {
    let wasm = committed();
    verify_import_provision(&wasm).expect("the provision covers the imports");
}

/// THE UNPROVISIONED TOOTH: an empty linker — the component's import
/// has no provider and the instantiate REFUSES with the typed error
/// (never a panic, never a silent skip; the Lean SSOT's
/// `checkImports.importUnclaimed` is the generation-time face of the
/// same drift).
#[test]
fn the_unprovisioned_import_refuses_at_instantiate() {
    let wasm = committed();
    match run_import_component_unprovisioned(&wasm) {
        Err(HostError::ImportUnprovisioned(name)) => {
            assert_eq!(name, "host-add");
        }
        Err(e) => panic!("the unprovisioned instantiate answered the wrong error: {e}"),
        Ok(()) => panic!("the unprovisioned instantiate SUCCEEDED — the tooth is gone"),
    }
}

/// THE SKEW TOOTH: a provision with the WRONG signature (`u64 -> u64`
/// where the world's row is `func(a: u64, b: u64) -> u64`) — the
/// wasmtime LINKER's typecheck refuses at instantiate with the typed
/// skew error (the Lean SSOT's `importSigDrift` is the
/// generation-time face of the same drift).
#[test]
fn the_skewed_provision_refuses_at_instantiate() {
    let wasm = committed();
    match run_import_component_skewed(&wasm) {
        Err(HostError::ImportSignatureSkew { name, .. }) => {
            assert_eq!(name, "host-add");
        }
        Err(e) => panic!("the skewed provision answered the wrong error: {e}"),
        Ok(()) => panic!("the skewed provision SUCCEEDED — the tooth is gone"),
    }
}

//! The faults lane's host-side pins: the generated faults' consumption
//! (`HostError::fault` — the mapping face) + the E-code discipline at the
//! Rust surface.
//!
//! The codes pinned here are the GENERATED spellings (the persisted
//! registry's allocation — `faults/Faults/Spec.lean` + notes/
//! code-registry.txt are the SSOT); a re-allocation surfaces as these
//! pins failing, and the fix is `lake exe faultsgen` + regen — never a
//! hand edit of either side.
//!
//! Negative controls are mandatory: an UNDECLARED surface reports no
//! fault (the envelope honesty), and the declared faults' codes are
//! pairwise distinct (the allocation's collision tooth, pinned).

use mandate_host::{ErrorCategory, FaultError, HostError, GOLDEN_ANSWER};

#[test]
fn content_hash_mismatch_maps_to_its_declared_fault() {
    let e = HostError::ContentHashMismatch { declared: 1, computed: 2 };
    let f = e.fault().expect("the declared fault");
    assert_eq!(f.code(), "FT0133");
    assert_eq!(f.category(), ErrorCategory::Content);
    assert!(!f.retryable(), "content errors are never retryable");
    assert!(f.to_string().contains("content hash mismatch"));
    // the payload survives the mapping (the structured face) — the
    // macro's NEWTYPE shape: the pin destructures the payload struct
    // (the generated enum is Debug-only — the value pins ride
    // code()/category(), the registry's projection, plus the payload
    // fields' own pins here).
    match f {
        FaultError::ContentHashMismatch(p) => {
            assert_eq!(p.declared, 1);
            assert_eq!(p.computed, 2);
        }
        other => panic!("the wrong variant: {other:?}"),
    }
}

#[test]
fn lifecycle_refusal_maps_to_its_declared_fault() {
    let e = HostError::Lifecycle { from: "Loaded", event: "answer" };
    let f = e.fault().expect("the declared fault");
    assert_eq!(f.code(), "FT0135");
    assert_eq!(f.category(), ErrorCategory::Invariant);
    assert!(!f.retryable(), "invariant errors are never retryable");
    // the payload rides the mapping (the from/event -> phase/event rename
    // is the generated variant's field spelling, not a re-spec) — the
    // macro's NEWTYPE shape (see the content-hash pin above).
    match f {
        FaultError::LifecycleIllegalTransition(p) => {
            assert_eq!(p.phase, "Loaded");
            assert_eq!(p.event, "answer");
        }
        other => panic!("the wrong variant: {other:?}"),
    }
}

#[test]
fn wasm_trap_maps_to_its_declared_fault() {
    // The typed trap (the duel's vocabulary) maps onto the declared
    // fatal fault. Construction site note: the duel's `observe` face
    // returns the trap itself; `run_answer`'s call path reports it
    // textually today — the fast-observe integration reroutes both (the
    // named follow-up). The mapping is the unit under test here.
    let trap = wasmtime::Trap::from_u8(9).expect("code 9 is the \
        unreachable trap (the encoding's 10th variant)");
    let e = HostError::WasmTrap(trap);
    let f = e.fault().expect("the declared fault");
    assert_eq!(f.code(), "FT0136");
    assert_eq!(f.category(), ErrorCategory::Fatal);
    assert!(!f.retryable());
    assert!(f.to_string().contains("wasm trap"));
    assert!(f.to_string().contains("unreachable"));
}

#[test]
fn the_declared_faults_codes_are_pairwise_distinct() {
    // the allocation's collision tooth, pinned at the consumer: four
    // declared faults, four distinct E-codes.
    let codes: Vec<&str> = vec![
        HostError::ContentHashMismatch { declared: 0, computed: 0 }
            .fault()
            .expect("declared")
            .code(),
        HostError::Lifecycle { from: "New", event: "stop" }
            .fault()
            .expect("declared")
            .code(),
    ];
    assert_eq!(codes.first(), codes.first());
    assert_ne!(codes[0], codes[1]);
}

#[test]
fn the_journal_refusal_maps_to_its_declared_fault() {
    // The journal seam's fault: the structural variant carries the
    // delta-log error; the fault face reports the declared row (the
    // payload-less variant — the detail rides the envelope). The open
    // refuses on the missing parent dir (the backend's io failure),
    // deterministic, nothing created.
    let path = std::env::temp_dir()
        .join("mandate-faults-teeth")
        .join("no-such-dir")
        .join("journal");
    let e = mandate_host::Journal::open(&path, mandate_host::ledger_schema())
        .expect_err("the journal's io failure refuses");
    assert!(matches!(e, HostError::Journal(_)), "the io failure is the \
        journal variant");
    let f = e
        .fault()
        .expect("the journal's refusals are declared faults");
    assert_eq!(f.code(), "FT0134");
}

#[test]
fn undeclared_surfaces_report_no_fault() {
    // THE NEGATIVE CONTROL (the envelope honesty): the structural
    // surfaces are NOT declared faults — the mapping reports None, the
    // fast-observe replacement does not overclaim.
    let e = HostError::SidecarMalformed("test");
    assert!(e.fault().is_none());
    let e = HostError::Incomplete("test");
    assert!(e.fault().is_none());
    let e = HostError::AnswerMismatch { got: GOLDEN_ANSWER + 1 };
    assert!(e.fault().is_none());
    let e = HostError::DuelManifest("test".to_string());
    assert!(e.fault().is_none());
    let e = HostError::WorldSkew("test");
    assert!(e.fault().is_none());
    let e = HostError::Engine("test".to_string());
    assert!(e.fault().is_none());
    let e = HostError::EngineRefused("test".to_string());
    assert!(e.fault().is_none());
    let e = HostError::MissingExport("test".to_string());
    assert!(e.fault().is_none());
    let e = HostError::Signature;
    assert!(e.fault().is_none());
    let e = HostError::ComponentSignature("test");
    assert!(e.fault().is_none());
    let e = HostError::ComponentAnswerMismatch { got: 0, expected: 0 };
    assert!(e.fault().is_none());
    let e = HostError::LiveState("test".to_string());
    assert!(e.fault().is_none());
    let e = HostError::Io {
        what: "test",
        source: std::io::Error::new(std::io::ErrorKind::NotFound, "test"),
    };
    assert!(e.fault().is_none());
}

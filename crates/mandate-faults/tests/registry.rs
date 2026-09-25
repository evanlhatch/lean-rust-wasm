//! The generated fault surface's pins (wave-30 C1 — the fast-observe
//! `error!` face): the registry ENTRIES resolve through `lookup_error`
//! after `init_host()`, the E-code spellings are the persisted
//! allocation's (notes/code-registry.txt — the SSOT), the
//! category↔policy axis is fast-observe's own.
//!
//! Negative controls are mandatory: an UNALLOCATED code misses the
//! registry (no fabricated entry), the codes are pairwise distinct.

use mandate_faults::{
    init_host, ContentHashMismatch, FaultError, LifecycleIllegalTransition, WasmTrap,
};

/// The four declared rows' spellings (the persisted allocation, pinned
/// here at the consumer — a re-allocation moves these pins AND the
/// artifact in the same commit, never a hand edit of either side).
const CODES: [&str; 4] = ["FT0133", "FT0134", "FT0135", "FT0136"];

#[test]
fn init_registers_and_lookup_resolves_every_code() {
    init_host();
    for code in CODES {
        let e = fast_observe::lookup_error(code)
            .unwrap_or_else(|| panic!("registry lost {code} after init_host"));
        assert_eq!(e.code, code);
        // the registry entry is the macro's projection of the same Lean
        // row the enum variant renders (one registry, two faces)
        assert!(
            e.module.contains("mandate_faults"),
            "the entry names its module: {}",
            e.module
        );
    }
}

#[test]
fn unallocated_code_misses_the_registry() {
    // THE NEGATIVE CONTROL: no fabricated entry — a code outside the
    // persisted allocation is a registry MISS.
    assert!(fast_observe::lookup_error("FT0999").is_none());
}

#[test]
fn each_variant_reports_its_allocated_code_category_and_advice() {
    let faults = [
        (
            FaultError::ContentHashMismatch(ContentHashMismatch {
                declared: 1,
                computed: 2,
            }),
            "FT0133",
            fast_observe::ErrorCategory::Content,
        ),
        (FaultError::JournalCorrupt, "FT0134", fast_observe::ErrorCategory::Content),
        (
            FaultError::LifecycleIllegalTransition(LifecycleIllegalTransition {
                phase: "Loaded".to_string(),
                event: "stop".to_string(),
            }),
            "FT0135",
            fast_observe::ErrorCategory::Invariant,
        ),
        (
            FaultError::WasmTrap(WasmTrap { detail: "x".to_string() }),
            "FT0136",
            fast_observe::ErrorCategory::Fatal,
        ),
    ];
    for (f, code, category) in faults {
        assert_eq!(f.code(), code, "the allocated spelling");
        assert_eq!(f.category(), category, "the policy axis");
        // the fix is the spec's advice field — present on every declared row
        assert!(!f.advice().unwrap_or("").is_empty());
        // the display is the spec's display field, rendered
        assert!(f.to_string().len() > 0);
    }
}

#[test]
fn transient_is_the_only_retryable_category() {
    // the policy axis: none of the DECLARED rows is transient today, so
    // none is retryable — the pin rides the category() face (the macro's
    // projection), never a second table.
    let f = FaultError::JournalCorrupt;
    assert!(!f.retryable());
    assert_eq!(
        f.category().policy(),
        fast_observe::Policy::FixInput,
        "content faults fix the input, never retry"
    );
}

#[test]
fn the_entries_are_the_four_declared_rows_pairwise_distinct() {
    assert_eq!(FaultError::ENTRIES.len(), 4);
    let mut codes: Vec<&str> = FaultError::ENTRIES.iter().map(|e| e.code).collect();
    codes.sort();
    codes.dedup();
    assert_eq!(codes.len(), 4, "the allocation's collision tooth");
}

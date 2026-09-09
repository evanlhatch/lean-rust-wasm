//! Capability-denial faults — fast-observe is the error tool; engine
//! plumbing errors flow through the boxed [`HostFault::Engine`] variant.
//!
//! Stage C: the enum is GENERATED from the Lean faults registry
//! (`Faults/Spec/Host.lean` → `src/host_faults_generated.rs`, codes
//! allocated at E110) — the hand-written `error!` block was deleted.
//! One E-code space with the guest (E100… apiFaults): `lookup_error`
//! resolves either side's codes from the same fast-observe registry.

// The generated module lives at the repo root's src/ (one-writer
// discipline: the faults emitter owns it; `just gen` regenerates).
#[path = "../../../src/host_faults_generated.rs"]
pub mod host_faults_generated;

pub use host_faults_generated::{
    Engine, HostFault, MissingExport, UnsupportedResult, init_host,
};

/// Register the host fault entries — call once at startup (native builds
/// would resolve codes at link time via linkme; explicit call is the
/// generated contract either way).
pub fn register() {
    init_host();
}

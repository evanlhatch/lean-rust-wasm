//! mandate-host — the honest host seed: a CONSUMER of the checked
//! artifacts, nothing more.
//!
//! WHAT THE HOST IS (notes/v3/03-bidirectional.md): Lean owns meaning;
//! Rust owns implementation. This crate implements nothing that the
//! model specifies — it LOADS, VERIFIES, and RUNS what the toolchain
//! emitted:
//!
//! - `gen/wasm-slice.wasm` — the 39-byte validated module; its export
//!   `answer` runs to `i64 42` (the golden, pinned in the tests).
//! - `gen/wasm-slice.wasm.hdr` — the GENERATED sidecar whose
//!   `content hash <n>` names the bytes (Kit.Emit.bytesHash — the LCG
//!   fold, re-derived consumer-side in [`artifact::bytes_hash`]).
//! - `gen/schema-slice.wit` — the WIT surface the toolchain committed
//!   (presence-level skew check; its byte-tie stays Lean-gate-owned).
//!
//! WHAT THE HOST ISN'T: no second semantics, no re-implementation of
//! the model, no codec, no schema types. The artifacts are the only
//! authority; a byte of drift between what the toolchain emitted and
//! what this host runs is a STARTUP REFUSAL (the skew teeth), never a
//! silently-different execution.
//!
//! ERROR DISCIPLINE (notes/v3/12-construction.md §8): no bare panics
//! on real error paths — [`HostError`] is total over the failure
//! surface. The fast-observe fault-registry integration (`@[host_fault]`
//! E-codes, the causal trees, the span coverage) is a LATER order; this
//! enum is the honest first seed, one variant per future fault row.

pub mod artifact;
pub mod component;
pub mod duel;
pub mod engine;
pub mod persistence;

pub use artifact::{GenSlice, bytes_hash};
pub use component::{
    load_component, load_string_component, run_component, run_string_component, GUEST_EXPORT,
    GUEST_GOLDEN, STRING_GOLDEN, STRING_GOLDEN_INPUT, STRING_GUEST_EXPORT,
};
pub use duel::{DuelReport, DuelRow, Expectation, RowVerdict, run_duel};
pub use engine::{GOLDEN_ANSWER, run_answer, run_slice};
pub use persistence::Journal;

use std::path::{Path, PathBuf};

/// The typed error surface (the first-seed shape; the fault-registry
/// rows land later — see the crate doc).
#[derive(Debug, thiserror::Error)]
pub enum HostError {
    /// A file the artifact set requires could not be read.
    #[error("artifact unreadable: {what}: {source}")]
    Io {
        what: &'static str,
        #[source]
        source: std::io::Error,
    },

    /// The sidecar exists but is not a well-formed GENERATED header
    /// naming a `content hash`.
    #[error("sidecar malformed: {0}")]
    SidecarMalformed(&'static str),

    /// THE skew tooth: the bytes the host would run do not hash to the
    /// value the sidecar declares — the artifact the toolchain emitted
    /// is not the artifact in hand.
    #[error(
        "content hash mismatch: sidecar declares {declared}, artifact computes {computed}"
    )]
    ContentHashMismatch { declared: u64, computed: u64 },

    /// The artifact set is incomplete (a sibling artifact is absent)
    /// or fails the presence-level surface check.
    #[error("artifact set incomplete: {0}")]
    Incomplete(&'static str),

    /// The wasmtime engine refused the bytes (compile/validate/link).
    #[error("wasm engine: {0}")]
    Engine(String),

    /// The engine refused to ACCEPT the module (compile/validate) —
    /// distinct from a runtime trap: this is the refusal the duel's
    /// `.refuse` rows EXPECT (the invalid control's second refusal).
    #[error("wasm engine refused the module: {0}")]
    EngineRefused(String),

    /// A runtime wasm trap (the duel's `.trap` rows expect this).
    #[error("wasm trap: {0}")]
    WasmTrap(#[source] wasmtime::Trap),

    /// The duel's manifest is malformed (no GENERATED header, no
    /// generator row, an unknown expectation word, a bad row).
    #[error("duel manifest malformed: {0}")]
    DuelManifest(String),

    /// The module does not export `answer`.
    #[error("missing export: {0}")]
    MissingExport(String),

    /// The `answer` export exists but does not have the `-> i64`
    /// signature.
    #[error("export signature: expected `answer : -> i64`")]
    Signature,

    /// The module ran but did not produce the golden.
    #[error("golden answer mismatch: got {got}, expected {GOLDEN_ANSWER}")]
    AnswerMismatch { got: i64 },

    /// The component lane's WORLD skew: the committed `.wit` surface
    /// does not carry the world contract the host consumes (the
    /// generated header, the package line, the world block naming the
    /// guest export). The world is the SSOT — a skew refuses.
    #[error("component world skew: {0}")]
    WorldSkew(&'static str),

    /// The component's export exists but does not have the signature
    /// the typed lift demands (`expected` = the contract the world
    /// declares — the canonical-ABI typed lift refuses; the string
    /// lane's `(ptr, len)` lowering and the tuple lane's flattening
    /// ride the same tooth).
    #[error("component export signature: expected {0}")]
    ComponentSignature(&'static str),

    /// The component ran but did not produce the golden (the typed
    /// call's result is the model's fact, consumed — never re-derived).
    #[error("component answer mismatch: got {got}, expected {expected}")]
    ComponentAnswerMismatch { got: u64, expected: u64 },

    /// The persistence seam's delta-log failure (the journal beside the
    /// host: a torn tail recovers; a corrupt frame refuses — typed,
    /// never a panic, never a silent truncation).
    #[error("journal: {0}")]
    Journal(#[from] mandate_delta::DeltaError),
}

/// The `gen/` directory's location as shipped by the toolchain
/// (repo-root-relative; the crate is a consumer, the paths are the
/// committed universe's).
pub fn repo_gen_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../gen")
}

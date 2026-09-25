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
//! surface. THE FAULTS LANE (landed, wave-30 C1): the model-level refusals
//! are DECLARED in the Lean registry (`faults/Faults/Spec.lean`) and
//! consumed through the generated enum ([`FaultError`] — fast-observe's
//! `error!` face: the allocated E-codes, the registry ENTRIES, the policy
//! axis, the advice); [`HostError::fault`] is the mapping face. THE
//! OBSERVABILITY FACE (C1): every lifecycle/ledger operation opens its
//! dotted-static `scope!` (the schema's namespace path as the name source;
//! 'static low-cardinality ONLY — high-cardinality data rides log kv,
//! NEVER scope tags); [`init_observability`] is the composition root's
//! init discipline. The honest judgment: [`HostError`] STAYS the
//! structural envelope — its io/engine surfaces are implementation
//! plumbing, not declared faults (they report `None`); the generated enum
//! does not replace it (the causal-tree `Fault<HostFault>` crossing is the
//! named follow-up, design-faults §2.3's W10.3) — the declared faults
//! ride it. NIGHTLY: fast-observe is nightly-only —
//! `crates/rust-toolchain.toml` pins the lane.

pub mod artifact;
pub mod component;
pub mod duel;
pub mod engine;
pub mod lifecycle;
pub mod live;
pub mod persistence;

pub use artifact::{GenSlice, bytes_hash};
pub use mandate_faults::{ErrorCategory, FaultError};

/// THE COMPOSITION ROOT'S INIT (C1's host integration — the main/init
/// discipline): the fault registry's static registration (the wasm
/// discipline — on native the linkme slice already carries the entries
/// and this is harmless) + fast-observe's deployment init (idempotent —
/// a second init is ignored upstream). Call once before the first
/// span/fault; the lifecycle machine calls it at [`HostMachine::new`].
pub fn init_observability() {
    mandate_faults::init_host();
    fast_observe::init();
}
pub use component::{
    load_component, load_edge_component, load_string_component, run_component,
    run_edge_component, run_string_component, EDGE_EXPORTS_1, EDGE_EXPORTS_2, EDGE_PARITY,
    EDGE_WASM, EDGE_WIT, GUEST_EXPORT, GUEST_GOLDEN, STRING_GOLDEN, STRING_GOLDEN_INPUT,
    STRING_GUEST_EXPORT,
};
pub use duel::{DuelReport, DuelRow, Expectation, RowVerdict, run_duel};
pub use engine::{GOLDEN_ANSWER, run_answer, run_slice};
pub use lifecycle::{
    HostMachine, Phase, ModelTransition, MODEL_TRANS, EVENT_CALL, EVENT_INSTANTIATE, EVENT_LOAD,
    EVENT_START, EVENT_STOP,
};
pub use live::{Account, Live, LiveVerdict, Proposal, ViolationRow, ledger_schema, run_commit_duel};
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

    /// The lifecycle's own refusal: a journaled row lost its schema
    /// (a journal this crate wrote can only be replayed against the
    /// SAME schema — a drift is a typed fault, never a panic or a
    /// silent skip).
    #[error("live state: {0}")]
    LiveState(String),

    /// THE LIFECYCLE TOOTH (the model: `Machines.HostLifecycle` — the
    /// host lifecycle is a machine, the Lean side's `machine!`
    /// declaration): an illegal transition refuses TYPED — the event
    /// the implementation was asked to run from the phase it is in is
    /// not a row of the model's transition table. The host never
    /// silently proceeds past a phase boundary; the refusals
    /// (`refuseLoad`/`refuseInstantiate`/`refuseStart`/`trap`) are
    /// themselves model rows and land in `Phase::Failed` instead.
    #[error("illegal lifecycle transition: {event} from {from} (the model: Machines.HostLifecycle)")]
    Lifecycle { from: &'static str, event: &'static str },
}

impl HostError {
    /// THE FAULT FACE (the faults lane's consumption — 12 §8): the
    /// declared fault this error instantiates, if any. The four
    /// model-level refusals map onto the generated [`FaultError`]
    /// variants — the E-code, the policy axis and the advice flow from
    /// the LEAN REGISTRY (the persisted allocation), never a hand
    /// constant here. SHAPE (the macro's grammar): struct variants are
    /// NEWTYPES wrapping the generated payload structs — the mapping
    /// constructs the payload and wraps it. The structural surfaces
    /// (io, engine, duel plumbing) are not declared faults — they report
    /// `None` (the honest judgment: the envelope stays; the
    /// causal-tree `Fault<…>` replacement is the named follow-up).
    pub fn fault(&self) -> Option<FaultError> {
        use mandate_faults::{ContentHashMismatch, LifecycleIllegalTransition, WasmTrap};
        match self {
            HostError::ContentHashMismatch { declared, computed } => {
                Some(FaultError::ContentHashMismatch(ContentHashMismatch {
                    declared: *declared,
                    computed: *computed,
                }))
            }
            HostError::Journal(_) => Some(FaultError::JournalCorrupt),
            HostError::Lifecycle { from, event } => {
                Some(FaultError::LifecycleIllegalTransition(
                    LifecycleIllegalTransition {
                        phase: (*from).to_string(),
                        event: (*event).to_string(),
                    },
                ))
            }
            HostError::WasmTrap(t) => Some(FaultError::WasmTrap(WasmTrap {
                detail: t.to_string(),
            })),
            _ => None,
        }
    }
}

/// The `gen/` directory's location as shipped by the toolchain
/// (repo-root-relative; the crate is a consumer, the paths are the
/// committed universe's).
pub fn repo_gen_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../gen")
}

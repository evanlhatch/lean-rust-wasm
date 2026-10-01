//! THE WITNESS GATE LANE — the host-gating lane's host face (the D6
//! named follow-up's completion). The legacy `@[invariant]`
//! discipline: the host calls the GUEST-COMPILED CHECKER to GATE
//! processing. Here the processing is the ledger's commit: a proposed
//! transfer + its certificate (the producer's flat 5-slot wire) cross
//! into the committed component's `witness-gate` export, and the
//! checker's verdict decides whether [`Live::commit`] is reached at
//! all.
//!
//! The roles, honest: the guest checker owns the INVARIANT's teeth
//! (the certificate's every recorded verdict is RE-FIRED against the
//! recomputed checks — verified, never trusted); the host's own
//! mirror checker (`Live::check`'s violation queries) stays the
//! STATE's teeth (the post-state's account-level rows). The gate is
//! CONJUNCTIVE: a commit passes only when BOTH faces accept — the
//! guest's typed refusal refuses before the host's checker runs.
//!
//! The parity discipline (the edge lane's shape, two legs): the Lean
//! EXECUTOR over the fixture's own module answers the pinned codes
//! (`ComponentTests.WitFixture.legExecutorParity`), and THIS face —
//! wasmtime's typed calls over the COMMITTED component — answers the
//! same literals; the byte-tie ties the committed component to that
//! module, closing the circle. The code table is the Lean SSOT's
//! (`ComponentTests.WitFixture`'s refusal codes), mirrored here as
//! constants; the teeth pin both faces at the same literals.
//!
//! ERROR DISCIPLINE (12 §8): a refusal is a TYPED error
//! ([`HostError::WitnessRefused`] — the checker's VERDICT, codes
//! 1/2/3), never a trap ([`HostError::WasmTrap`] is the component's
//! BUG, a different KIND — the tests pin both) and never an engine
//! string. A refusal produces NO state change and NO journal entry —
//! the commit is never reached.

use crate::component::run_witness_gate;
use crate::live::{Live, LiveVerdict, Proposal};
use crate::HostError;

/// The valid row's certificate wire (the producer's certificate's
/// slots — `component::WITNESS_WIRE_OK` re-exported here as the gate's
/// honest-certificate face; a caller shipping anything else is either
/// tampered (2) or wrong-schema (3), and the checker refuses).
pub use crate::component::WITNESS_WIRE_OK as WIRE_OK;

/// The refusal codes (the Lean SSOT's mirror — re-exported for the
/// tests' literal pins).
pub use crate::component::{WIT_CODE_CLAIM_FALSE, WIT_CODE_TAMPERED, WIT_CODE_WRONG_SCHEMA};

/// THE GATE: the proposed row + its certificate wire cross into the
/// guest-compiled checker; `Ok(())` = the gate opens, `Err` = the
/// typed refusal (the checker's verdict — never a trap, never an
/// engine string). The tiered codes: 1 = the claim is FALSE at the
/// proposed row (no honest certificate exists), 2 = TAMPERED record
/// (a recorded verdict disagrees with the recomputed check), 3 =
/// WRONG-SCHEMA certificate (the shape tags do not fit the deployed
/// invariant's certificate shape).
///
/// # Errors
/// [`HostError::WitnessRefused`] (the verdict), [`HostError::WasmTrap`]
/// (the component's bug), or the engine/compile faces — all typed.
pub fn witness_gate(wasm: &[u8], p: &Proposal, wire: &[u64; 5]) -> Result<(), HostError> {
    run_witness_gate(wasm, p.src, p.dst, p.amount, wire)
}

/// THE GATED COMMIT (the legacy `@[invariant]` discipline's host
/// face): the guest-compiled checker's verdict GATES [`Live::commit`].
/// A refusal returns BEFORE the commit fires — no state change, no
/// journal entry, the version unmoved. A gate-open hands the proposal
/// to the live loop's OWN verdict logic (stale/violated stay the
/// host-checker's faces — the gate is conjunctive, the guest's teeth
/// do not REPLACE the state's).
///
/// # Errors
/// The gate's typed refusals (see [`witness_gate`]) plus `Live::
/// commit`'s own genuine faults (the journal's I/O).
pub fn gated_commit(
    live: &mut Live,
    p: &Proposal,
    wasm: &[u8],
    wire: &[u64; 5],
) -> Result<LiveVerdict, HostError> {
    witness_gate(wasm, p, wire)?;
    live.commit(p)
}

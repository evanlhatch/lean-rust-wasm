/-
# SchemaLang.Pipeline — the forge build pipeline as a Machine

The pipeline stages (reflection → universeCheck → emitters → byte-tie)
modeled as a guarded state machine (Machines.Machine, authored via
`machine!`). The universe it processes is `SchemaLang.Item`'s `List Item`
(see `universeCheck`, `universeWellFormed`); this file models the STAGE
discipline, not the item algebra.

Two projections, per Machines.Core:
- executable: `pipeline.step?` / `pipeline.run` — invalid sequences are
  REJECTED (a `check` fired without `reflect` returns `none`),
- proof: `pipeline.tr` + `run_preserves` — every successful run ends in an
  invariant-satisfying state; `failed` is the one state the invariant
  excludes (errors are observable states, not silent ones).

Acyclicity: the happy path is a linear chain
idle → reflecting → checked → emitted → tied. `rank_advances` proves every
non-`reset` transition strictly increases `rank` (no cycle without reset);
`happy_path` executes the chain end-to-end.

The conformance battery (Machines.Testing.conformance) sweeps the full
6-state space; `Pipeline.pipelineConformance` is the positive result,
`pipelineGuardControl` the negative control (a dead-event machine must
FAIL guard coverage — the battery is not vacuous).
-/

import Machines.Dsl
import Machines.Testing
import SchemaLang.Item

open Machines.Dsl

namespace SchemaLang

/-! ## States, events, machine -/

/-- The pipeline states. `failed` carries the stage that failed plus its
    diagnostics (the `universeCheck` diagnostic authority, stage-tagged). -/
inductive PipelineState where
  | idle
  | reflecting    -- @[schema] reflection ran, registry populated
  | checked       -- universeCheck passed (wellFormed, no diags)
  | emitted       -- all emitters ran, artifacts written
  | tied          -- byte-tie clean (artifacts match committed)
  | failed (stage : String) (diags : List String)
deriving Repr, BEq, DecidableEq, Inhabited

-- The pipeline machine. Every stage's guard is its predecessor state;
-- `reset` is always enabled (the recovery edge, including out of
-- `failed`). The invariant excludes ONLY `failed` — an error state is
-- not a legal resting state. (plain comment: doc comments cannot
-- precede machine! — the custom command rejects them)
machine! pipeline where
  State: PipelineState
  Inv: fun s => match s with
    | .failed _ _ => false  -- failed is NOT in the invariant (error state)
    | _ => true
  event: reflect guard: (fun s => s = .idle) action: (fun _ _ => .reflecting)
  event: check guard: (fun s => s = .reflecting) action: (fun _ _ => .checked)
  event: emit guard: (fun s => s = .checked) action: (fun _ _ => .emitted)
  event: tie guard: (fun s => s = .emitted) action: (fun _ _ => .tied)
  event: reset guard: (fun _ => true) action: (fun _ _ => .idle)

/-- The invariant is decidable over the enumerated states (the conformance
    battery's `DecidablePred` requirement). -/
instance : DecidablePred pipeline.Inv := fun s => by
  cases s with
  | idle => exact isTrue (by rfl)
  | reflecting => exact isTrue (by rfl)
  | checked => exact isTrue (by rfl)
  | emitted => exact isTrue (by rfl)
  | tied => exact isTrue (by rfl)
  | failed _ _ => exact isFalse (by simp)

/-- The full state space: the 5 invariant states + the error state (one
    representative failure). The battery sweeps ALL of them. -/
def pipelineStates : List PipelineState :=
  [.idle, .reflecting, .checked, .emitted, .tied, .failed "check" ["dupName `user`"]]

/-- The conformance battery: deadlock-freedom + guard coverage +
    invariant non-vacuity over the full state space. Labels are GENERATED
    by `machine!` (`pipeline.labels`). -/
def pipelineConformance : List (String × TestKit.CheckResult) :=
  Machines.Testing.conformance pipeline pipeline.labels pipelineStates pipeline.labels_complete

-- NEGATIVE CONTROL: a machine with an unsatisfiable guard (a dead event)
-- must FAIL guard coverage — proves the battery is not vacuous.
machine! pipelineDead where
  State: Nat
  Inv: fun _ => True
  event: tick guard: (fun _ => true) action: (fun s _ => s + 1)
  event: dead guard: (fun s => s > 0 ∧ s < 0) action: (fun s _ => s)
    safety: (by intro s h; simp at h)

/-! ## Acyclicity — the happy path is a linear chain -/

/-- Position along the happy chain; `failed` and `idle` both rank 0
    (both only leave via `reset`, which re-enters at 0). -/
def PipelineState.rank : PipelineState → Nat
  | .idle => 0
  | .reflecting => 1
  | .checked => 2
  | .emitted => 3
  | .tied => 4
  | .failed _ _ => 0

/-- Core acyclicity fact, on the action directly: firing ANY non-`reset`
    event from ANY state lands strictly higher on the chain (the guard
    rules out the non-advancing firings). -/
theorem rank_advances (s : PipelineState) (l : pipeline.Label)
    (hnr : l ≠ .reset) (w : (pipeline.event l).guard s = true) :
    s.rank < ((pipeline.event l).action s w).rank := by
  cases s <;> cases l <;>
    simp [pipeline, pipeline.spec, PipelineState.rank] at hnr w ⊢ <;>
    omega

/-- Every NON-reset transition strictly increases the rank: the pipeline
    is a DAG whose only cycles pass through `reset` (the explicit recovery
    edge). The happy chain idle → reflecting → checked → emitted → tied
    can never return to an earlier stage. -/
theorem rank_advances_tr (s s' : PipelineState) (l : pipeline.Label)
    (htr : pipeline.tr s l s') (hnr : l ≠ .reset) :
    s.rank < s'.rank := by
  obtain ⟨w, hact⟩ := htr
  have h := rank_advances s l hnr w
  rw [hact] at h
  exact h

/-- The happy path EXECUTES: reflect, check, emit, tie — idle to tied in
    four accepted steps. -/
theorem happy_path : pipeline.run .idle [.reflect, .check, .emit, .tie]
    = some ([(.reflect, .reflecting), (.check, .checked), (.emit, .emitted), (.tie, .tied)], .tied) :=
  rfl

/-- Out-of-order firing is REJECTED, observably: `check` without
    `reflect` cannot start the pipeline. -/
theorem reject_out_of_order :
    pipeline.run .idle [.check] = none := rfl

/-- `reset` recovers from ANY state, `failed` included — the error state
    is a resting place, not a wedge. -/
theorem reset_from_failed :
    pipeline.run (.failed "tie" ["artifact drift"]) [.reset] = some ([(.reset, .idle)], .idle) :=
  rfl

/-! ## The transition table — DATA, emitted to the Rust driver

The forge driver (crates/forge) sequences its gen/check phases through
THE SAME machine: the table below is folded into
`src/pipeline_generated.rs` (pipelineEmitter), forge includes it and
steps Idle→…→Tied — an illegal transition aborts the driver. The
agreement theorem makes the emitted table the machine's step?, so the
proved properties (`rank_advances`, `happy_path`, `reject_out_of_order`)
govern the Rust driver. This is the connection the old "Pipeline is a
model forge never reads" gap lacked: the driver consumes the spec.
-/

/-- The transition table as plain data: (event, from, to) over the
    machine's GENERATED `Label` (one ctor per event — the same type the
    proofs case-split). One row per enabled (event, from) with CONCRETE
    from-states; the `failed` state (arbitrary strings — data can't
    wildcard it) is handled structurally in `tableStep?`.
    `tableStep?_eq_step?` PROVES the composition is the machine. -/
def pipelineTrans : List (pipeline.Label × PipelineState × PipelineState) :=
  [ (.reflect, .idle, .reflecting)
  , (.check, .reflecting, .checked)
  , (.emit, .checked, .emitted)
  , (.tie, .emitted, .tied)
  , (.reset, .idle, .idle)
  , (.reset, .reflecting, .idle)
  , (.reset, .checked, .idle)
  , (.reset, .emitted, .idle)
  , (.reset, .tied, .idle) ]

/-- Table lookup: the first row matching (event, from); `none` = illegal
    (the machine's guard failed). `failed` is structural: `reset` recovers
    (the recovery edge), every other event is rejected. -/
def tableStep? (e : pipeline.Label) (s : PipelineState) : Option PipelineState :=
  match s with
  | .failed _ _ => match e with | .reset => some .idle | _ => none
  | _ =>
      (pipelineTrans.filter fun (e', s', _) => e' == e && s' == s)
        |>.head?.map fun (_, _, to') => to'

/-- The emitted table IS the machine: same total step function. Every
    guard in `machine! pipeline` is an equality on the state, so the
    table (+ the structural failed arm) enumerates exactly the enabled
    (event, from, to) triples. -/
theorem tableStep?_eq_step? (e : pipeline.Label) (s : PipelineState) :
    tableStep? e s = pipeline.step? s e := by
  cases s <;> cases e <;>
    simp [tableStep?, pipeline, pipeline.spec, PipelineState.rank] <;> rfl

end SchemaLang

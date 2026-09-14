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
/-- Position along the happy chain; `failed` and `idle` both rank 0
    (both only leave via `reset`, which re-enters at 0). -/
def PipelineState.rank : PipelineState → Nat
  | .idle => 0
  | .reflecting => 1
  | .checked => 2
  | .emitted => 3
  | .tied => 4
  | .failed _ _ => 0

machine! pipeline where
  State: PipelineState
  Inv: fun s => match s with
    | .failed _ _ => false  -- failed is NOT in the invariant (error state)
    | _ => true
  rank: PipelineState.rank rewind: reset
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

/-! ## The stage machine, as the driver consumes it

forge (crates/forge) sequences its gen/check phases through the
GENERATED stage machine (`src/pipeline_generated.rs`, emitted by the
`pipelineEmitter`). `tableStep?` is the STRUCTURAL match over the
machine's own Label + State — and `tableStep?_eq_step?` PROVES it is
the machine's `step?`, so the emitted Rust (which mirrors this match —
the Rust-side `happy_path_assertions` + the spliced-run tests are its
drift guards) is the machine, not a sketch of it: the proved
`rank_advances`/`reject_out_of_order` govern the driver.
-/

/-- The transition DATA the emitter folds (`Emit.Registry.pipelineArms`
    generates the Rust match from these rows, with the reset-wildcard
    collapse checked against this table). The DATA and the structural
    `tableStep?` below are two readings of one machine — the theorem
    pins the structural reading to the machine; the emitter's
    wildcard-check + the Rust-side assertions guard the data reading. -/
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

/-- The stage machine as a total lookup (STRUCTURAL — the theorem's
    subject): the machine's guards are equality tests on the state, so
    the match arms are exactly the enabled (event, from, to) triples;
    `reset` fires from EVERY state (the recovery edge — `failed`
    included); everything else is illegal. -/
def tableStep? : pipeline.Label → PipelineState → Option PipelineState
  | .reflect, .idle => some .reflecting
  | .check, .reflecting => some .checked
  | .emit, .checked => some .emitted
  | .tie, .emitted => some .tied
  | .reset, _ => some .idle
  | _, _ => none

/-- The emitted table IS the machine. -/
theorem tableStep?_eq_step? (e : pipeline.Label) (s : PipelineState) :
    tableStep? e s = pipeline.step? s e := by
  cases s <;> cases e <;>
    simp [tableStep?, pipeline, pipeline.spec]

end SchemaLang

/-
# Gates.DriverMachine — the gates driver as a machine

The F3 wave's shape (notes/canon.md's "the build pipeline itself = a
machine" row, materialized on the gates PROCESS): the four gate stages —
load → regenerate → compare → report — are a guarded `Machines.Machine`
(`gateRun`), and the gates exe's driver steps through it. The IO stays
where it belongs: the machine's events are PURE state transitions (stage
bookkeeping, attempt counting); the DRIVER performs each stage's effect
(regenerate the artifact, read the committed baseline, print the report)
between steps. The machine enforces what the driver must not:
- the stage order (a `compare` before a verdict, a `report` before any
  regeneration, are REJECTED — observable `none`s),
- the retry-on-transient edge back to `regen` (a transient regeneration
  failure rewinds; only a non-transient verdict advances to `compare`),
- the attempt bookkeeping (each regeneration — transient or not — counts).

The machine's `Inv` is the stage discipline's surviving property: a
transient verdict is legal only at the decide point or the retry anchor.

Acyclicity: `rank` (attempts dominate, stage breaks ties) strictly
increases per non-rewind event (`gateRun.rank_advances`), `retry` being
the rewind — the pair is the "generated step/rank" the driver reuses.
DELIBERATE EXCLUSION: the rank pair is hand-written under the generated
names, not the `rank:` clause's output — that proof case-splits `s` per
STATE CONSTRUCTOR, but the driver's `PipelineState` is a STRUCTURE
(stage field + attempt counter), which `cases s` splits into fields and
`omega` cannot reason about (`stageRank` of a variable). The
`step?`/`run`/`tr` surface the driver steps through remains the
machine!'s generated one.

Scope (honest): ONE subcommand routes through this machine —
`gates coverage`'s check lane (`Gates.Coverage.run` → `runGate`). The
other baseline lanes keep `TestKit.runBaselines` (the shared verdict
loop); the sharded `--package` modes (axioms/native-policy/kernel-check/
docs-check child) keep their existing drivers unchanged. Wiring the exe's
`main` directly (stepping EVERY subcommand) would couple the sharded
paths to the machine's stage model with no behavioral gain — the machine
defines the canonical route and one production consumer proves the step
curve; the rest are follow-ups.

Ownership: new here; F3. The machine!-assembled parts follow the
Machines.Sync pattern (`machine!` with payload labels; the structure
state is this machine's own shape).
-/

module

public import Machines.Dsl
public import Machines.Core
public import TestKit.Baseline

@[expose] public section

namespace Gates.DriverMachine

/-! ## The machine's state -/

/-- The four gate stages (plus the pre-launch `.dead` and the terminal
    `.done`). The `.regen` stage is the retry anchor: a transient
    regeneration rewinds here. -/
inductive Stage where
  | dead | load | regen | decide | report | done
deriving Repr, DecidableEq

/-- The regeneration's verdict, fed back at the decide point: `.transient`
    rewinds; `.inSync` / `.drifted` / `.absent` proceed to the report. -/
inductive Verdict where
  | transient | inSync | drifted | absent
deriving Repr, DecidableEq

/-- The pipeline position: the current stage, the last regeneration's
    verdict, and the regeneration attempt count (the retry bookkeeping). -/
structure PipelineState where
  stage : Stage
  lastVerdict : Verdict
  attempts : Nat
deriving Repr, DecidableEq

/-- The stage's position on the happy chain (dead 0 → done 5). -/
def stageRank : Stage → Nat
  | .dead => 0 | .load => 1 | .regen => 2 | .decide => 3 | .report => 4 | .done => 5

/-- The acyclicity rank: attempts dominate, stage breaks ties. Every
    non-rewind event strictly increases it
    (`gateRun.rank_advances` — hand-written, see the header); the rewind
    (`retry`) may step back within an attempt. -/
def PipelineState.rank (s : PipelineState) : Nat := s.attempts * 6 + stageRank s.stage

/-- The invariant: a transient verdict is legal only at the decide point
    or the retry anchor (`.regen`/`.decide`) — it must never ride into
    the report. -/
def PipelineInv (s : PipelineState) : Prop :=
  match s.stage with
  | .dead => s.lastVerdict ≠ .transient
  | .load => s.lastVerdict ≠ .transient
  | .regen => True
  | .decide => True
  | .report => s.lastVerdict ≠ .transient
  | .done => s.lastVerdict ≠ .transient

-- The gates driver machine: load → regenerate → compare → report, with
-- the retry-on-transient edge back to regenerate.
-- (plain comment: doc comments cannot precede machine!)
machine! gateRun where
  State: PipelineState
  Inv: PipelineInv
  event: launch guard: (fun s => decide (s.stage = .dead))
    action: (fun s _ => { s with stage := .load })
    safety: (by
      intro s w hinv
      simp only [decide_eq_true_eq] at w
      unfold PipelineInv at hinv ⊢
      simp only [w] at hinv ⊢
      exact hinv)
  event: loadOk guard: (fun s => decide (s.stage = .load))
    action: (fun s _ => { s with stage := .regen })
    safety: (by
      intro s w hinv
      simp only [decide_eq_true_eq] at w
      unfold PipelineInv at hinv ⊢
      simp only [w] at hinv ⊢)
  event: regen (v : Verdict) guard: (fun s => decide (s.stage = .regen))
    action: (fun s _ => { s with attempts := s.attempts + 1, lastVerdict := v, stage := .decide })
    safety: (by
      intro s w hinv
      simp only [decide_eq_true_eq] at w
      unfold PipelineInv at hinv ⊢
      simp only [w] at hinv ⊢)
  event: retry guard: (fun s => decide (s.stage = .decide && s.lastVerdict = .transient))
    action: (fun s _ => { s with stage := .regen })
    safety: (by
      intro s w hinv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at w
      rcases w with ⟨wstage, _⟩
      unfold PipelineInv at hinv ⊢
      simp only [wstage] at hinv ⊢)
  event: compare guard: (fun s =>
      decide ((s.stage = .decide && s.lastVerdict ≠ .transient) && s.attempts ≥ 1))
    action: (fun s _ => { s with stage := .report })
    safety: (by
      intro s w hinv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at w
      -- w : (s.stage = .decide ∧ s.lastVerdict ≠ .transient) ∧ s.attempts ≥ 1
      -- (explicit parens pin the nesting; the attempt-count slot is a
      --  proof-typed conjunct — extract by projection, never by rcases)
      unfold PipelineInv at hinv ⊢
      simp only [w.1.1] at hinv ⊢
      exact w.1.2)
  event: report guard: (fun s =>
      decide ((s.stage = .report && s.lastVerdict ≠ .transient) && s.attempts ≥ 1))
    action: (fun s _ => { s with stage := .done })
    safety: (by
      intro s w hinv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at w
      unfold PipelineInv at hinv ⊢
      simp only [w.1.1] at hinv ⊢
      exact hinv)

/-! ## The step assertions (the happy path + the retry edge)

The driver's contract, as executable facts: the happy path and the retry
path run END TO END (definitional — the machine reduces), and the
ORDERING rejects (an out-of-order event is an observable `none`). These
are the "happy-path step assertions in the driver" the F3 scope calls
for; the label sequences they check are exactly the label sequences
`Gates.DriverMachine.runGate` issues. -/

/-- The happy path END TO END: launch → load → regenerate (in sync) →
    compare → report — accepted; the final state counts the attempt. -/
theorem happy_path_run :
    gateRun.run ⟨.dead, .inSync, 0⟩
        [.launch, .loadOk, .regen .inSync, .compare, .report]
      = some
          ( [(.launch, ⟨.load, .inSync, 0⟩), (.loadOk, ⟨.regen, .inSync, 0⟩)
          , (.regen .inSync, ⟨.decide, .inSync, 1⟩)
          , (.compare, ⟨.report, .inSync, 1⟩)
          , (.report, ⟨.done, .inSync, 1⟩) ]
          , ⟨.done, .inSync, 1⟩ ) :=
  rfl

/-- The retry cycle END TO END: a transient first regeneration rewinds
    via `retry`, a second regeneration (in sync) completes the run; the
    two regenerations count two attempts. -/
theorem retry_path_run :
    gateRun.run ⟨.dead, .inSync, 0⟩
        [.launch, .loadOk, .regen .transient, .retry, .regen .inSync, .compare, .report]
      = some
          ( [(.launch, ⟨.load, .inSync, 0⟩), (.loadOk, ⟨.regen, .inSync, 0⟩)
          , (.regen .transient, ⟨.decide, .transient, 1⟩)
          , (.retry, ⟨.regen, .transient, 1⟩)
          , (.regen .inSync, ⟨.decide, .inSync, 2⟩)
          , (.compare, ⟨.report, .inSync, 2⟩)
          , (.report, ⟨.done, .inSync, 2⟩) ]
          , ⟨.done, .inSync, 2⟩ ) :=
  rfl

/-- The stage ORDER is enforced: `compare` cannot fire from the raw regen
    stage (a verdict must be fed first — the driver feeds exactly one
    `.regen v` per regeneration). -/
theorem compare_without_verdict_rejected :
    gateRun.step? ⟨.regen, .inSync, 1⟩ .compare = none :=
  rfl

/-- The stage ORDER is enforced: `report` before any regeneration is
    REJECTED (the report stage's guard demands the attempt count). -/
theorem report_without_regen_rejected :
    gateRun.step? ⟨.dead, .inSync, 0⟩ .report = none :=
  rfl

/-- The retry edge only rewinds a TRANSIENT failure: an in-sync verdict
    at the decide point cannot retry (it must compare + report). -/
theorem retry_after_inSync_rejected :
    gateRun.step? ⟨.decide, .inSync, 1⟩ .retry = none :=
  rfl

/-- The retry edge FIRES: a transient verdict at the decide point rewinds
    to the regen stage, attempt count kept. -/
theorem retry_rewinds :
    gateRun.step? ⟨.decide, .transient, 2⟩ .retry = some ⟨.regen, .transient, 2⟩ :=
  rfl

/-- The happy path's recorded states (from `happy_path_run`). -/
def happyPathTrace : gateRun.Trace :=
  [ (.launch, ⟨.load, .inSync, 0⟩), (.loadOk, ⟨.regen, .inSync, 0⟩)
  , (.regen .inSync, ⟨.decide, .inSync, 1⟩)
  , (.compare, ⟨.report, .inSync, 1⟩)
  , (.report, ⟨.done, .inSync, 1⟩) ]

/-- The retry cycle's recorded states (from `retry_path_run`). -/
def retryPathTrace : gateRun.Trace :=
  [ (.launch, ⟨.load, .inSync, 0⟩), (.loadOk, ⟨.regen, .inSync, 0⟩)
  , (.regen .transient, ⟨.decide, .transient, 1⟩)
  , (.retry, ⟨.regen, .transient, 1⟩)
  , (.regen .inSync, ⟨.decide, .inSync, 2⟩)
  , (.compare, ⟨.report, .inSync, 2⟩)
  , (.report, ⟨.done, .inSync, 2⟩) ]

/-- `run_preserves` instantiated: an accepted happy-path run records only
    invariant-satisfying states — the machine's safety obligations,
    discharged at construction, applied to the concrete trace and final
    state of `happy_path_run`. -/
theorem happy_path_run_preserves :
    PipelineInv ⟨.done, .inSync, 1⟩ ∧ ∀ p ∈ happyPathTrace, PipelineInv p.2 := by
  exact gateRun.run_preserves ⟨.dead, .inSync, 0⟩ (by simp [PipelineInv])
    [.launch, .loadOk, .regen .inSync, .compare, .report]
    happyPathTrace
    ⟨.done, .inSync, 1⟩ happy_path_run

/-- `run_preserves` on the retry path: the rewound states satisfy the
    invariant too (a transient verdict never escapes the
    decide/regen anchor) — applied to the retry cycle's concrete trace. -/
theorem retry_path_run_preserves :
    PipelineInv ⟨.done, .inSync, 2⟩ ∧ ∀ p ∈ retryPathTrace, PipelineInv p.2 := by
  exact gateRun.run_preserves ⟨.dead, .inSync, 0⟩ (by simp [PipelineInv])
    [.launch, .loadOk, .regen .transient, .retry, .regen .inSync, .compare, .report]
    retryPathTrace
    ⟨.done, .inSync, 2⟩ retry_path_run

/-! ## The acyclicity rank (hand-written, under the machine!'s generated
    names)

The machine!'s `rank:` clause generates `rank_advances` with a proof that
case-splits `s` per STATE CONSTRUCTOR. The driver's `PipelineState` is a
STRUCTURE (stage field + attempt counter) — `cases s` splits into fields,
not stages, and `omega` cannot reason about `stageRank` of a variable. So
the rank pair is stated under the generated names and proved here by
case-splitting the LABEL + substituting the guard-determined stage; the
`step?`/`run`/`tr` surface the driver reuses is the generated one. -/

/-- Theorem (same statement the `rank:` clause would generate): every
    non-rewind event strictly increases `PipelineState.rank`; only
    `retry` (the rewind) may step backward. -/
theorem gateRun.rank_advances (s : PipelineState) (l : gateRun.Label)
    (hnr : l ≠ .retry) (w : (gateRun.event l).guard s = true) :
    PipelineState.rank s < PipelineState.rank ((gateRun.event l).action s w) := by
  cases l with
  | launch =>
      cases s with
      | mk stage v n =>
          simp [gateRun.spec, decide_eq_true_eq] at w
          subst stage
          simp [gateRun.spec, PipelineState.rank, stageRank]
          try omega
  | loadOk =>
      cases s with
      | mk stage v n =>
          simp [gateRun.spec, decide_eq_true_eq] at w
          subst stage
          simp [gateRun.spec, PipelineState.rank, stageRank]
          try omega
  | regen v' =>
      cases s with
      | mk stage v n =>
          simp [gateRun.spec, decide_eq_true_eq] at w
          subst stage
          simp [gateRun.spec, PipelineState.rank, stageRank]
          try omega
  | retry =>
      exfalso
      exact hnr rfl
  | compare =>
      cases s with
      | mk stage v n =>
          simp [gateRun.spec, Bool.and_eq_true, decide_eq_true_eq] at w
          have hst : stage = .decide := w.1.1
          subst stage
          simp [gateRun.spec, PipelineState.rank, stageRank]
          try omega
  | report =>
      cases s with
      | mk stage v n =>
          simp [gateRun.spec, Bool.and_eq_true, decide_eq_true_eq] at w
          have hst : stage = .report := w.1.1
          subst stage
          simp [gateRun.spec, PipelineState.rank, stageRank]
          try omega

/-- The same property over the two-state relation (the generated
    `X_rank_advances_tr` statement): a `tr` step off the rewind strictly
    increases the rank. -/
theorem gateRun.rank_advances_tr (s s' : PipelineState) (l : gateRun.Label)
    (htr : gateRun.tr s l s') (hnr : l ≠ .retry) :
    PipelineState.rank s < PipelineState.rank s' := by
  obtain ⟨w, hact⟩ := htr
  have h := gateRun.rank_advances s l hnr w
  rw [hact] at h
  exact h

/-! ## The driver: IO at the stages, the machine between them -/

/-- Cap on CONSECUTIVE transient regeneration failures: past this, the
    driver reports the gate failed instead of retrying forever (the
    machine's rewind edge is the mechanism; the cap is the driver's
    termination policy). -/
def maxAttempts : Nat := 3

/-- One machine step, or a driver failure if the label is rejected from
    `s` (an invalid order — a driver bug the machine catches). -/
def step (s : PipelineState) (l : gateRun.Label) : IO PipelineState :=
  match gateRun.step? s l with
  | some s' => pure s'
  | none => throw (IO.userError s!"gate-run: step rejected from stage {repr s.stage}")

/-- Classify the regeneration against the committed baseline at `base.path`
    (absent/directory = the `absent` verdict — a vanished baseline fails).
    The retry-on-transient classification is the DRIVER's: a regeneration
    that throws (a transient IO failure) is `.transient`, found in
    `runGate`'s tryCatch, not here. -/
def classify (b : TestKit.Baseline) (fresh : String) : IO Verdict := do
  unless ← b.path.pathExists do return .absent
  if ← b.path.isDir then return .absent
  let committed ← IO.FS.readFile b.path
  if b.compare committed fresh then pure .inSync else pure .drifted

/-- Drive one gate's Baseline through the machine. `regenerate` is called
    at the regen stage; a thrown regeneration is `.transient` and REWINDS
    (the retry edge) up to `maxAttempts` consecutive failures. The
    regenerated report echoes at the report stage (the gate's log); the
    run's row + count line are the C5 "run → verdict → count" shape.
    Exit 0 iff the final verdict is `.inSync`. -/
unsafe def runGate (b : TestKit.Baseline) : IO UInt32 := do
  -- (1) load: the preamble (env init, package selection — the driver's
  --     concern; the machine records only the stage move).
  let s ← step ⟨.dead, .inSync, 0⟩ .launch
  let mut s ← step s .loadOk
  -- (2) regenerate, with the retry-on-transient edge back to regen
  let mut fresh : String := ""
  let mut verdict : Verdict := .absent
  let mut transient : Nat := 0
  while s.stage = .regen do
    -- a THROWN regeneration is the machine's transient classification:
    -- the driver recovers it here and rewinds via the retry edge
    let out ← EIO.tryCatch
      (do let t ← b.regenerate; pure (some t))
      (fun _ : IO.Error => pure none)
    match out with
    | none =>
        -- transient regeneration: feed the verdict, rewind, and try again
        s ← step s (.regen .transient)
        s ← step s .retry
        transient := transient + 1
        if transient > maxAttempts then
          IO.eprintln s!"{b.name}: regeneration failed {transient} times consecutively \
            (transient) — giving up (the machine rewound {transient} time(s))"
          return 1
    | some txt =>
        fresh := txt
        -- (3) compare: classify against the committed baseline
        verdict ← classify b txt
        s ← step s (.regen verdict)
  s ← step s .compare
  -- (4) report: the gate's log, the run's row, and the count
  s ← step s .report
  if !fresh.isEmpty then IO.println fresh
  let ok := match verdict with | .inSync => true | _ => false
  let detail := match verdict with
    | .inSync => "in sync"
    | .drifted => s!"DIFFERS from {b.path}"
    | .absent => s!"baseline absent at {b.path}"
    | .transient => s!"gave up after {maxAttempts} consecutive transient regeneration failures"
  IO.println (TestKit.verdictLine b ok detail)
  IO.println s!"{b.name}: 1 baseline(s) run, {if ok then 0 else 1} failed"
  return if ok then 0 else 1

end Gates.DriverMachine

end -- @[expose] public section

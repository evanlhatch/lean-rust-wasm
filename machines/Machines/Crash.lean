/- 
# Machines.Crash — the crash/recovery refinement: first-class crash steps + persistent/volatile separation

Owned by: the crash/recovery refinement lane (the mandate tree, `machines/`).
Driving decisions: notes/v3/decisions.md D13 (the review-10C content:
"crash/recovery refinement (first-class crash steps + persistent/volatile
separation)" — the MODEL face; the delta log's crash-recovery suite is
the RUNTIME face, a different artifact) + notes/v3/01-core.md §3 (the
TraceModel discipline: the transition semantics is AUTHORITATIVE — every
crashy claim ties back to a landed `Machine.step?` by definition, never
a parallel encoding) + notes/v3/04-verification.md §4 (the observer
parameter: "the observable behavior is preserved" names its observer,
as data).

## The discipline (what lands, honestly)

- `CrashMachine V P I` — the machine whose state separates into the
  PERSISTENT component `P` (survives a crash — it is the disk) and the
  VOLATILE component `V` (dies in a crash — it is the cache). The
  separation is IN THE TYPE: a state is a pair, and the crash step's
  codomain is `P` ALONE — after a crash there is no volatile component
  to speak of, not a zeroed one.
- `crashStep` — THE CRASH STEP as a first-class transition: from the
  paired state, the volatile is DROPPED (projected away, unrepresentable
  in the down state's type) and the persistent SURVIVES. What a crash
  cannot do is depend on the volatile's value: two different caches over
  the same disk crash to the same remnant (pinned as a law).
- `CrashMachine.up` — THE RECOVERY TRANSITION as a first-class
  transition: from the persistent ALONE, the machine's recovery
  discipline (`recover : P → V`) reconstructs the honest resumed state.
- `CrashMachine.closure` — the crash+recovery closure: the composite
  `up ∘ crashStep`. FAITHFULNESS is the statement that the closure is
  the identity — the recovery reconstructed exactly the volatile that
  died (`FaithfulAt`).

## The refinement (the honest statement)

The crashy machine and the crash-free machine live on the SAME paired
state space, over the label type `Sum I Unit` — `inl i` is the honest
step, `inr ()` is the crash event. The crash-free machine answers a
crash event with the STUTTER (a world where crashes do not occur: the
event is a no-op, and a no-op is a fired self-loop, not a silent
refusal — Basic's refusal-is-data discipline stays intact because a
crash event is not a disabled input, it is an input that does nothing).
The crashy machine answers it with the closure.

THE REFINEMENT: on the FAITHFUL FRAGMENT (the states where the recovery
discipline reconstructs the honest volatile, closed under the honest
step), the crashy machine refines the crash-free machine AND the
crash-free machine refines the crashy machine — both riding the landed
`Coalg.Refines` through the SAME observer — so the observed behavior
streams are EQUAL: the observable behavior is preserved under the
crash+recovery closure WHEN the recovery is faithful. The
observer-parameterized form is 04 §4's discipline; the two `Refines`
instances compose into an equivalence, proved once, consumed by the
worked example.

## The worked example (the event-sourcing discipline)

The journal-backed machine: the volatile cache is the state value, the
persistent journal is the delta list; the honest step appends the delta
to the journal AND updates the cache; the recovery discipline REPLAYS
the journal (`replayJ` — the integrate face of the landed additive
structure). The faithful fragment is the event-sourcing invariant "the
cache IS the journal's replay" — proved closed under the honest steps,
so the refinement instantiates with the journal machine. The recovery
IS the journal's replay: a crash + the recovery returns the machine to
exactly where it was.

The SABOTAGE control (MachinesTests.Crash): a LOSSY persistence — a
step that updates the cache but journals a zero — breaks faithfulness,
and the crash+recovery closure REWINDS the state: the behaviors diverge.
The teeth are real: the refinement's premise is load-bearing.

## The five questions

- **Root**: TraceModel (01-core §3) — the behavior side: crash steps
  and recovery are TRANSITIONS (first-class, tied to the authoritative
  `step?` by definition), the refinement is the derived view riding the
  landed `Coalg.Refines` + `Kit.Observer`. No new root (10C: "fits the
  behavior/refinement foundation").
- **Carrier grade**: pattern #1 at the machine level (the crashy/free
  machines ARE `Machine`s over the landed carrier — their `step?` is
  data, the honest step is shared definitionally); the refinement rides
  the ONE relation family (`Kit.Rel`) through `Coalg.Refines`.
- **Spine reading**: none — a substrate module; journals, outboxes,
  checkpoints, exactly-once claims instantiate it.
- **Ladder rung**: hand theorems at the structure (rung 6 — the
  refinement's step obligation is one case split per label; the
  behavior-stream equality is the two `beh_le` inclusions glued
  pointwise); the value faces land as rung-3 decides in the tests.
- **Gate rows**: the axiom pins in MachinesTests.Crash (the core-triple
  surface over the refinement laws + the faithfulness closure).

## Named exclusions

- NO nondeterministic crash placement inside a step (a crash DURING an
  operation — the torn-write model: the persistent catches SOME prefix
  of the step's writes) — the honest minimal crashes BETWEEN steps
  (the crash event is a label); the torn-write discipline lands with
  its first storage consumer.
- NO crash-without-recovery semantics (a machine stuck DOWN — the down
  state is not itself a machine state here; the crashed-and-stayed-down
  behavior needs a `V ⊕ P` state space) — lands with its first
  availability consumer.
- NO distributed/multi-node recovery (replication, consensus) — D13's
  data corrections name them separately; not this slice.

Core-only: no mathlib, no Batteries (the cone rule).
-/
module

public import Machines.Coalg
public import Machines.Fusion
public import Kit.Observer
@[expose] public section


namespace Machines

/-! ## The crash step (first-class) -/

variable {V P : Type}

/-- THE CRASH STEP (first-class; D13's 10C): the volatile state RESETS
    — dropped, unrepresentable in the down state's type `P` — and the
    persistent survives. The crash cannot peek at the volatile: the law
    below pins that two different volatiles over the same persistent
    crash to the SAME remnant. -/
def crashStep (vp : V × P) : P := vp.2

/-- THE CRASH DROPS THE VOLATILE (the law): the remnant depends only on
    the persistent — the volatile's value is gone. -/
theorem crashStep_congr {V P : Type} (v₁ v₂ : V) (p : P) :
    crashStep (V := V) (P := P) (v₁, p) = crashStep (v₂, p) := rfl

/-- THE PERSISTENT SURVIVES (the law): the remnant IS the persistent. -/
theorem crashStep_survives {V P : Type} (v : V) (p : P) :
    crashStep (v, p) = p := rfl

/-! ## The crashy machine -/

/-- A machine WITH the crash discipline: the state separates into the
    volatile `V` (dies) and the persistent `P` (survives); the honest
    step moves both; the recovery discipline `recover` reconstructs the
    volatile from the persistent ALONE — that reconstruction is the
    machine's whole honesty about crashes. -/
structure CrashMachine (V P I : Type) where
  /-- The honest step: consumes the paired state, produces the paired
      state (both components may move — the write discipline is the
      step's own business). -/
  step? : V → P → I → Option (V × P)
  /-- THE RECOVERY DISCIPLINE: from the persistent alone, the honest
      resumed volatile. -/
  recover : P → V

namespace CrashMachine

variable {V P I : Type}

/-- THE RECOVERY TRANSITION (first-class): from the persistent alone,
    the discipline reconstructs the honest resumed state — the volatile
    is REBUILT (never remembered: there is no `V` input to remember
    from), the persistent is untouched. -/
def up (m : CrashMachine V P I) (p : P) : V × P := (m.recover p, p)

/-- THE CRASH+RECOVERY CLOSURE: the composite first-class transition —
    a crash (volatile dropped, persistent survives) immediately followed
    by the recovery (the state reconstructed from what survived). -/
def closure (m : CrashMachine V P I) (vp : V × P) : V × P := m.up (crashStep vp)

/-- FAITHFULNESS at a state: the closure is the identity there — the
    recovery reconstructed exactly the volatile that died. This is the
    premise the refinement consumes. -/
abbrev FaithfulAt (m : CrashMachine V P I) (vp : V × P) : Prop :=
  m.recover vp.2 = vp.1

/-- THE FAITHFULNESS LAW: at a faithful state, the crash+recovery
    closure IS the identity — the crash is invisible in the state. -/
theorem closure_of_faithful (m : CrashMachine V P I) (vp : V × P)
    (h : m.FaithfulAt vp) : m.closure vp = vp := by
  obtain ⟨v, p⟩ := vp
  show m.up (v, p).2 = (v, p)
  show (m.recover (v, p).2, (v, p).2) = (v, p)
  rw [h]

/-! ### The two machines over the crash-extended labels -/

/-- THE CRASHY MACHINE: the honest step on the paired state, plus the
    crash event as a FIRST-CLASS label — its step is the crash+recovery
    closure (the machine crashes and restarts in one atomic event; the
    stayed-down semantics is a named exclusion above). -/
def crashy (m : CrashMachine V P I) : Machine (V × P) (Sum I Unit) :=
  ⟨fun vp l => match l with
    | .inl i => m.step? vp.1 vp.2 i
    | .inr _ => some (m.closure vp)⟩

/-- THE CRASH-FREE MACHINE: the SAME honest step; the crash event is
    the STUTTER — a no-op fired as a self-loop (a world without crashes
    is not a world that refuses its inputs; the refusal-is-data
    discipline is about disabled inputs, and a crash event in a
    crash-free world is not disabled, it is nothing). -/
def free (m : CrashMachine V P I) : Machine (V × P) (Sum I Unit) :=
  ⟨fun vp l => match l with
    | .inl i => m.step? vp.1 vp.2 i
    | .inr _ => some vp⟩

/-! ### The faithful fragment -/

/-- THE FAITHFUL FRAGMENT: the paired states where the recovery
    discipline reconstructs the honest volatile (`faithful`), CLOSED
    under the honest step (`step_preserves` — the persistence
    discipline: a step that journaled less than it cached leaves the
    fragment). The refinement is stated ON the fragment — the honest
    premise, never a hidden assumption. -/
structure Faithful (m : CrashMachine V P I) (F : V × P → Prop) : Prop where
  /-- The fragment's states are faithful: recovery reconstructs. -/
  faithful : ∀ vp, F vp → m.FaithfulAt vp
  /-- The honest step preserves the fragment (the write discipline's
      obligation — the journal keeps up with the cache). -/
  step_preserves : ∀ (vp : V × P) (i : I) (v' : V) (p' : P),
      F vp → m.step? vp.1 vp.2 i = some (v', p') → F (v', p')

/-! ### The refinement (both directions, riding Coalg.Refines) -/

variable {O : Type}

/-- The crashy coalgebra under the named observer (04 §4). -/
def crashyCoalg (m : CrashMachine V P I) (o : Kit.Observer (V × P) O) :
    Coalgebra (V × P) (Sum I Unit) O := ⟨m.crashy, o⟩

/-- The crash-free coalgebra under the named observer. -/
def freeCoalg (m : CrashMachine V P I) (o : Kit.Observer (V × P) O) :
    Coalgebra (V × P) (Sum I Unit) O := ⟨m.free, o⟩

/- The observe faces (all `rfl` — the coalgebra map is tied to the
   machines' `step?` by definition, no parallel encoding). -/
theorem observe_crashy_inl (m : CrashMachine V P I) (o : Kit.Observer (V × P) O)
    (v : V) (p : P) (i : I) :
    (m.crashyCoalg o).observe (v, p) (Sum.inl i)
      = (m.step? v p i).map (fun vp' => (o.see vp', vp')) := rfl

theorem observe_crashy_inr (m : CrashMachine V P I) (o : Kit.Observer (V × P) O)
    (vp : V × P) :
    (m.crashyCoalg o).observe vp (Sum.inr ())
      = some (o.see (m.closure vp), m.closure vp) := rfl

theorem observe_free_inl (m : CrashMachine V P I) (o : Kit.Observer (V × P) O)
    (v : V) (p : P) (i : I) :
    (m.freeCoalg o).observe (v, p) (Sum.inl i)
      = (m.step? v p i).map (fun vp' => (o.see vp', vp')) := rfl

theorem observe_free_inr (m : CrashMachine V P I) (o : Kit.Observer (V × P) O)
    (vp : V × P) :
    (m.freeCoalg o).observe vp (Sum.inr ()) = some (o.see vp, vp) := rfl

/-- THE STEP-OBLIGATION BUILDER (the refinement's shared assembly,
    honest-label face): the two coalgebras' `inl` faces are the SAME
    honest step (the observe ties supplied as `hA`/`hB`), so the
    stepwise obligation is proved ONCE — crashy↔free agnostic. -/
theorem step_oblig (m : CrashMachine V P I) (F : V × P → Prop)
    (hF : m.Faithful F) (o : Kit.Observer (V × P) O)
    {c₁ c₂ : Coalgebra (V × P) (Sum I Unit) O}
    (hA : ∀ (vp : V × P) (i : I), c₁.observe vp (Sum.inl i)
      = (m.step? vp.1 vp.2 i).map (fun vp' => (o.see vp', vp')))
    (hB : ∀ (vp : V × P) (i : I), c₂.observe vp (Sum.inl i)
      = (m.step? vp.1 vp.2 i).map (fun vp' => (o.see vp', vp')))
    (s₁ : V × P) (hFvp : F s₁) (i : I) :
    (c₁.observe s₁ (Sum.inl i) = none
      ∧ ∀ (o₂ : O) (s₂' : V × P), c₂.observe s₁ (Sum.inl i) = some (o₂, s₂') →
          s₁ = s₂' ∧ F s₁)
    ∨ ∃ (ob : O) (s₁' s₂' : V × P),
        c₁.observe s₁ (Sum.inl i) = some (ob, s₁')
        ∧ c₂.observe s₁ (Sum.inl i) = some (ob, s₂')
        ∧ s₁' = s₂' ∧ F s₁' := by
  cases hs : m.step? s₁.1 s₁.2 i with
  | none =>
      refine Or.inl ⟨?_, ?_⟩
      · rw [hA s₁ i, hs]; rfl
      · intro o₂ s₂' hspec
        rw [hB s₁ i, hs] at hspec
        simp at hspec
  | some vp' =>
      obtain ⟨v', p'⟩ := vp'
      refine Or.inr ⟨o.see (v', p'), (v', p'), (v', p'), ?_, ?_, ?_⟩
      · rw [hA s₁ i, hs]; rfl
      · rw [hB s₁ i, hs]; rfl
      · exact ⟨rfl, hF.step_preserves _ i v' p' hFvp hs⟩

/-- THE CRASH-OBLIGATION BUILDER (the shared assembly's crash face):
    one side fires the closure, the other the stutter, and faithfulness
    makes them the SAME observation — one `Or.inr` payload serves both
    directions (the witnesses supplied as `w₁`/`w₂`). -/
theorem crash_oblig (m : CrashMachine V P I) (F : V × P → Prop)
    (hF : m.Faithful F) (o : Kit.Observer (V × P) O)
    {c₁ c₂ : Coalgebra (V × P) (Sum I Unit) O}
    (s₁ : V × P) (hFvp : F s₁) (w₁ w₂ : V × P)
    (hweq : w₁ = w₂) (hFw : F w₂)
    (h₁ : c₁.observe s₁ (Sum.inr ()) = some (o.see w₁, w₁))
    (h₂ : c₂.observe s₁ (Sum.inr ()) = some (o.see w₂, w₂)) :
    ∃ (ob : O) (s₁' s₂' : V × P),
        c₁.observe s₁ (Sum.inr ()) = some (ob, s₁')
        ∧ c₂.observe s₁ (Sum.inr ()) = some (ob, s₂')
        ∧ s₁' = s₂' ∧ F s₁' := by
  rw [← hweq] at h₂ hFw
  exact ⟨o.see w₁, w₁, w₁, h₁, h₂, rfl, hFw⟩

/-- THE REFINEMENT, crashy ≤ free (the crash/recovery refinement's
    impl ≤ spec face, riding the landed `Coalg.Refines`): ON THE
    FAITHFUL FRAGMENT, every observation the crashy machine makes, the
    crash-free machine makes — through the relation "the same faithful
    state". The crash event is the load-bearing case: the crashy
    machine's closure step observes as the stutter (faithfulness makes
    the closure the identity), so the crash is invisible in the
    observation. -/
theorem refines_crashy (m : CrashMachine V P I) (F : V × P → Prop)
    (hF : m.Faithful F) (o : Kit.Observer (V × P) O) :
    Refines (m.crashyCoalg o) (m.freeCoalg o) (fun a b => a = b ∧ F a) := by
  refine ⟨?_⟩
  intro s₁ s₂ h l
  obtain ⟨heq, hFvp⟩ := h
  subst heq
  cases l with
  | inl i =>
      exact m.step_oblig F hF o
        (fun vp i => observe_crashy_inl m o vp.1 vp.2 i)
        (fun vp i => observe_free_inl m o vp.1 vp.2 i) s₁ hFvp i
  | inr _ =>
      exact Or.inr (m.crash_oblig F hF o s₁ hFvp (m.closure s₁) s₁
        (m.closure_of_faithful _ (hF.faithful _ hFvp)) hFvp
        (observe_crashy_inr m o s₁) (observe_free_inr m o s₁))

/-- THE REFINEMENT, free ≤ crashy (the reverse face): on the faithful
    fragment the inclusion runs BOTH ways — the crash-free machine
    never out-observes the crashy one either. The two instances together
    are the honest "≡" of the crash/recovery refinement: the observable
    behavior is PRESERVED (equality, not just inclusion), when the
    recovery is faithful. -/
theorem refines_free_crashy (m : CrashMachine V P I) (F : V × P → Prop)
    (hF : m.Faithful F) (o : Kit.Observer (V × P) O) :
    Refines (m.freeCoalg o) (m.crashyCoalg o) (fun a b => a = b ∧ F a) := by
  refine ⟨?_⟩
  intro s₁ s₂ h l
  obtain ⟨heq, hFvp⟩ := h
  subst heq
  cases l with
  | inl i =>
      exact m.step_oblig F hF o
        (fun vp i => observe_free_inl m o vp.1 vp.2 i)
        (fun vp i => observe_crashy_inl m o vp.1 vp.2 i) s₁ hFvp i
  | inr _ =>
      have hc := m.closure_of_faithful _ (hF.faithful _ hFvp)
      exact Or.inr (m.crash_oblig F hF o s₁ hFvp s₁ (m.closure s₁) hc.symm
        (by rw [hc]; exact hFvp)
        (observe_free_inr m o s₁) (observe_crashy_inr m o s₁))

/-- THE BEHAVIOR PRESERVATION (the refinement's payoff, at stream
    level): from a faithful state, the crashy machine's observed
    behavior stream EQUALS the crash-free machine's — on EVERY input
    stream, crashes included. The two `Refines` instances glue
    pointwise: an observation is `some` on one side iff `some` with the
    same value on the other. This is the honest "the observable
    behavior is preserved when the recovery is faithful". -/
theorem beh_eq_faithful (m : CrashMachine V P I) (F : V × P → Prop)
    (hF : m.Faithful F) (o : Kit.Observer (V × P) O)
    (vp : V × P) (hvp : F vp) (ins : Stream (Sum I Unit)) :
    (m.crashyCoalg o).beh ins vp = (m.freeCoalg o).beh ins vp := by
  have h₁ := m.refines_crashy F hF o
  have h₂ := m.refines_free_crashy F hF o
  funext t
  rcases h : (m.crashyCoalg o).beh ins vp t with _ | ob
  · cases hf : (m.freeCoalg o).beh ins vp t with
    | none => rfl
    | some ob' =>
        exact absurd (h₂.beh_le_at vp vp ins ⟨rfl, hvp⟩ t ob' hf)
          (by rw [h]; simp)
  · rw [h₁.beh_le_at vp vp ins ⟨rfl, hvp⟩ t ob h]

end CrashMachine

/-! ## The worked example: the journal-backed machine (event sourcing) -/

namespace Crash.Journal

/- The event-sourcing discipline: the volatile cache is the state
value, the persistent journal is the DELTA list (the landed additive
structure's entries — `Kit.intAdd.compose` is the integration's
operation); the honest step appends the delta to the journal AND
updates the cache; the recovery discipline REPLAYS the journal. A crash
+ the recovery = the journal's replay. -/

/-- An input: journal the +1 delta, or journal the −1 delta. -/
inductive JInput where
  | inc | dec
deriving DecidableEq, Repr, BEq

open JInput

/-- THE REPLAY: integrate the journal — the recovery discipline. The
    additive structure is the landed `Kit.intAdd` (the group rung:
    deltas compose, cancel, commute). -/
def replayJ (j : List Int) : Int := j.foldl Kit.intAdd.compose 0

/-- The compose-unfolding simp lemma (the intAdd face — `compose` IS
    addition, definitionally). -/
@[simp] theorem compose_add (a b : Int) : Kit.intAdd.compose a b = a + b := rfl

/-- The replay's append law: integrating one more delta extends the
    integral — the induction the step preservation needs. -/
theorem replayJ_append (j : List Int) (d : Int) :
    replayJ (j ++ [d]) = replayJ j + d := by
  simp only [replayJ, List.foldl_append, List.foldl_cons, List.foldl_nil, compose_add]

/-- THE JOURNAL-BACKED MACHINE: the honest step journals the delta and
    updates the cache (the write-through discipline, in the type); the
    recovery IS the replay. -/
def jmach : CrashMachine Int (List Int) JInput :=
  ⟨fun v j i => match i with
    | .inc => some (v + 1, j ++ [1])
    | .dec => some (v - 1, j ++ [-1]),
   replayJ⟩

/-- THE EVENT-SOURCING INVARIANT (the faithful fragment): the cache IS
    the journal's replay. -/
def journalF : Int × List Int → Prop := fun vp => vp.1 = replayJ vp.2

/-- THE FRAGMENT IS FAITHFUL: the invariant says recovery reconstructs
    (definitional — the recovery IS the replay), and the honest step
    preserves it (the append law: journaling the delta keeps the replay
    exactly one delta ahead of the replayed past). -/
theorem journal_faithful : jmach.Faithful journalF := by
  refine ⟨?_, ?_⟩
  · intro vp hvp
    show jmach.recover vp.2 = vp.1
    rw [hvp]
    rfl
  · intro vp i v' p' hvp hstep
    cases i with
    | inc =>
        have hinj : vp.1 + 1 = v' ∧ vp.2 ++ [1] = p' := by
          simpa [jmach, CrashMachine.step?] using hstep
        show (v', p').1 = replayJ (v', p').2
        rw [← hinj.1, ← hinj.2, replayJ_append, hvp]
    | dec =>
        have hinj : vp.1 - 1 = v' ∧ vp.2 ++ [-1] = p' := by
          simpa [jmach, CrashMachine.step?] using hstep
        show (v', p').1 = replayJ (v', p').2
        rw [← hinj.1, ← hinj.2, replayJ_append, hvp]
        rfl

/-- The observer: sees the cache (the volatile's observable face). -/
def cacheObs : Kit.Observer (Int × List Int) Int := ⟨fun vp => vp.1⟩

/-- THE JOURNAL MACHINE'S REFINEMENT, crashy ≤ free — the generic
    theorem instantiated on the faithful event-sourcing fragment. -/
theorem refines_journal :
    Refines (jmach.crashyCoalg cacheObs) (jmach.freeCoalg cacheObs)
      (fun a b => a = b ∧ journalF a) :=
  jmach.refines_crashy journalF journal_faithful cacheObs

/-- THE JOURNAL MACHINE'S REFINEMENT, free ≤ crashy — the reverse
    face: the observable behavior is preserved BOTH ways. -/
theorem refines_journal_reverse :
    Refines (jmach.freeCoalg cacheObs) (jmach.crashyCoalg cacheObs)
      (fun a b => a = b ∧ journalF a) :=
  jmach.refines_free_crashy journalF journal_faithful cacheObs

/-- THE RECOVERY IS THE REPLAY (the worked example's payoff, at stream
    level): from a state satisfying the event-sourcing invariant, the
    journal machine's observed behavior is THE SAME with or without
    crashes interleaved — the crash + the recovery = the journal's
    replay = exactly where the machine was. -/
theorem beh_eq_journal (vp : Int × List Int) (hvp : journalF vp)
    (ins : Stream (Sum JInput Unit)) :
    (jmach.crashyCoalg cacheObs).beh ins vp
      = (jmach.freeCoalg cacheObs).beh ins vp :=
  jmach.beh_eq_faithful journalF journal_faithful cacheObs vp hvp ins

end Crash.Journal

end Machines

end -- public section

/-
# Machines.Trace — the execution views: witnesses, projection, observers

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/01-core.md §3 (the transition semantics is
AUTHORITATIVE; the trace/observation views are DERIVED — every derived
claim here is a THEOREM tying it back to `Machine.run`/`Machine.step`,
never an independent encoding) + notes/v3/04-verification.md §4 (the
observer parameter — "same behavior" is meaningless without naming the
observer; every equivalence claim here carries one, as data).

## What lands

- `Exec` — the execution as an INDUCTIVE, from a start state: each
  step carries its input, its post-state, and its step-relation
  WITNESS. The witness-carrying is honest because the witnesses are
  constructor data, not recoverable Props.
- The projections: `tape` (the input sequence) and `record` (the
  (input, post-state) audit trail). Both are tied to `Machine.run` by
  theorems (`exec_run`, `run_exec`) — the derived views cannot drift
  from the authoritative semantics.
- The observer composition: an `Kit.Observer` over step records lifts
  to an observer over EXECUTIONS (`execObs`), and execution
  equivalence rides `Kit.Observer.equiv` directly — its proved laws
  (refl/symm/trans, Kit.Observer's equivalence-theorem block) are
  CITED, not re-proved: `Exec.equivUnder_*`.
- The bridge to `Kit.Execution` (the minimal shape the standard
  observers consume): `toExecution` — record as trace, no terminal
  event (this slice's machines have no return vocabulary; `result` is
  honestly `none`), cost = the record length.
- THE GRADUATION (16-surface §5.1, 15-patterns #11): the run tie's
  cons law + the tie lemmas assemble `execRetraction` and **`execIso`**
  — `Exec` ≅ the runnable tapes as a TRUE `Kit.Iso` (both round trips:
  `run_exec_exec_run`, `tape_run_exec`).

## The five questions

- **Root**: TraceModel (01-core §3) — the DERIVED VIEWS block: the
  sequential execution set, the observation function, the equivalence
  under a named observer. Bisimulation/refinement between machines is
  NOT here — it lands with its first consumer (leftover rule).
- **Carrier grade**: pattern #1 at the view level — every projection
  is data + a proved tie back to `run`/`step`.
- **Spine reading**: none — a substrate module.
- **Ladder rung**: hand theorems at the structure (rung 6 with the
  written reason: these are relational content over inductive
  witnesses, not decidable ground facts); the observer laws are CITED
  rung-6 theorems from Kit.Observer (the dual-reading tie, pattern #6).
- **Gate rows**: the axiom report pins in MachinesTests.Axioms.

## Named exclusions

- NO bisimulation, NO stutter-invariance/observation-hiding — 01-core
  §3 names them per-claim choices; they land with the first claim that
  needs them. The per-execution causal poset (the DAG view) likewise
  waits for the concurrency consumer.
- NO fairness machinery, NO POR, NO vector clocks (08 §10's guard).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Basic
import Kit.Observer
import Kit.Correspondence

namespace Machines

/-! ## The execution, witness-carrying -/

/-- An execution of `m` starting at `s`, indexed by its final state.
    Every step carries the input, the post-state, and the step-relation
    witness — as constructor data. The `here` constructor is the empty
    execution (the trivial loop state); `step` prepends one witnessed
    transition. -/
inductive Exec (m : Machine S I) : S → S → Type where
  | here : Exec m s s
  | step : (i : I) → {s : S} → {fin : S} → (s' : S) → m.step s i s' →
      Exec m s' fin → Exec m s fin

namespace Exec

variable {m : Machine S I} {s fin : S}

/-- The input tape the execution consumes — the derived tape view. -/
def tape : {s fin : S} → Exec m s fin → List I
  | _, _, .here => []
  | _, _, .step i _ _ r => i :: r.tape

/-- The audit record: one (input, post-state) pair per step — what an
    audit-grade observer consumes. -/
def record : {s fin : S} → Exec m s fin → List (I × S)
  | _, _, .here => []
  | _, _, .step i s' _ r => (i, s') :: r.record

/-- THE TAPE TIE: the projections agree with the authoritative fold —
    running the execution's tape from its start state lands exactly on
    the execution's final state, with the witnesses along the way. -/
theorem exec_run (e : Exec m s fin) : m.run s e.tape = some fin := by
  induction e with
  | here => simp only [tape]; rfl
  | step i s' h r ih =>
      simp only [tape]
      rw [m.run_cons]
      simp only [Machine.step] at h
      rw [h, Option.bind_some, ih]

/- The cons branch's two helpers. The run-proof's decomposition must
    route through the option-recursion on `m.step? start i` (the
    extraction of the first post-state is a large elimination); the
    helpers keep the run/step defeq-link (`m.run_cons` is rfl) INSIDE
    their own proofs, so the branches' bodies are link-free and the
    equation lemma `run_exec.eq_2` supports rewriting (the graduation's
    cons law consumes it via `split`, which handles the dependent
    generalization the raw rewrite motive cannot). -/

/-- A disabled first step contradicts a successful run. -/
theorem run_none_absurd {m : Machine S I} {s : S} {i : I} {t : List I} {fin : S}
    (hH : m.step? s i = none) (h : m.run s (i :: t) = some fin) : False := by
  rw [m.run_cons, hH, Option.bind_none] at h
  simp at h

/-- A witnessed first step hands the run's tail to the post-state. -/
theorem run_some_inv {m : Machine S I} {s : S} {i : I} {t : List I} {fin s₀ : S}
    (hH : m.step? s i = some s₀) (h : m.run s (i :: t) = some fin) :
    m.run s₀ t = some fin := by
  rw [m.run_cons, hH, Option.bind_some] at h
  exact h

/-- THE RUN TIE (the converse): every successful run has a witnessing
    execution. Together with `exec_run`: executions = successful runs,
    the derived view recovered in both directions. (A def, not a
    theorem: the witness is Type-valued data.) -/
def run_exec (m : Machine S I) (start : S) :
    {t : List I} → {fin : S} → m.run start t = some fin → Exec m start fin
  | [], fin, h => by
      rw [m.run_nil] at h
      rw [Option.some.inj h]
      exact .here
  | i :: t, fin, h =>
      match hH : m.step? start i with
      | none => False.elim (run_none_absurd hH h)
      | some s₀ => Exec.step i s₀ hH (run_exec m s₀ (run_some_inv hH h))

/-- The run tie's NIL law, over the final state as given (`run_nil`
    pins `fin = start`). -/
theorem run_exec_nil {m : Machine S I} {s : S} (h : m.run s [] = some s) :
    run_exec m s h = .here := by rfl

/-- THE RUN TIE'S CONS LAW: over a cons-tape whose first step is the
    witnessed `s —i→ s₀`, `run_exec` is the witnessed step over the
    tail's `run_exec` (the witnesses are proof-irrelevant, the post-
    state determined by `step?`'s functionality). -/
theorem run_exec_cons {m : Machine S I} {s fin s₀ : S} {i : I} {t : List I}
    (hs₀ : m.step? s i = some s₀) (h : m.run s₀ t = some fin)
    (P : m.run s (i :: t) = some fin) :
    run_exec m s P
      = Exec.step (i := i) (s := s) (fin := fin) (s' := s₀) hs₀ (run_exec m s₀ h) := by
  rw [run_exec.eq_2 m s fin i t P]
  split
  · rename_i hH
    exact (run_none_absurd hH P).elim
  · rename_i o hH
    have hoe : s₀ = o := Option.some.inj (hs₀.symm.trans hH)
    subst hoe
    rfl

/-- The tape projection of `run_exec`'s witness is the tape itself —
    the successful run determines its execution's tape. -/
theorem tape_run_exec (m : Machine S I) (start : S) (t : List I) (fin : S)
    (h : m.run start t = some fin) : (run_exec m start h).tape = t := by
  revert h
  induction t generalizing start with
  | nil =>
      intro h
      have hst : start = fin := Option.some.inj (by rw [m.run_nil] at h; exact h)
      subst hst
      rw [run_exec_nil h]
      rfl
  | cons i t ih =>
      intro h
      rw [m.run_cons] at h
      obtain ⟨s₀, hs₀, hr⟩ := Option.bind_eq_some_iff.mp h
      rw [run_exec_cons hs₀ hr h]
      simp only [tape]
      rw [ih s₀ hr]

/-- THE ROUND TRIP (the run tie closes): `run_exec` over an execution's
    own `exec_run` witness recovers the execution — the witnesses are
    constructor data, the lookups determined by `step?`'s
    functionality. -/
theorem run_exec_exec_run {m : Machine S I} {s fin : S} (e : Exec m s fin) :
    run_exec m s (exec_run e) = e := by
  induction e with
  | here => exact run_exec_nil _
  | step i s₀ hw r ih =>
      have Pe : m.run _ (i :: r.tape) = some _ :=
        exec_run (Exec.step (i := i) s₀ hw r)
      show run_exec m _ Pe = _
      rw [run_exec_cons (hw : m.step? _ i = some s₀) (exec_run r) Pe, ih]

/-- Executions refine the reachable view. -/
theorem exec_reachable (e : Exec m s fin) : m.Reachable s fin := by
  induction e with
  | here => exact .here
  | step i s' h r ih =>
      simp only [Machine.step] at h
      exact Machine.Reachable.trans (.step i h .here) ih

/-! ## The observer composition (04 §4: the observer is a parameter) -/

/-- Lifting an observer over step records to an observer over
    executions: what it sees is the record's observed image. This is
    the ONE lift — every observation claim about executions names a
    record observer and rides this. -/
def execObs (o : Kit.Observer (I × S) O) : Kit.Observer (Exec m s fin) (List O) :=
  ⟨fun e => e.record.map o.see⟩

/-- Equivalence of executions UNDER an observer — the kernel of the
    lifted `see`, i.e. `Kit.Observer.equiv` at the execution level. -/
abbrev equivUnder (o : Kit.Observer (I × S) O) (e₁ e₂ : Exec m s fin) : Prop :=
  (execObs o).equiv e₁ e₂

/-- The proved laws, CITED from Kit.Observer (never re-proved): the
    kernel of `see` is reflexive. -/
theorem equivUnder_refl (o : Kit.Observer (I × S) O) (e : Exec m s fin) :
    e.equivUnder o e := Kit.Observer.equiv_refl _ e

/-- ... symmetric (Kit.Observer.equiv_symm). -/
theorem equivUnder_symm (o : Kit.Observer (I × S) O) {e₁ e₂ : Exec m s fin}
    (h : e₁.equivUnder o e₂) : e₂.equivUnder o e₁ := Kit.Observer.equiv_symm _ h

/-- ... transitive (Kit.Observer.equiv_trans). -/
theorem equivUnder_trans (o : Kit.Observer (I × S) O) {e₁ e₂ e₃ : Exec m s fin}
    (h₁ : e₁.equivUnder o e₂) (h₂ : e₂.equivUnder o e₃) : e₁.equivUnder o e₃ :=
  Kit.Observer.equiv_trans _ h₁ h₂

/-! ## The bridge to Kit.Execution (the standard observers' shape) -/

/-- The minimal-shape execution the standard observers consume
    (Kit.Observer's `Execution`): the record as the trace, cost = the
    record length. `result` is honestly `none` — this slice's machines
    carry no return vocabulary; a terminal-event discipline lands with
    the consumer that has one. -/
def toExecution (e : Exec m s fin) : Kit.Execution (I × S) where
  trace := e.record
  result := none
  cost := e.record.length

/-- The bridge law: the standard AUDIT observer sees exactly the
    execution's record (the result projection is honestly `none`). -/
theorem toExecution_audit (e : Exec m s fin) :
    (Kit.auditObs (I × S)).see e.toExecution = (none, e.record) := rfl

/-! ## THE GRADUATION (16-surface §5.1, 15-patterns #11): Exec ≅ the
    runnable tapes -/

/- The two landed halves: `exec_run` (the execution's tape runs to the
    execution's final state) and `run_exec` (every successful run has a
    witnessing execution). The step?-functional discipline (the
    transition relation IS the graph of `step?` — Basic's `step_iff`)
    means the tape determines the execution: the three tie lemmas above
    close both round trips, and the correspondence is a TRUE `Kit.Iso`. -/

/-- The executions from `start`, the final state carried as data. -/
abbrev ExecsFrom (m : Machine S I) (start : S) : Type := (fin : S) × Exec m start fin

/-- The tapes that run from `start`, with the final state they land on —
    the honest subtype (the run's success rides in the type; a tape
    that refuses is UNREPRESENTABLE, the final state included).

    Carrier-shape note: the final state rides AS DATA (a Σ-subtype over
    the bare run equation), not behind an `∃`. A Type-valued iso cannot
    eliminate a Prop — the reconstruction (`run_exec`) consumes the
    final state and the run equation as ARGUMENTS, and only the Σ shape
    supplies them by projection. The ∃-form is the Prop-level reading,
    tied at `runnableTapes_iff`. -/
abbrev RunnableTapes (m : Machine S I) (start : S) : Type :=
  {ht : (_fin : S) × List I // m.run start ht.2 = some ht.1}

/-- The tape→execution reconstruction (the run tie, as data). -/
def execOfTape (m : Machine S I) (start : S) (ht : RunnableTapes m start) :
    ExecsFrom m start :=
  ⟨ht.1.1, run_exec m start ht.property⟩

/-- The execution→tape projection (the execution tie, as data). -/
def tapeOfExec (m : Machine S I) (start : S) (x : ExecsFrom m start) :
    RunnableTapes m start :=
  ⟨⟨x.1, x.2.tape⟩, exec_run x.2⟩

/-- THE RETRACTION (the carrier's embedding grade): the tape map
    embeds the executions into the runnable tapes, `run_exec`
    reconstructs. `inv_emb` IS `run_exec_exec_run`. -/
def execRetraction (m : Machine S I) (start : S) :
    Kit.Retraction (ExecsFrom m start) (RunnableTapes m start) where
  emb := tapeOfExec m start
  inv := execOfTape m start
  inv_emb x := by
    show execOfTape m start (tapeOfExec m start x) = x
    simp only [tapeOfExec, execOfTape]
    rw [run_exec_exec_run x.2]

/-- THE GRADUATION'S VALUE: the runnable tapes ≅ the executions from
    `start`. `to` reconstructs the execution from the run (the run
    tie); `inv` projects the tape (the execution tie). The image-iso
    upgrade in full: the retraction above restricted to its image is
    this iso (the image's property unfolds to runnability —
    `execRetraction_image_iff`), so nothing stronger is being claimed
    than the two proved round trips. -/
def execIso (m : Machine S I) (start : S) :
    Kit.Iso (RunnableTapes m start) (ExecsFrom m start) where
  to := execOfTape m start
  inv := tapeOfExec m start
  to_inv x := by
    show execOfTape m start (tapeOfExec m start x) = x
    simp only [tapeOfExec, execOfTape]
    rw [run_exec_exec_run x.2]
  inv_to ht := by
    show tapeOfExec m start (execOfTape m start ht) = ht
    have hv : (tapeOfExec m start (execOfTape m start ht)).val = ht.val := by
      show ⟨ht.1.1, (run_exec m start ht.property).tape⟩ = ht.1
      rw [tape_run_exec m start ht.1.2 ht.1.1 ht.property]
    rw [Subtype.ext hv]

/-- The retraction's image IS the runnable tapes (the image's witness
    chain collapses to the subtype's own run equation). -/
theorem execRetraction_image_iff (m : Machine S I) (start : S)
    (ht : RunnableTapes m start) :
    (∃ x : ExecsFrom m start, Kit.Retraction.emb (execRetraction m start) x = ht)
      ↔ m.run start ht.1.2 = some ht.1.1 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact x.2.exec_run
  · intro hf
    exact ⟨execOfTape m start ⟨ht.1, hf⟩, (execIso m start).inv_to ⟨ht.1, hf⟩⟩

/-- The Prop-level reading of the carrier: a Σ-tape runs iff the tape
    has SOME successful run (the final state is determined — the run's
    value IS the landing state). -/
theorem runnableTapes_iff (m : Machine S I) (start : S) (ht : RunnableTapes m start) :
    ∃ fin, m.run start ht.1.2 = some fin := ⟨ht.1.1, ht.property⟩

end Exec

end Machines

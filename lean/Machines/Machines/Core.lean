/-
# Machines.Core — the machine, its two projections

Design: notes/lean/lean-v3.md Part 5 + notes/lean/TOOLKIT.md §2.4.
Veil's two-projection shape, owned: actions are executable functions with
the guard PROOF threaded into construction (an UPDATE…WHERE cannot be
constructed without discharging its guard); the Prop relation is *derived*
from the same definition, so execution and proof case-split over the same
labels and cannot drift.

- Projection 1 (executable): `step?`, `run` — total, emit traces.
- Projection 2 (proof): `tr` — the two-state relation; preservation is a
  theorem (`run_preserves`), not a convention.

Deliberately absent (per lean-v3 D2): nondeterminism (own module, later),
WP/Hoare machinery (deterministic actions collapse it to a one-liner),
SMT. Convergence lives in `Machines.Convergent` (planned); liveness in
`Machines.Live` (lentil's leads_to/wf1, vendored, planned).
-/

namespace Machines

/-- An event: a decidable guard, an action that REQUIRES the guard's proof,
    and the invariant-preservation obligation. The author writes state +
    guard + action; the `safety` field is the PO slot (the Dsl layer will
    default it to `by decide`/`omega` — TOOLKIT §4.2 autoParam). -/
structure EventSpec (S : Type) (Inv : S → Prop) where
  guard : S → Bool
  action : (s : S) → guard s = true → S
  safety : ∀ s h, Inv s → Inv (action s h)

/-- A machine: state type, event labels, invariant, and the event family.
    `Label` should be a generated inductive over event names so proofs
    case-split and execution enumerates the SAME set (the veil Assemble
    pattern). -/
structure Machine where
  State : Type
  Label : Type
  Inv : State → Prop
  event : Label → EventSpec State Inv

namespace Machine

variable (m : Machine)

/-- Is the event enabled (guard holds) in this state? -/
def enabled (s : m.State) (l : m.Label) : Bool := (m.event l).guard s

/-- Execute one event. `none` = not enabled. Total. -/
def step? (s : m.State) (l : m.Label) : Option m.State :=
  if h : (m.event l).guard s = true then some ((m.event l).action s h) else none

/-- The derived two-state relation (projection 2). -/
def tr (s : m.State) (l : m.Label) (s' : m.State) : Prop :=
  ∃ h : (m.event l).guard s = true, (m.event l).action s h = s'

/-- The two projections agree BY CONSTRUCTION: `tr` is the relational
    reading of `step?`. (The tie the oracle rests on.) -/
theorem tr_iff_step? (s : m.State) (l : m.Label) (s' : m.State) :
    m.tr s l s' ↔ m.step? s l = some s' := by
  constructor
  · intro h
    obtain ⟨hg, hact⟩ := h
    unfold step?
    rw [dif_pos hg]
    exact congrArg some hact
  · intro h
    unfold step? at h
    split at h
    · next hg =>
      exact ⟨hg, Option.some.inj h⟩
    · next =>
      simp at h

/-- A trace: the (label, post-state) history of an execution. Journals are
    traces; the replay checker consumes this type. -/
abbrev Trace (m : Machine) := List (m.Label × m.State)

/-- Run an event sequence, emitting the trace. `none` = some event's guard
    failed (the run is REJECTED — invalid sequences are observable, not
    silent). -/
def run (s : m.State) (ls : List m.Label) : Option (Trace m × m.State) :=
  match ls with
  | [] => some ([], s)
  | l :: rest =>
    match m.step? s l with
    | none => none
    | some s' =>
      match run s' rest with
      | none => none
      | some (tr, fin) => some ((l, s') :: tr, fin)

/-- One step preserves the invariant — the EventSpec.safety obligation,
    projected. -/
theorem step?_preserves (s : m.State) (l : m.Label) (s' : m.State)
    (h : m.step? s l = some s') (hi : m.Inv s) : m.Inv s' := by
  unfold step? at h
  split at h
  · next hg =>
    have hs := (m.event l).safety s hg hi
    have heq := Option.some.inj h
    rw [← heq]
    exact hs
  · next =>
    simp at h

/-- The invariant holds at the end of every successful run and at every
    recorded state — the correctness-by-construction payoff: a machine whose
    events all discharge `safety` CANNOT reach a bad state through `run`. -/
-- the @[simp] equation set: every recursive def ships these (lean/AGENTS.md
-- construction rule 1) — proofs consume `simp [Machine.run]`, never walk the
-- match structure by hand.

theorem step?_eq (s : m.State) (l : m.Label) :
    m.step? s l = if h : (m.event l).guard s = true
      then some ((m.event l).action s h) else none := rfl

@[simp] theorem run_nil (s : m.State) : m.run s [] = some ([], s) := rfl

@[simp] theorem run_cons (s : m.State) (l : m.Label) (ls : List m.Label) :
    m.run s (l :: ls) = match m.step? s l with
      | none => none
      | some s' => match m.run s' ls with
        | none => none
        | some (tr, fin) => some ((l, s') :: tr, fin) := rfl

theorem run_preserves (init : m.State) (hinit : m.Inv init)
    (ls : List m.Label) (tr : Trace m) (fin : m.State)
    (h : m.run init ls = some (tr, fin)) : m.Inv fin ∧ ∀ p ∈ tr, m.Inv p.2 := by
  induction ls generalizing init tr with
  | nil =>
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hinit, fun _ hp => by simp at hp⟩
  | cons l rest ih =>
    simp only [run] at h
    split at h
    · next => contradiction
    · next s' hs =>
      split at h
      · next => contradiction
      · next tr' fin' hr =>
        have h' : (l, s') :: tr' = tr ∧ fin' = fin := by
          simpa using h
        obtain ⟨rfl, rfl⟩ := h'
        have hs' := m.step?_preserves init l s' hs hinit
        obtain ⟨hfin, htr⟩ := ih s' hs' tr' hr
        constructor
        · exact hfin
        · intro q hq
          rcases List.mem_cons.mp hq with hqeq | hqtr
          · rw [hqeq]; exact hs'
          · exact htr q hqtr

end Machine

end Machines

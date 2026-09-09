/-
# Machines.Trace — the liveness side of traces

The TRACE TYPE itself lives in `Machines.Core` (`Machine.Trace` — the
replay journal; the lemma `Lean-v3` Part 5 port). This module adds the
predicates that sit ON TOP of traces, without touching Core:

- `Machine.DeadlockFree` — guard-disjunction: from every invariant state,
  SOME event is enabled. The liveness property opposite to `run` rejection
  (a `run` that fails at `fin` means `fin`'s guard was false): no
  invariant state is stuck.
- `Machine.deadlockFree_run_extend` — a deadlock-free machine never ends:
  every successful run can be extended by one more event (`step?` at the
  run's final state is a `some`). In engine terms: a live cascade always
  has somewhere left to go.
- `Machine.deadlockFree_comp_inl` / `Machine.deadlockFree_comp_inr` —
  deadlock-freedom survives parallel composition (`Machines.Compose`):
  the product invariant forces both sides' invariants, so either side's
  witness lifts to an `inl`/`inr` witness in the composite. (A joint
  `deadlockFree_comp` is not provided; the two projections are the
  useful form.)

Trace-type moves (rewind, merge, replay-equality) are their own modules;
this one only owns the deadlock predicates.
-/

import Machines.Compose

namespace Machines

namespace Machine

/-- Deadlock-freedom: from every invariant state, some event is enabled
    (the guard-disjunction property of SPEC/lean-v3 Part 5 Trace).
    In operational terms: no `step?` from a good state is `none`. -/
def DeadlockFree (m : Machine) : Prop :=
  ∀ s : m.State, m.Inv s → ∃ l : m.Label, (m.event l).guard s = true

/-- A deadlock-free machine never ends: every successful run can be extended
    by one more event. `run_preserves` supplies `Inv fin`; the guard
    disjunction supplies the event; `step?` returns its witness action. -/
theorem deadlockFree_run_extend (m : Machine) (init : m.State) (hinit : m.Inv init)
    (ls : List m.Label) (tr : Machine.Trace m) (fin : m.State)
    (h : m.run init ls = some (tr, fin)) (hdf : m.DeadlockFree) :
    ∃ l : m.Label, ∃ s' : m.State, m.step? fin l = some s' := by
  have hfin : m.Inv fin := (m.run_preserves init hinit ls tr fin h).1
  obtain ⟨l, hg⟩ := hdf fin hfin
  exact ⟨l, (m.event l).action fin hg, by
    unfold Machine.step?
    rw [dif_pos hg]⟩

/-- Deadlock-freedom lifts to composition through the LEFT machine: if `m1`
    is deadlock-free, the composite (whose invariant forces `m1.Inv` on the
    first projection) is deadlock-free, witnessed by the `inl` lift of `m1`'s
    guard witness. -/
theorem deadlockFree_comp_inl (m1 m2 : Machine) (h1 : m1.DeadlockFree) :
    (Machine.compose m1 m2).DeadlockFree := by
  intro s hs
  obtain ⟨l, hg⟩ := h1 s.1 hs.1
  exact ⟨Sum.inl l, by simpa [Machine.compose] using hg⟩

/-- Symmetric lift through the RIGHT machine (`inr` witness). -/
theorem deadlockFree_comp_inr (m1 m2 : Machine) (h2 : m2.DeadlockFree) :
    (Machine.compose m1 m2).DeadlockFree := by
  intro s hs
  obtain ⟨l, hg⟩ := h2 s.2 hs.2
  exact ⟨Sum.inr l, by simpa [Machine.compose] using hg⟩

end Machine

end Machines

/-
# Machines.Refine — functional and relational refinement

lean-v3 Part 5: "Refine.lean — functional + relational refinement + PO
bundles (relational is NET-NEW — veil never built it; needed for
stage-walker ≡ queue-cascade where frame order differs)".

Two shapes:

- `RefinesFun` — the concrete machine simulates the abstract one under an
  ABSTRACTION FUNCTION: every concrete step maps to an abstract step.
  Deterministic-schedule refinement (same order).
- `Refines` — simulation up to a RELATION. Frame order may differ between
  the two machines; only the relation is step-preserved. This is the shape
  the schedule-equivalence refinement needs (SPEC §7.4: "Refinement is
  RELATIONAL (frame order differs)").

The payoff theorem (`Refines.run_sim`): every concrete run lifts to an
abstract run over the interpreted labels, ending in related states — the
oracle-level statement: observed concrete behavior is explained abstractly.
-/

import Machines.Core

namespace Machines

variable {c a : Machine}

/-- Relational refinement: `c` refines `a` up to `R`, with label
    interpretation `ρ`. -/
structure Machine.Refines (c a : Machine) where
  /-- The simulation relation. -/
  R : c.State → a.State → Prop
  /-- Label interpretation: which abstract event a concrete event means. -/
  ρ : c.Label → a.Label
  /-- Initial states relate: concrete invariant states have an abstract
      counterpart... stated as: related states exist for every concrete
      invariant state the caller starts from (the caller supplies `as`). -/
  step : ∀ cs as l cs', R cs as → c.tr cs l cs' →
    ∃ as', a.tr as (ρ l) as' ∧ R cs' as'

/-- Functional refinement: the relation is the graph of an abstraction
    function. -/
structure Machine.RefinesFun (c a : Machine) where
  abs : c.State → a.State
  ρ : c.Label → a.Label
  step : ∀ cs l cs', c.tr cs l cs' → a.tr (abs cs) (ρ l) (abs cs')

/-- Functional refinement is relational refinement. -/
def Machine.RefinesFun.toRefines (r : Machine.RefinesFun c a) : c.Refines a where
  R := fun cs as => r.abs cs = as
  ρ := r.ρ
  step := fun cs as l cs' hR htr => by
    subst hR
    exact ⟨r.abs cs', r.step cs l cs' htr, rfl⟩

/-- **The simulation lifts to runs**: every concrete run has an abstract
    counterpart over the interpreted labels, ending in related states. The
    schedule-walker's output is thus explained by the reference cascade. -/
theorem Machine.Refines.run_sim (r : c.Refines a) :
    ∀ (ls : List c.Label) cs as tr fin,
      c.run cs ls = some (tr, fin) → r.R cs as →
      ∃ atr afin, a.run as (ls.map r.ρ) = some (atr, afin) ∧ r.R fin afin := by
  intro ls
  induction ls with
  | nil =>
    intro cs as tr fin hrun hR
    simp only [Machine.run, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨[], as, rfl, hR⟩
  | cons l rest ih =>
    intro cs as tr fin hrun hR
    simp only [Machine.run] at hrun
    split at hrun
    · contradiction
    · next s' hstep =>
      split at hrun
      · contradiction
      · next tr' fin' hrest =>
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrun)
        subst h1 h2
        have htr : c.tr cs l s' := (c.tr_iff_step? cs l s').mpr hstep
        obtain ⟨as', hatr, hR'⟩ := r.step cs as l s' hR htr
        have hastep : a.step? as (r.ρ l) = some as' := (a.tr_iff_step? as (r.ρ l) as').mp hatr
        obtain ⟨atr, afin, harun, hRfin⟩ := ih s' as' tr' fin' hrest hR'
        refine ⟨(r.ρ l, as') :: atr, afin, ?_, hRfin⟩
        simp only [List.map_cons, Machine.run, hastep, harun]

end Machines

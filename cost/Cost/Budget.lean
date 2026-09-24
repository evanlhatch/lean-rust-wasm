/-
# Cost.Budget — the budget discipline: monus-shaped, exhaustion as data

The Change-ladder connection (notes/v3/01-core.md §1 + §3): a budget is
NOT a root — "resources are not a root: fuel/budgets/size = monotone
consumption, a Change instance (monus)". The delta here is the cost,
the state is the remaining budget, and the application IS
`Kit.Change.monus` (saturating subtraction: composes, has the no-op,
NOT reversible — information is lost, which is exactly the budget's
honesty).

And the bounded-exploration trichotomy's rule (01 §3) is honored at the
data level: **budget exhaustion is UNKNOWN, never silently a verdict**.
`spend` answers with DATA — `.covered` (the monus remaining) or
`.exhausted` (the shortfall) — and BOTH outcomes carry the computed
value: what ran out is the budget, not the computation; no outcome is
smuggled in as a verdict on the program.

The composition law is the Change ladder's `applyCompose` read on
budgets (`spend_seq`): two sequential spends are ONE spend of the
composed cost — cited from `Kit.monus`, never re-proved.

The five questions (notes/v3/01-core.md):
- **Root**: Change (01 §1's named degenerate case) — the budget is the
  monus instance's state; the cost is the delta.
- **Carrier grade**: the outcome as closed data (`BudgetOutcome`) —
  exhaustion observable, never a silent collapse.
- **Spine reading**: none — the discipline layer's budget substrate.
- **Ladder rung**: the monus rung (WithIdentity — composes, no-op, NOT
  reversible), cited; the theorems below are one-line citations.
- **Gate rows**: the axiom report over the spend theorems + CostTests
  pins (the exhaustion teeth + the mandatory negative controls).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Cost.Basic
import Kit.Change

namespace Cost

/-! ## The budget outcome -/

/-- The budget outcome: exhaustion is OBSERVABLE DATA. `.covered`
    carries the remaining budget (the monus apply); `.exhausted`
    carries the shortfall. BOTH carry the value — the graded eval is
    total, the budget's exhaustion is bookkeeping data, never a verdict
    on the program (01 §3). -/
inductive BudgetOutcome (α : Type) where
  | covered (val : α) (remaining : Nat)
  | exhausted (val : α) (shortfall : Nat)

deriving Repr, BEq, DecidableEq

/-- spend: run a graded computation against a Nat budget. The budget is
    monus-shaped state (`Kit.monus`: apply s d = some (s - d)); the
    cost is the delta; the outcome names which branch the monus took —
    as data, with the shortfall when saturated. -/
def spend (budget : Nat) (g : Graded Nat α) : BudgetOutcome α :=
  if g.cost ≤ budget then
    .covered g.val (budget - g.cost)
  else
    .exhausted g.val (g.cost - budget)

/-! ## The laws (cited, not re-proved) -/

/-- The covered branch: the remaining budget is EXACTLY the monus
    apply — the budget is the monus instance's state, the cost its
    delta (01 §1). -/
theorem spend_covered {α : Type} {g : Graded Nat α} {budget : Nat}
    (h : g.cost ≤ budget) :
    spend budget g = .covered g.val (budget - g.cost) := by
  simp only [spend, if_pos h]

/-- The exhausted branch: the shortfall is the data, and the VALUE is
    still delivered — exhaustion is never a verdict on the program. -/
theorem spend_exhausted {α : Type} {g : Graded Nat α} {budget : Nat}
    (h : budget < g.cost) :
    spend budget g = .exhausted g.val (g.cost - budget) := by
  simp only [spend, if_neg (Nat.not_le.mpr h)]

/-- THE monus tie, spelled out: the delta application is the Change
    ladder's `monus` (the `WithIdentity` rung — composes, no-op, NOT
    reversible; the budget forgets what was spent, which is why a
    budget can never be un-spent). -/
theorem covered_remaining_monus (budget cost : Nat) :
    Kit.monus.apply budget cost = some (budget - cost) := rfl

/-- THE budget composition law (the Change ladder's `applyCompose`
    read on budgets): two sequential spends — the budget handed on
    through the Option — are ONE spend of the COMPOSED cost. Cited
    from `Kit.monus.applyCompose`; budgets compose, they don't fork. -/
theorem spend_seq (budget c₁ c₂ : Nat) :
    (Kit.monus.apply budget c₁).bind (Kit.monus.apply · c₂)
      = Kit.monus.apply budget (c₁ + c₂) :=
  (Kit.monus.applyCompose budget c₁ c₂).symm

end Cost

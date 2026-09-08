/-
# Dbsp.Ordering — monotone streams and the derivative landmine

Ports tchajed/database-stream-processing-theory `src/ordering.lean` (Lean 3,
79 lines) to Lean 4 (notes/lean/lean-v3.md Part 3).

The content is one theorem and one counterexample:

- `derivative_pos`: a monotone stream with a nonneg start has a nonneg
  derivative — the hypothesis `0 ≤ s 0` is REQUIRED (the DBSP paper omits
  it).
- `derivative_pos_counter_example`: without the start hypothesis the claim
  is false — a constant negative stream is monotone with a negative
  derivative at t=0. **This is the floor-lint's formal justification**
  (lean-v3 Part 4.5 / SPEC-core §7): monotone flow alone never guarantees a
  floored stock stays floored; the floor must be declared and the clamp
  generated. The lint cites this theorem.
-/

import Dbsp.Linear
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Pi

namespace Dbsp

-- mathlib's unbundled ordered group: AddCommGroup + PartialOrder + IsOrderedAddMonoid
-- (the old `OrderedAddCommGroup` no longer exists).
variable {a b : Type} [AddCommGroup a] [PartialOrder a] [IsOrderedAddMonoid a]
  [AddCommGroup b] [PartialOrder b] [IsOrderedAddMonoid b]

/-- A stream of nonnegatives. -/
def positive (s : Stream a) : Prop := 0 ≤ s

/-- Pointwise-nondecreasing. -/
def StreamMonotone (s : Stream a) : Prop := ∀ t, s t ≤ s (t + 1)

/-- An operator preserving positivity. -/
def IsPositive (f : Stream a → Stream b) : Prop := ∀ s, positive s → positive (f s)

/-- Stepwise monotonicity is order preservation. -/
theorem stream_monotone_order (s : Stream a) :
    StreamMonotone s ↔ ∀ t1 t2, t1 ≤ t2 → s t1 ≤ s t2 := by
  constructor
  · intro h t1 t2 hle
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    clear hle
    induction d with
    | zero => rw [Nat.add_zero]
    | succ d ih =>
      rw [Nat.add_succ]
      exact le_trans ih (h (t1 + d))
  · intro h t
    exact h t (t + 1) (Nat.le_succ t)

/-- The integral of a nonnegative stream is monotone. -/
theorem integral_monotone (s : Stream a) (hp : positive s) :
    StreamMonotone (I s) := by
  intro t
  rw [integral_sum_vals, integral_sum_vals]
  show sumVals s (t + 1) ≤ s (t + 1) + sumVals s (t + 1)
  exact le_add_of_nonneg_left (hp (t + 1))

/-- **Monotone + nonneg start ⇒ nonneg derivative.** The `0 ≤ s 0`
    hypothesis is the one the DBSP paper omits; without it the claim is
    false (see `derivative_pos_counter_example`). -/
theorem derivative_pos (s : Stream a) (h0 : 0 ≤ s 0) (hm : StreamMonotone s) :
    positive (D s) := by
  intro t
  show 0 ≤ s t - delay s t
  cases t with
  | zero => simp only [delay_zero, sub_zero]; exact h0
  | succ n =>
    rw [delay_succ, sub_nonneg]
    exact hm n

/-- **The landmine, proved negative.** Monotone does NOT imply nonneg
    derivative in general: a constant negative stream is monotone, and its
    derivative at t=0 is negative. Stock-flow clamping (the resolve phase,
    SPEC-core §7.2) and the floor lint exist because this is false without
    the start hypothesis. -/
theorem derivative_pos_counter_example (h : ∃ x : a, x < 0) :
    ¬ ∀ s : Stream a, StreamMonotone s → positive (D s) := by
  obtain ⟨x, hx⟩ := h
  intro hall
  have hmono : StreamMonotone (fun _ => x : Stream a) := fun _ => le_refl _
  have hpos := hall _ hmono 0
  have h2 : (0 : a) ≤ x := by
    simp only [Pi.zero_apply, D, Pi.sub_apply, delay_zero, sub_zero] at hpos
    exact hpos
  exact not_le_of_gt hx h2

end Dbsp

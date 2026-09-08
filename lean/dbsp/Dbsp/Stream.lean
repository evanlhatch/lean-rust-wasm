/-
# Dbsp.Stream — streams and agreement

Ports tchajed/database-stream-processing-theory `src/stream.lean` (Lean 3)
to Lean 4 (notes/lean/lean-v3.md Part 3). Streams are functions of time;
`agreeUpto` is the workhorse equivalence the fixpoint theorems are proved
through.

Deferred from the source: the `cut` machinery and `zero_after`/stream-elim
(our exec layer is fuel-bounded vectors with a decidable convergence check +
a bridge theorem — notes/lean/SPEC-core.md §7.1; the classical choice the
source needs evaporates for us).
-/

import Dbsp.Lint
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Notation.Prod

namespace Dbsp

/-- A stream is a function from time. -/
abbrev Stream (a : Type) := Nat → a

-- Group structure on streams comes from mathlib's Pi instances
-- (`Pi.instZero`, `Pi.addCommGroup`, ... — lean-v3 D1). The earlier local
-- Zero/OfNat instances were removed: two sources of the same instance is a
-- diamond, and mathlib's are the canonical ones.

/-- Two streams agree up to time `n` (inclusive). -/
def agreeUpto (n : Nat) (s₁ s₂ : Stream a) : Prop := ∀ t, t ≤ n → s₁ t = s₂ t

@[refl] theorem agree_refl (n : Nat) (s : Stream a) : agreeUpto n s s :=
  fun _ _ => rfl

theorem agree_symm (n : Nat) (s₁ s₂ : Stream a) : agreeUpto n s₁ s₂ → agreeUpto n s₂ s₁ :=
  fun h t ht => (h t ht).symm

theorem agree_trans (s₁ s₂ s₃ : Stream a) :
    agreeUpto n s₁ s₂ → agreeUpto n s₂ s₃ → agreeUpto n s₁ s₃ :=
  fun h₁ h₂ t ht => (h₁ t ht).trans (h₂ t ht)

/-- Pointwise-agreeing-everywhere streams are equal (funext). -/
theorem agree_everywhere_eq (s s' : Stream a) :
    s = s' ↔ ∀ n, agreeUpto n s s' := by
  constructor
  · intro h n t _; rw [h]
  · intro h; funext t; exact h t t (Nat.le_refl t)

theorem agree_upto_0 (s s' : Stream a) : agreeUpto 0 s s' ↔ s 0 = s' 0 := by
  constructor
  · intro h; exact h 0 (Nat.le_refl 0)
  · intro h t ht
    have h0 : t = 0 := Nat.eq_zero_of_le_zero ht
    subst h0; exact h

/-- Extend agreement by one step given the endpoints match. -/
theorem agree_upto_extend (n : Nat) (s s' : Stream a)
    (h : agreeUpto n s s') (hn : s (n + 1) = s' (n + 1)) : agreeUpto (n + 1) s s' := by
  intro t ht
  rcases Nat.lt_or_eq_of_le ht with hlt | heq
  · exact h t (Nat.lt_succ_iff.mp hlt)
  · subst heq; exact hn

/-- Agreement weakens along the index. -/
theorem agree_upto_weaken (s s' : Stream a) (n n' : Nat)
    (h : agreeUpto n s s') (hnn' : n' ≤ n) : agreeUpto n' s s' :=
  fun t ht => h t (Nat.le_trans ht hnn')

end Dbsp

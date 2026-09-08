/-
# Dbsp.StreamElim — eliminating streams to single values

Ports tchajed/database-stream-processing-theory `src/stream_elim.lean`
(Lean 3) to Lean 4 (notes/lean/lean-v3.md Part 3).

`streamElim s` ("∫ s" in the source) is the sum of an eventually-zero
stream — well-defined because the partial sums stabilize. This is how a
finite computation is read out of the stream world: a converged cascade
produces deltas that are zero after the fixpoint pass, and `streamElim`
extracts the answer. The classical choice in the source's definition is
inert for us: every USE comes with a `ZeroAfter` proof (the convergence
certificate), and then `stream_elim_zero_after` gives the computational
content (the partial sum). Our exec layer stays fuel-bounded with a
decidable convergence check (SPEC-core.md §7.1) — this file is the theory
that certifies what the fuel-bounded check computes.

Deliberately NOT ported: the source's closing `example` (it documents, with
sorries, that `stream_elim` is NOT invariant under incrementalization —
kept as a comment in the source; a non-theorem needs no port).

Also here: `δ0` (the unit impulse), `zeroAfter`, and the I/D interplay
lemmas (`integral_zero`, `integral_delta`, `nested_zpp`).
-/

import Dbsp.Incremental

open Classical

namespace Dbsp

variable {a b : Type}

section Zero

variable [Zero a]

/-- The unit impulse: `x` at time 0, zero afterwards. -/
def δ0 (x : a) : Stream a := fun t => if t = 0 then x else 0

@[simp] theorem δ0_apply (x : a) (n : Nat) : δ0 x n = if n = 0 then x else 0 := rfl

@[simp] theorem δ0_0 : δ0 (0 : a) = 0 := by
  funext t
  simp only [δ0]
  split_ifs <;> simp

/-- `s` is zero from time `n` on. The convergence certificate. -/
def ZeroAfter (s : Stream a) (n : Nat) : Prop := ∀ t, t ≥ n → s t = 0

theorem zero_after_ge {s : Stream a} {n1 : Nat} (pf1 : ZeroAfter s n1) :
    ∀ n2 ≥ n1, ZeroAfter s n2 := by
  intro n2 hge m hge2
  exact pf1 m (Nat.le_trans hge hge2)

theorem δ0_zero_after (x : a) : ZeroAfter (δ0 x) 1 := by
  intro t hge
  simp only [δ0]
  rw [if_neg (by omega)]

end Zero

variable [AddCommGroup a] [AddCommGroup b]

/-- Drop the first `k` elements of a stream. -/
def drop (k : Nat) (s : Stream a) : Stream a := fun n => s (k + n)

theorem sum_vals_split (s : Stream a) (n k : Nat) :
    sumVals s (n + k) = sumVals s n + sumVals (drop n s) k := by
  induction k generalizing n with
  | zero => simp [sumVals]
  | succ k ih =>
    have e1 : sumVals s (n + (k + 1)) = s (n + k) + sumVals s (n + k) := rfl
    have e2 : sumVals (drop n s) (k + 1) = drop n s k + sumVals (drop n s) k := rfl
    rw [e1, e2, ih]
    show s (n + k) + (sumVals s n + sumVals (drop n s) k)
       = sumVals s n + (s (n + k) + sumVals (drop n s) k)
    abel

theorem sum_vals_zero_ge (s : Stream a) (n m : Nat) (hz : ZeroAfter s n) (hge : m ≥ n) :
    sumVals s n = sumVals s m := by
  have hzero : sumVals (drop n s) (m - n) = 0 := by
    apply sumVals_zero
    intro t
    exact hz (n + t) (by omega)
  have hdiff : m = n + (m - n) := by omega
  rw [hdiff, sum_vals_split, hzero, add_zero]

theorem sum_vals_eq_helper (s : Stream a) (n1 n2 : Nat)
    (hz1 : ZeroAfter s n1) (hz2 : ZeroAfter s n2) (hle : n1 ≤ n2) :
    sumVals s n1 = sumVals s n2 :=
  sum_vals_zero_ge s n1 n2 hz1 hle

theorem sum_vals_eq (s : Stream a) (n1 n2 : Nat)
    (hz1 : ZeroAfter s n1) (hz2 : ZeroAfter s n2) :
    sumVals s n1 = sumVals s n2 := by
  rcases Nat.le_total n1 n2 with h | h
  · exact sum_vals_eq_helper s n1 n2 hz1 hz2 h
  · exact (sum_vals_eq_helper s n2 n1 hz2 hz1 h).symm

/-- The sum of an eventually-zero stream (the source's `∫ s`).
    Noncomputable (classical choice of the bound) — every use should come
    with an explicit `ZeroAfter` certificate, after which
    `stream_elim_zero_after` makes it a plain partial sum. -/
noncomputable def streamElim (s : Stream a) : a :=
  if h : ∃ n, ZeroAfter s n then sumVals s (Classical.choose h) else 0

theorem stream_elim_zero_after (s : Stream a) (n : Nat) (pf : ZeroAfter s n) :
    streamElim s = sumVals s n := by
  unfold streamElim
  rw [dif_pos ⟨n, pf⟩]
  exact sum_vals_eq s _ _ (Classical.choose_spec _) pf

@[simp] theorem stream_elim_0 : streamElim (0 : Stream a) = 0 := by
  rw [stream_elim_zero_after _ 0]
  · simp
  · intro t _
    rfl

theorem stream_elim_delta (x : a) : streamElim (δ0 x) = x := by
  rw [stream_elim_zero_after _ 1 (δ0_zero_after x)]
  show δ0 x 0 + sumVals (δ0 x) 0 = x
  simp

theorem delta_linear : ∀ (x y : a), δ0 (x + y) = δ0 x + δ0 y := by
  intro x y
  funext t
  show (if t = 0 then x + y else 0) = δ0 x t + δ0 y t
  simp only [δ0]
  split_ifs <;> simp

@[simp] theorem delta_incremental : incremental (lifting (@δ0 a _)) = lifting δ0 := by
  apply lti_incremental
  apply lifting_lti
  exact delta_linear

theorem sum_vals_linear (s1 s2 : Stream a) (n : Nat) :
    sumVals (s1 + s2) n = sumVals s1 n + sumVals s2 n := by
  induction n with
  | zero => simp [sumVals]
  | succ n ih =>
    show (s1 + s2) n + sumVals (s1 + s2) n = (s1 n + sumVals s1 n) + (s2 n + sumVals s2 n)
    rw [ih]
    show s1 n + s2 n + (sumVals s1 n + sumVals s2 n) = _
    abel

theorem sum_zero_after {s1 s2 : Stream a} {n1 : Nat} (pf1 : ZeroAfter s1 n1)
    {n2 : Nat} (pf2 : ZeroAfter s2 n2) :
    ZeroAfter (s1 + s2) (if n1 ≥ n2 then n1 else n2) := by
  split_ifs with h
  · intro m hge
    show s1 m + s2 m = 0
    rw [pf1 m (by omega), pf2 m (by omega), add_zero]
  · intro m hge
    show s1 m + s2 m = 0
    rw [pf1 m (by omega), pf2 m (by omega), add_zero]

theorem sub_zero_after {s1 s2 : Stream a} {n1 : Nat} (pf1 : ZeroAfter s1 n1)
    {n2 : Nat} (pf2 : ZeroAfter s2 n2) :
    ZeroAfter (s1 - s2) (if n1 ≥ n2 then n1 else n2) := by
  split_ifs with h
  · intro m hge
    show s1 m - s2 m = 0
    rw [pf1 m (by omega), pf2 m (by omega), sub_self]
  · intro m hge
    show s1 m - s2 m = 0
    rw [pf1 m (by omega), pf2 m (by omega), sub_self]

/-- streamElim is linear (given convergence certificates for the inputs). -/
theorem stream_elim_linear (s1 s2 : Stream a)
    (n1 : Nat) (pf1 : ZeroAfter s1 n1) (n2 : Nat) (pf2 : ZeroAfter s2 n2) :
    streamElim (s1 + s2) = streamElim s1 + streamElim s2 := by
  rw [stream_elim_zero_after s1 _ pf1, stream_elim_zero_after s2 _ pf2,
    stream_elim_zero_after _ _ (sum_zero_after pf1 pf2)]
  by_cases h : n2 ≤ n1
  · rw [if_pos h]
    rw [sum_vals_zero_ge s2 n2 n1 pf2 h]
    exact sum_vals_linear s1 s2 n1
  · rw [if_neg h]
    rw [sum_vals_zero_ge s1 n1 n2 pf1 (Nat.le_of_not_ge h)]
    exact sum_vals_linear s1 s2 n2

theorem stream_elim_time_invariant : TimeInvariant (lifting (@streamElim a _)) := by
  apply lifting_time_invariant
  simp

/-- If the integral is eventually zero, the input was eventually zero
    (shifted by one). -/
theorem integral_zero (s : Stream a) (n : Nat) :
    ZeroAfter (I s) n → ZeroAfter s (n + 1) := by
  intro hz m hge
  have hm := hz m (by omega)
  have hm' := congr_fun (integral_unfold s) m
  rw [hm'] at hm
  -- hm : s m + delay (I s) m = 0
  cases m with
  | zero => omega
  | succ k =>
    have hprev := hz k (by omega)
    -- delay (I s) (k+1) = I s k = 0
    have : s (k + 1) + delay (I s) (k + 1) = 0 := hm
    rw [delay_succ] at this
    rw [hprev, add_zero] at this
    exact this

/-- Pointwise unfolding of the integral away from zero. -/
theorem integral_nested_unfold (s : Stream (Stream a)) (t : Nat) (h : 0 < t) :
    I s t = s t + I s (t - 1) := by
  have hu := congr_fun (integral_unfold s) t
  rw [hu]
  show s t + delay (I s) t = s t + I s (t - 1)
  rw [delay_sub_1 _ t h]

/-- The nested form of `integral_zero`. -/
theorem integral_zero' (s : Stream (Stream a)) (t n : Nat) :
    ZeroAfter (I s t) n → ZeroAfter (I s (t - 1)) n → ZeroAfter (s t) (n + 1) := by
  intro hz hz'
  by_cases ht : t = 0
  · subst ht
    intro m hge
    have h0 := congr_fun (integral_unfold s) 0
    -- I s 0 = s 0 + delay (I s) 0 = s 0 + 0
    have : s 0 m = I s 0 m := by
      have := congr_fun h0 m
      simp only [Pi.add_apply, delay_zero, Pi.zero_apply, add_zero] at this
      exact this.symm
    rw [this]
    exact hz m (by omega)
  · intro m hge
    have hd := congr_fun (derivative_difference s t (Nat.pos_of_ne_zero ht)) m
    -- D s t m = s t m - s (t-1) m; but D (I s) = s
    have key : s t m = D (I s) t m := by rw [integral_derivative]
    rw [key]
    show D (I s) t m = 0
    rw [derivative_difference _ t (Nat.pos_of_ne_zero ht)]
    show I s t m - I s (t - 1) m = 0
    rw [hz m (by omega), hz' m (by omega), sub_self]

/-- The integral of an impulse is constant. -/
theorem integral_delta (x : a) : I (δ0 x) = fun _ => x := by
  funext t
  induction t with
  | zero => simp
  | succ n ih =>
    have h := congr_fun (integral_unfold (δ0 x)) (n + 1)
    show I (δ0 x) (n + 1) = x
    rw [h]
    show δ0 x (n + 1) + delay (I (δ0 x)) (n + 1) = x
    rw [delay_succ, ih]
    simp [δ0]

@[simp] theorem integral_delta_apply (x : a) (n : Nat) : I (δ0 x) n = x := by
  rw [integral_delta]

/-- The streamElim of a time-invariant operator applied to the zero impulse
    is zero. -/
theorem nested_zpp (Q : Operator a b) (hti : TimeInvariant Q) :
    streamElim (Q (δ0 0)) = 0 := by
  rw [δ0_0, time_invariant_zpp Q hti, stream_elim_0]

end Dbsp

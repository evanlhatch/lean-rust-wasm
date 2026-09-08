/-
# Dbsp.NestedCycle — the nested-stream ("cycle2") machinery

Ports the `fix2` section of tchajed/database-stream-processing-theory
`src/operators.lean` and the nested-stream cycle theorems of
`src/incremental.lean` (lines ~181-330) to Lean 4
(notes/lean/lean-v3.md Part 3).

The source's notation maps: `↑↑` is our `lifting`, `↑²` is our `lifting2`,
`z⁻¹` is `delay`, and `==n==` is `agreeUpto`. `fix2` is the fixpoint
lifted one level: of an operator on `Stream (Stream a)`, producing a
`Stream (Stream a)`. The two-dimensional strictness (column-strictness),
`strict2`, is the license for its fixpoint theorems; `agree_upto2` is the
row-wise agreement its proofs run through.

The crown jewels:

- `fix2_eq`, `fix2_unique` (with `fixpoints2_unique`, `causal_nested`,
  `strict2`, `agree_upto2` machinery) — the nested fixpoint theorem. The
  recursive-rule contract when the state is itself a stream.
- `lifting_cycle` — the lifted one-input feedback loop equals the nested
  loop: `↑↑(λ s, fix (λ α, T s z⁻¹ α)) = λ s, fix2 (λ α, ↑²T s ↑↑z⁻¹ α)`.
- `cycle2_incremental` — **the nested cascade theorem**: the incremental
  form of the nested loop is the nested loop of the incrementalized body:
  `(λ s, fix2 (λ α, T s ↑↑z⁻¹ α))^Δ = λ s, fix2 (λ α, T^Δ2 s ↑↑z⁻¹ α)`.
  Recursion incrementalizes at one more level of nesting.
- `integral_lift_time_invariant`, `lift_integral_lift_time_invariant`,
  `sum_vals_nested` — the I/D commutation licenses under `lifting delay`.
- `integral_causal_nested`, `derivative_causal_nested` — nested causality
  of I and D, and `cycle_body_strict2` / `cycle_body_incremental_strict2`
  — the nested strictness facts that make `cycle2_incremental` go.

Deferred (part of the source sections but not needed by the cycle2
theorem, and duplicating the unary flow): the sprod/`integral_sprod`
product forms and the `feedback_ckt_*` family from operators.lean.
-/

import Dbsp.Incremental
import Dbsp.StreamElim

namespace Dbsp

variable {a b c : Type}

/-! ## The nested fixpoint -/

section Fix2

variable [Zero a]

/-- The nested fixpoint: at row-column (n, t) read the t-th iterate of F
    at (n, t). -/
def fix2 (F : Operator (Stream a) (Stream a)) : Stream (Stream a) :=
  fun n t => nthIter F t n t

/-- Nested causality: output at (n, t) depends only on inputs at rows ≤ n
    and columns ≤ t. -/
def causal_nested (Q : Operator (Stream a) (Stream b)) : Prop :=
  ∀ (s s' : Stream (Stream a)) (n t : Nat),
    (∀ n', n' ≤ n → ∀ t', t' ≤ t → s n' t' = s' n' t') → Q s n t = Q s' n t

/-- Nested strictness: output at (n, t) depends only on inputs at rows
    ≤ n and columns < t. -/
def strict2 (Q : Operator (Stream a) (Stream b)) : Prop :=
  ∀ (s s' : Stream (Stream a)) (n t : Nat),
    (∀ n', n' ≤ n → ∀ t', t' < t → s n' t' = s' n' t') → Q s n t = Q s' n t

omit [Zero a] in
theorem strict2_is_causal_nested (Q : Operator (Stream a) (Stream b)) :
    strict2 Q → causal_nested Q := by
  intro hstrict s s' n t heq
  exact hstrict s s' n t (fun n' hn' t' ht' => heq n' hn' t' (Nat.le_of_lt ht'))

omit [Zero a] in
/-- A nested-strict operator is independent of its input at column 0. -/
theorem strict2_agree_0 (F : Operator (Stream a) (Stream b)) (hstrict : strict2 F) :
    ∀ s s' n, F s n 0 = F s' n 0 := by
  intro s s' n
  exact hstrict s s' n 0 (fun n' hn' t' ht' => absurd ht' (Nat.not_lt_zero t'))

/-- At column 0 the nested-strict output is the all-zero input's output. -/
theorem strict2_eq_0 (F : Operator (Stream a) (Stream b)) (hstrict : strict2 F) :
    ∀ s n, F s n 0 = F 0 n 0 := by
  intro s n
  exact strict2_agree_0 F hstrict s 0 n

/-- Row-wise agreement: `s1` and `s2` agree up to column `t` in every
    row. -/
def agree_upto2 (t : Nat) (s1 s2 : Stream (Stream a)) : Prop :=
  ∀ n, ∀ t' (_ : t' ≤ t), s1 n t' = s2 n t'

omit [Zero a] in
theorem agree_upto2_refl (t : Nat) (s : Stream (Stream a)) : agree_upto2 t s s :=
  fun _ _ _ => rfl

omit [Zero a] in
theorem agree_upto2_symm (t : Nat) (s1 s2 : Stream (Stream a)) :
    agree_upto2 t s1 s2 → agree_upto2 t s2 s1 :=
  fun h n t' hle => (h n t' hle).symm

omit [Zero a] in
theorem agree_upto2_trans (t : Nat) (s1 s2 s3 : Stream (Stream a)) :
    agree_upto2 t s1 s2 → agree_upto2 t s2 s3 → agree_upto2 t s1 s3 :=
  fun h1 h2 n t' hle => (h1 n t' hle).trans (h2 n t' hle)

omit [Zero a] in
theorem agree_upto2_0 (s1 s2 : Stream (Stream a)) :
    agree_upto2 0 s1 s2 ↔ ∀ n, s1 n 0 = s2 n 0 := by
  constructor
  · intro h n
    exact h n 0 (Nat.le_refl 0)
  · intro h n t' ht'
    have ht : t' = 0 := Nat.eq_zero_of_le_zero ht'
    subst ht
    exact h n

omit [Zero a] in
theorem agree_upto2_extend (t : Nat) (s s' : Stream (Stream a)) :
    agree_upto2 t s s' → (∀ n, s n (t + 1) = s' n (t + 1)) → agree_upto2 (t + 1) s s' := by
  intro h hnext n t' ht'
  rcases Nat.lt_or_eq_of_le ht' with hlt | heq
  · exact h n t' (Nat.le_of_lt_succ hlt)
  · subst heq
    exact hnext n

omit [Zero a] in
/-- Nested strictness propagates row-wise agreement one column further. -/
theorem agree_upto2_strict_extend (S : Operator (Stream a) (Stream b))
    (hstrict : strict2 S) (s s' : Stream (Stream a)) :
    ∀ t, agree_upto2 t s s' → agree_upto2 (t + 1) (S s) (S s') := by
  intro t h n t' ht'
  apply hstrict
  intro n' hn' t'' ht''
  exact h n' t'' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le ht'' ht'))

omit [Zero a] in
theorem strict_agree2_at_next (S : Operator (Stream a) (Stream b)) (hstrict : strict2 S) :
    ∀ s s' t, agree_upto2 t s s' → ∀ n, S s n (t + 1) = S s' n (t + 1) := by
  intro s s' t h n
  apply hstrict
  intro n' hn' t'' ht''
  exact h n' t'' (Nat.le_of_lt_succ ht'')

/-- At row t, the t-th iterate agrees with the fixpoint up to column t,
    and the fixpoint is a fixpoint up to column t. -/
private theorem nth_fix2_agree_aux (F : Operator (Stream a) (Stream a)) (hstrict : strict2 F)
    (t : Nat) : agree_upto2 t (nthIter F t) (fix2 F) ∧ agree_upto2 t (fix2 F) (F (fix2 F)) := by
  induction t with
  | zero =>
    rw [agree_upto2_0, agree_upto2_0]
    constructor
    · intro n
      rfl
    · intro n
      exact strict2_agree_0 F hstrict 0 (fix2 F) n
  | succ t ih =>
    rw [nthIter_succ]
    obtain ⟨h_fix, h_unfold⟩ := ih
    have h : agree_upto2 (t + 1) (F (nthIter F t)) (F (fix2 F)) :=
      agree_upto2_strict_extend F hstrict (nthIter F t) (fix2 F) t h_fix
    have h2 : agree_upto2 (t + 1) (fix2 F) (F (fix2 F)) := by
      apply agree_upto2_extend
      · exact h_unfold
      · intro n
        change nthIter F (t + 1) n (t + 1) = F (fix2 F) n (t + 1)
        rw [nthIter_succ]
        exact strict_agree2_at_next F hstrict (nthIter F t) (fix2 F) t h_fix n
    constructor
    · apply agree_upto2_trans (t + 1) (F (nthIter F t)) (F (fix2 F)) (fix2 F)
      · exact h
      · exact agree_upto2_symm (t + 1) (fix2 F) (F (fix2 F)) h2
    · exact h2

/-- `fix2_eq` — for nested-strict F, `fix2 F` is a fixpoint. -/
theorem fix2_eq (F : Operator (Stream a) (Stream a)) (hstrict : strict2 F) :
    fix2 F = F (fix2 F) := by
  funext n t
  exact (nth_fix2_agree_aux F hstrict t).2 n t (Nat.le_refl t)

omit [Zero a] in
/-- Row-wise agreement in every column implies equality. -/
theorem agree2_everywhere_eq (s1 s2 : Stream (Stream a)) :
    (∀ t, agree_upto2 t s1 s2) → s1 = s2 := by
  intro h
  funext n t
  exact h t n t (Nat.le_refl t)

omit [Zero a] in
/-- Fixpoints of a nested-strict operator are unique. -/
protected theorem fixpoints2_unique (F : Operator (Stream a) (Stream a)) (hstrict : strict2 F)
    (α β : Stream (Stream a)) : α = F α → β = F β → α = β := by
  intro hα hβ
  apply agree2_everywhere_eq
  intro t
  induction t with
  | zero =>
    rw [hα, hβ]
    intro n t' ht'
    have ht : t' = 0 := Nat.eq_zero_of_le_zero ht'
    subst ht
    exact strict2_agree_0 F hstrict α β n
  | succ t ih =>
    rw [hα, hβ]
    exact agree_upto2_strict_extend F hstrict α β t ih

/-- `fix2_unique` — any nested fixpoint IS `fix2 F`. -/
theorem fix2_unique (F : Operator (Stream a) (Stream a)) (hstrict : strict2 F)
    (α : Stream (Stream a)) (h_fix : α = F α) : α = fix2 F := by
  apply Dbsp.fixpoints2_unique F hstrict α (fix2 F) h_fix
  exact fix2_eq F hstrict

/-- The pointwise-lifted delay is nested-strict. -/
theorem lifting_delay_strict2 : strict2 (lifting (@delay a _)) := by
  intro s s' n t heq
  show delay (s n) t = delay (s' n) t
  cases t with
  | zero => rfl
  | succ t =>
    show s n t = s' n t
    exact heq n (Nat.le_refl n) t (Nat.lt_succ_self t)

omit [Zero a] in
@[simp]
theorem causal_nested_const (c : Stream (Stream b)) :
    causal_nested (fun (_ : Stream (Stream a)) => c) := by
  intro s s' n t heq
  rfl

omit [Zero a] in
theorem causal_nested_id : causal_nested (fun (x : Stream (Stream a)) => x) := by
  intro s s' n t heq
  exact heq n (Nat.le_refl n) t (Nat.le_refl t)

omit [Zero a] in
theorem causal_nested_comp (Q1 : Operator (Stream b) (Stream c)) (Q2 : Operator (Stream a) (Stream b)) :
    causal_nested Q1 → causal_nested Q2 → causal_nested (fun s => Q1 (Q2 s)) := by
  intro h1 h2 s s' n t heq
  apply h1
  intro n₁ hn₁ t₁ ht₁
  apply h2
  intro n₂ hn₂ t₂ ht₂
  exact heq n₂ (Nat.le_trans hn₂ hn₁) t₂ (Nat.le_trans ht₂ ht₁)

omit [Zero a] in
theorem causal_nested_lifting (Q : Operator a b) : Causal Q → causal_nested (lifting Q) := by
  intro h s s' n t heq
  show Q (s n) t = Q (s' n) t
  apply h
  intro t' ht'
  exact heq n (Nat.le_refl n) t' ht'

end Fix2

/-! ## Nested causality and the cycle theorems -/

section Cycle

variable [AddCommGroup a] [AddCommGroup b]

omit [AddCommGroup a] in
/-- The lifted two-input cycle body is nested-strict: the lifted delay is
    `lifting_delay_strict2`, and `lifting2 T s` is nested-causal in its
    second argument by `causal2`. -/
theorem lifting_cycle_body_strict2 (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    ∀ s : Stream (Stream a), strict2 (fun α : Stream (Stream b) => lifting2 T s (lifting delay α)) := by
  rw [causal2] at hcausal
  intro s s1 s2 n t heq
  show T (s n) (delay (s1 n)) t = T (s n) (delay (s2 n)) t
  apply hcausal
  · exact fun i hi => rfl
  · intro i hi
    cases i with
    | zero => rfl
    | succ j => exact heq n (Nat.le_refl n) j (Nat.lt_of_succ_le hi)

/-- The partial sums telescope down a row when the row itself is a stream. -/
theorem sum_vals_nested (s : Stream (Stream a)) (n t : Nat) :
    sumVals s n t = sumVals (fun k => s k t) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumVals, Pi.add_apply]
    rw [ih]

private theorem sumVals_congr (f g : Nat → a) (n : Nat) (h : ∀ k, k < n → f k = g k) :
    sumVals f n = sumVals g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hsum : sumVals f n = sumVals g n :=
      ih (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    show f n + sumVals f n = g n + sumVals g n
    rw [h n (Nat.lt_succ_self n), hsum]

/-- `I (z⁻¹ s) = z⁻¹ (I s)` at one more level: integrating the delayed
    stream is delaying the integrated stream. -/
theorem integral_lift_time_invariant (s : Stream (Stream a)) :
    I (lifting delay s) = lifting delay (I s) := by
  funext n t
  rw [integral_sum_vals (lifting delay s) n]
  change sumVals (lifting delay s) (n + 1) t = delay ((I s) n) t
  by_cases ht : t = 0
  · subst ht
    rw [sum_vals_nested]
    rw [sumVals_zero (fun k => (lifting delay s) k 0) (fun _ => by simp) (n + 1)]
    simp
  · have ht' : 0 < t := Nat.pos_of_ne_zero ht
    rw [sum_vals_nested]
    change sumVals (fun k => delay (s k) t) (n + 1) = delay ((I s) n) t
    rw [show (fun k : Nat => delay (s k) t) = (fun k : Nat => s k (t - 1))
          from funext (fun k => delay_sub_1 (s k) t ht')]
    rw [delay_sub_1 ((I s) n) t ht']
    rw [integral_sum_vals s n, sum_vals_nested s (n + 1) (t - 1)]

/-- `↑↑I (↑↑z⁻¹ s) = ↑↑z⁻¹ (↑↑I s)`: row-wise time invariance of the
    integral. -/
theorem lift_integral_lift_time_invariant (s : Stream (Stream a)) :
    lifting I (lifting delay s) = lifting delay (lifting I s) := by
  funext n t
  show I (delay (s n)) t = delay (I (s n)) t
  exact congr_fun (integral_time_invariant (s n)) t

/-- The lifted delay is linear. -/
theorem lifting_delay_linear : Linear (lifting (@delay a _)) := by
  intro x y
  funext t u
  show delay ((x + y) t) u = delay (x t) u + delay (y t) u
  cases u <;> simp

/-- Causality of I in the nested sense, stated at fixed column `t`. -/
theorem integral_causal_nested' (s1 s2 : Stream (Stream a)) (n t : Nat)
    (heq : ∀ n' ≤ n, s1 n' t = s2 n' t) : I s1 n t = I s2 n t := by
  rw [integral_sum_vals s1 n, integral_sum_vals s2 n]
  rw [sum_vals_nested, sum_vals_nested]
  exact sumVals_congr (fun k => s1 k t) (fun k => s2 k t) (n + 1)
    (fun k hk => heq k (Nat.le_of_lt_succ hk))

@[simp]
theorem integral_causal_nested : causal_nested (@I (Stream a) _) := by
  intro s1 s2 n t heq
  apply integral_causal_nested'
  intro n' hn'
  exact heq n' hn' t (Nat.le_refl t)

@[simp]
theorem derivative_causal_nested : causal_nested (@D (Stream a) _) := by
  intro s1 s2 n t heq
  show s1 n t - delay s1 n t = s2 n t - delay s2 n t
  have hdel : delay s1 n t = delay s2 n t := by
    cases n with
    | zero => simp
    | succ m => exact heq m (Nat.le_succ m) t (Nat.le_refl t)
  rw [heq n (Nat.le_refl n) t (Nat.le_refl t), hdel]

omit [AddCommGroup a] in
/-- The nested cycle body (`α ↦ T s (z⁻¹ α)`) is nested-strict. -/
theorem cycle_body_strict2 (T : Operator2 a (Stream b) (Stream b)) (s : Stream a) :
    causal_nested (T s) → strict2 (fun α : Stream (Stream b) => T s (lifting delay α)) := by
  intro hcausal s1 s2 n t hseq
  show T s (lifting delay s1) n t = T s (lifting delay s2) n t
  apply hcausal
  intro n₁ hn₁ t₁ ht₁
  show delay (s1 n₁) t₁ = delay (s2 n₁) t₁
  apply lifting_delay_strict2
  intro n' hn' t' ht'
  exact hseq n' (Nat.le_trans hn' hn₁) t' (Nat.lt_of_lt_of_le ht' ht₁)

/-- The incrementalized nested cycle body is nested-strict. -/
theorem cycle_body_incremental_strict2 (T : Operator2 a (Stream b) (Stream b)) (s : Stream a) :
    causal_nested (T (I s)) → strict2 (fun α : Stream (Stream b) => incremental2 T s (lifting delay α)) := by
  intro hcausal s1 s2 n t hseq
  show D (T (I s) (I (lifting delay s1))) n t = D (T (I s) (I (lifting delay s2))) n t
  apply derivative_causal_nested
  intro n₁ hn₁ t₁ ht₁
  apply hcausal
  intro n₂ hn₂ t₂ ht₂
  apply integral_causal_nested
  intro n₃ hn₃ t₃ ht₃
  show delay (s1 n₃) t₃ = delay (s2 n₃) t₃
  apply lifting_delay_strict2
  intro n₄ hn₄ t₄ ht₄
  exact hseq n₄ (Nat.le_trans (Nat.le_trans (Nat.le_trans hn₄ hn₃) hn₂) hn₁) t₄
    (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le ht₄ ht₃) (Nat.le_trans ht₂ ht₁))

/-- **The lifted cycle is the nested cycle**: lifting the one-input
    feedback loop is running its two-input version one level deeper. -/
theorem lifting_cycle (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    lifting (fun s : Stream a => fix (fun α : Stream b => T s (delay α))) =
      fun s : Stream (Stream a) =>
        fix2 (fun α : Stream (Stream b) => lifting2 T s (lifting delay α)) := by
  funext s
  apply fix2_unique
  · apply lifting_cycle_body_strict2
    exact hcausal
  · funext t
    show fix (fun α : Stream b => T (s t) (delay α))
       = T (s t) (delay (fix (fun α : Stream b => T (s t) (delay α))))
    exact fix_eq (fun α : Stream b => T (s t) (delay α)) (cycle_body_strict T hcausal (s t))

/-- **The nested cascade theorem**: a two-level feedback loop's
    incremental form is the nested loop of the incrementalized body. The
    delta engine may run recursive rules whose fixpoint state is itself a
    stream entirely on deltas; the result equals differentiating the
    batch nested fixpoint. -/
theorem cycle2_incremental (T : Operator2 a (Stream b) (Stream b))
    (hcausal : ∀ s : Stream a, causal_nested (T s)) :
    incremental (fun s : Stream a => fix2 (fun α : Stream (Stream b) => T s (lifting delay α))) =
      fun s : Stream a => fix2 (fun α : Stream (Stream b) => incremental2 T s (lifting delay α)) := by
  funext s
  apply fix2_unique
  · apply cycle_body_incremental_strict2
    exact hcausal (I s)
  · show D (fix2 (fun α : Stream (Stream b) => T (I s) (lifting delay α)))
      = D (T (I s) (I (lifting delay (D (fix2 (fun α : Stream (Stream b) => T (I s) (lifting delay α)))))))
    rw [integral_lift_time_invariant, derivative_integral]
    congr 1
    exact fix2_eq (fun α : Stream (Stream b) => T (I s) (lifting delay α))
      (cycle_body_strict2 T (I s) (hcausal (I s)))

end Cycle

end Dbsp

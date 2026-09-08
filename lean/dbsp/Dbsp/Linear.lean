/-
# Dbsp.Linear — linearity, differentiation, integration

Ports tchajed/database-stream-processing-theory `src/linear.lean` (Lean 3)
to Lean 4 (notes/lean/lean-v3.md Part 3). Requires the streams to carry an
`AddCommGroup` (mathlib Pi instances, see `Dbsp.Stream`).

The crown jewels — the D/I inverse pair:

- `derivative_integral` : I (D s) = s — integrating the differences
  recovers the stream. In flatland terms: replaying the journal from zero
  reconstructs the world. This is the journal/checkpoint license.
- `integral_derivative` : D (I s) = s — differentiating the accumulated
  stream recovers the deltas.
- `derivative_integral_inverse` : α = I s ↔ D α = s — the two directions
  are each other's unique inverse.

The `Bilinear` predicate is ported (needed by Dbsp.Relational for the
product/join/intersect bilinearity theorems); the source's `lifting2`
bilinearity and the two alternative `derivative_integral` proofs stay
deferred.
-/

import Dbsp.Certs
import Dbsp.Operators
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Abel

namespace Dbsp

variable {a b : Type} [AddCommGroup a] [AddCommGroup b]

/-! ## Linearity -/

/-- An operator is linear when it is a group homomorphism on streams. -/
def Linear (S : Operator a b) : Prop := ∀ x y, S (x + y) = S x + S y

theorem linear_add {S : Operator a b} (h : Linear S) :
    ∀ s1 s2, S (s1 + s2) = S s1 + S s2 := h

theorem linear_zero {S : Operator a b} (h : Linear S) : S 0 = 0 := by
  have h0 : S 0 = S 0 + S 0 := by
    have := h 0 0
    rwa [add_zero] at this
  exact (add_left_cancel (a := S 0) (b := 0) (c := S 0) (by rwa [add_zero])).symm

theorem linear_neg {S : Operator a b} (h : Linear S) : ∀ s, S (-s) = -S s := by
  intro s
  apply eq_neg_of_add_eq_zero_left
  rw [← h, neg_add_cancel, linear_zero h]

theorem linear_sub {S : Operator a b} (h : Linear S) :
    ∀ s1 s2, S (s1 - s2) = S s1 - S s2 := by
  intro s1 s2
  rw [sub_eq_add_neg, h, linear_neg h, sub_eq_add_neg]

/-- A function of two arguments is bilinear if it is linear in each argument
    separately (holding the other constant). A classic example is
    multiplication. This is the source's general `bilinear` — it is not
    stream-specific; the stream/operator version is `incremental2` in
    Dbsp.Incremental. -/
def Bilinear {a b c : Type} [AddCommGroup a] [AddCommGroup b] [AddCommGroup c]
    (f : a → b → c) : Prop :=
  (∀ x1 x2 y, f (x1 + x2) y = f x1 y + f x2 y) ∧
  (∀ x y1 y2, f x (y1 + y2) = f x y1 + f x y2)

/-- LTI: linear and time-invariant. -/
def Lti (S : Operator a b) : Prop := Linear S ∧ TimeInvariant S

theorem delay_time_invariant : TimeInvariant (@delay a _) := fun _ => rfl

theorem lifting_linear (f : a → b) (hlin : ∀ x y, f (x + y) = f x + f y) :
    Linear (lifting f) := by
  intro x y
  funext t
  exact hlin _ _

/-- A lifted additive function is LTI. -/
theorem lifting_lti (f : a → b) (hlin : ∀ x y, f (x + y) = f x + f y) :
    Lti (lifting f) := by
  refine ⟨lifting_linear f hlin, lifting_time_invariant f ?_⟩
  have h0 : f 0 = f 0 + f 0 := by rw [← hlin 0 0, add_zero]
  exact (add_left_cancel (a := f 0) (b := 0) (c := f 0) (by rwa [add_zero])).symm

theorem bilinear_sub_1 {α β γ : Type} [AddCommGroup α] [AddCommGroup β] [AddCommGroup γ]
    {f : α → β → γ} (hblin : Bilinear f) :
    ∀ x1 x2 y, f (x1 - x2) y = f x1 y - f x2 y := by
  intro x1 x2 y
  have h0 : f 0 y = 0 := by
    have h := hblin.1 0 0 y
    rw [add_zero] at h
    exact (add_left_cancel (a := f 0 y) (b := 0) (c := f 0 y) (by rwa [add_zero])).symm
  have hneg : f (-x2) y = -(f x2 y) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← hblin.1 (-x2) x2 y, neg_add_cancel, h0]
  rw [sub_eq_add_neg, hblin.1, hneg, sub_eq_add_neg]

theorem bilinear_sub_2 {α β γ : Type} [AddCommGroup α] [AddCommGroup β] [AddCommGroup γ]
    {f : α → β → γ} (hblin : Bilinear f) :
    ∀ x y1 y2, f x (y1 - y2) = f x y1 - f x y2 := by
  intro x y1 y2
  have h0 : f x 0 = 0 := by
    have h := hblin.2 x 0 0
    rw [add_zero] at h
    exact (add_left_cancel (a := f x 0) (b := 0) (c := f x 0) (by rwa [add_zero])).symm
  have hneg : f x (-y2) = -(f x y2) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← hblin.2 x (-y2) y2, neg_add_cancel, h0]
  rw [sub_eq_add_neg, hblin.2, hneg, sub_eq_add_neg]

/-- A pointwise-bilinear function lifts to a stream-bilinear operator. -/
theorem lifting_bilinear {α β γ : Type} [AddCommGroup α] [AddCommGroup β] [AddCommGroup γ]
    (f : α → β → γ) (h : Bilinear f) : Bilinear (lifting2 f) := by
  constructor
  · intro x1 x2 y; funext t; exact h.1 _ _ _
  · intro x1 x2 y; funext t; exact h.2 _ _ _

theorem delay_linear : Linear (@delay a _) := by
  intro x y
  funext t
  cases t with
  | zero => simp
  | succ n => rfl

/-! ## Feedback -/

/-- The feedback loop: `feedback S s` is the unique fixpoint of
    `α = S (s + z⁻¹α)`. The integral operator `I` is `feedback id`. -/
def feedback (S : Operator a a) : Operator a a :=
  fun s => fix (fun α => S (s + delay α))

/-- With causal S, the feedback body is strict — the loop is well-formed. -/
theorem feedback_strict {S : Operator a a} (hcausal : Causal S) (s : Stream a) :
    Strict (fun α => S (s + delay α)) := by
  intro α β n hagree
  apply hcausal
  intro i hi
  show s i + delay α i = s i + delay β i
  cases i with
  | zero => rfl
  | succ j => rw [delay_succ, delay_succ, hagree j (Nat.lt_of_succ_le hi)]

/-- The feedback loop unfolds once: `feedback S s = S (s + z⁻¹(feedback S s))`. -/
theorem feedback_unfold (S : Operator a a) (hcausal : Causal S) (s : Stream a) :
    feedback S s = S (s + delay (feedback S s)) :=
  fix_eq _ (feedback_strict hcausal s)

theorem agree_upto_respects_add (s1 s2 s1' s2' : Stream a) (n : Nat) :
    agreeUpto n s1 s1' → agreeUpto n s2 s2' → agreeUpto n (s1 + s2) (s1' + s2') := by
  intro h1 h2 t ht
  show s1 t + s2 t = s1' t + s2' t
  rw [h1 t ht, h2 t ht]

theorem agree_upto_respects_sub (s1 s2 s1' s2' : Stream a) (n : Nat) :
    agreeUpto n s1 s1' → agreeUpto n s2 s2' → agreeUpto n (s1 - s2) (s1' - s2') := by
  intro h1 h2 t ht
  show s1 t - s2 t = s1' t - s2' t
  rw [h1 t ht, h2 t ht]

/-- Feedback of a causal operator is causal. -/
theorem feedback_causal (S : Operator a a) (hcausal : Causal S) :
    Causal (feedback S) := by
  have hag : ∀ s1 s2 n, agreeUpto n s1 s2 → agreeUpto n (S s1) (S s2) :=
    (causal_to_agree S).mp hcausal
  rw [causal_to_agree]
  intro s1 s2 n heq
  induction n generalizing s1 s2 with
  | zero =>
    rw [feedback_unfold S hcausal s1, feedback_unfold S hcausal s2]
    apply hag
    intro t ht
    rw [Nat.le_zero.mp ht]
    show s1 0 + delay (feedback S s1) 0 = s2 0 + delay (feedback S s2) 0
    simp only [delay_zero]
    rw [heq 0 (Nat.le_refl 0)]
  | succ n ih =>
    rw [feedback_unfold S hcausal s1, feedback_unfold S hcausal s2]
    apply hag
    apply agree_upto_respects_add _ _ _ _ _ heq
    apply delay_succ_upto
    exact ih _ _ (agree_upto_weaken s1 s2 (n + 1) n heq (Nat.le_succ n))

/-- Feedback of a causal, time-invariant operator is time-invariant. -/
theorem feedback_time_invariant (S : Operator a a) (hcausal : Causal S)
    (hti : TimeInvariant S) : TimeInvariant (feedback S) := by
  intro s
  rw [agree_everywhere_eq]
  intro n
  induction n with
  | zero =>
    rw [agree_upto_0]
    have h0 : feedback S (delay s) 0 = S (delay s + delay 0) 0 := rfl
    rw [h0]
    have hds : (delay s + delay (0 : Stream a)) = delay s := by
      funext i
      show delay s i + delay (0 : Stream a) i = delay s i
      cases i with
      | zero => simp
      | succ j => simp
    rw [hds, time_invariant_t hti]
    simp only [delay_zero]
  | succ n ih =>
    rw [feedback_unfold S hcausal (delay s)]
    have hdl : delay s + delay (feedback S (delay s)) = delay (s + feedback S (delay s)) :=
      (delay_linear s (feedback S (delay s))).symm
    rw [hdl, hti]
    apply delay_succ_upto
    have h : agreeUpto n (s + feedback S (delay s)) (s + delay (feedback S s)) :=
      agree_upto_respects_add _ _ _ _ _ (agree_refl _ _) ih
    apply agree_trans _ _ _ (causal_respects_agreeUpto S hcausal _ _ n h)
    rw [← feedback_unfold S hcausal s]

/-- Feedback of an LTI operator is linear. -/
theorem feedback_linear (S : Operator a a) (hcausal : Causal S) (hlti : Lti S) :
    Linear (feedback S) := by
  intro s1 s2
  symm
  apply fix_unique _ (feedback_strict hcausal (s1 + s2))
  show feedback S s1 + feedback S s2
    = S ((s1 + s2) + delay (feedback S s1 + feedback S s2))
  rw [delay_linear (feedback S s1) (feedback S s2)]
  have hreshuffle :
      (s1 + s2) + (delay (feedback S s1) + delay (feedback S s2))
        = (s1 + delay (feedback S s1)) + (s2 + delay (feedback S s2)) := by
    abel
  rw [hreshuffle, hlti.1]
  rw [← feedback_unfold S hcausal s1, ← feedback_unfold S hcausal s2]

/-! ## Differentiation -/

/-- The derivative operator D: `(D s)(t) = s(t) - s(t-1)`, `(D s)(0) = s(0)`.
    Produces the stream of changes. The journal is D applied to the world
    history. -/
def D : Operator a a := fun s => s - delay s

@[simp] theorem derivative_causal : Causal (@D a _) := by
  intro s s' t hpre
  show s t - delay s t = s' t - delay s' t
  cases t with
  | zero => simp only [delay_zero, sub_zero]; exact hpre 0 (Nat.le_refl 0)
  | succ n =>
    simp only [delay_succ]
    rw [hpre (n + 1) (Nat.le_refl _), hpre n (Nat.le_succ n)]

theorem derivative_linear : Linear (@D a _) := by
  intro x y
  show (x + y) - delay (x + y) = (x - delay x) + (y - delay y)
  rw [delay_linear x y]
  abel

theorem derivative_time_invariant : TimeInvariant (@D a _) := by
  intro s
  show delay s - delay (delay s) = delay (s - delay s)
  funext t
  cases t with
  | zero => simp
  | succ n => rfl

theorem derivative_lti : Lti (@D a _) := ⟨derivative_linear, derivative_time_invariant⟩

@[simp] theorem derivative_0 (s : Stream a) : D s 0 = s 0 := by
  show s 0 - delay s 0 = s 0
  simp

/-- The closed form of D away from zero. -/
theorem derivative_succ (s : Stream a) (t : Nat) : D s (t + 1) = s (t + 1) - s t := rfl

@[simp] theorem derivative_zpp : D (0 : Stream a) = 0 := by
  funext t
  show (0 : Stream a) t - delay 0 t = 0
  cases t <;> simp [delay_succ]

/-! ## Integration -/

/-- The integral operator I: sums the changes so far. `I s = s + z⁻¹(I s)`,
    the unique fixpoint. Checkpoints are I applied to the journal. -/
def I : Operator a a := feedback id

protected theorem id_causal : Causal (@id (Stream a)) := by
  intro s s' t hpre
  exact hpre t (Nat.le_refl t)

theorem integral_causal : Causal (@I a _) :=
  feedback_causal id Dbsp.id_causal

theorem integral_unfold (s : Stream a) : I s = s + delay (I s) :=
  feedback_unfold id Dbsp.id_causal s

theorem id_linear : Linear (@id (Stream a)) := fun _ _ => rfl

theorem id_time_invariant : TimeInvariant (@id (Stream a)) := fun _ => rfl

protected theorem id_lti : Lti (@id (Stream a)) := ⟨id_linear, id_time_invariant⟩

/-- Feedback preserves the LTI property. -/
theorem feedback_lti (S : Operator a a) (hcausal : Causal S) (hlti : Lti S) :
    Lti (feedback S) :=
  ⟨feedback_linear S hcausal hlti, feedback_time_invariant S hcausal hlti.2⟩

theorem integral_lti : Lti (@I a _) := feedback_lti id Dbsp.id_causal Dbsp.id_lti

theorem integral_linear : Linear (@I a _) := integral_lti.1

theorem integral_time_invariant : TimeInvariant (@I a _) := integral_lti.2

/-- The sum of `s 0 .. s (n-1)` — the closed form of I, offset by 1
    (`integral_sum_vals`). -/
def sumVals (s : Stream a) : Nat → a
  | 0 => 0
  | n + 1 => s n + sumVals s n

@[simp] theorem sumVals_0 (s : Stream a) : sumVals s 0 = 0 := rfl
@[simp] theorem sumVals_1 (s : Stream a) : sumVals s 1 = s 0 := by
  show s 0 + 0 = s 0
  exact add_zero _

@[simp] theorem sumVals_zero (s : Stream a) (hz : ∀ n, s n = 0) (n : Nat) :
    sumVals s n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => show s n + sumVals s n = 0; rw [hz n, ih, add_zero]

/-- The derivative away from zero, in predecessor form. -/
theorem derivative_difference (s : Stream a) (t : Nat) (h : 0 < t) :
    D s t = s t - s (t - 1) := by
  cases t with
  | zero => exact absurd h (Nat.lt_irrefl 0)
  | succ n => rfl

@[simp] theorem integral_0 (s : Stream a) : I s 0 = s 0 := by
  have h := congr_fun (integral_unfold s) 0
  show I s 0 = s 0
  rw [h]
  show s 0 + delay (I s) 0 = s 0
  simp

theorem integral_sum_vals (s : Stream a) (n : Nat) : I s n = sumVals s (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := congr_fun (integral_unfold s) (n + 1)
    show I s (n + 1) = s (n + 1) + sumVals s (n + 1)
    rw [h]
    show s (n + 1) + delay (I s) (n + 1) = s (n + 1) + sumVals s (n + 1)
    rw [delay_succ, ih]

/-- Telescoping: the sums of the differences are the values. -/
theorem sum_vals_succ_n (s : Stream a) (t : Nat) : sumVals (D s) (t + 1) = s t := by
  induction t with
  | zero =>
    show D s 0 + 0 = s 0
    rw [add_zero, derivative_0]
  | succ t ih =>
    show D s (t + 1) + sumVals (D s) (t + 1) = s (t + 1)
    rw [derivative_succ, ih]
    show s (t + 1) - s t + s t = s (t + 1)
    exact sub_add_cancel _ _

/-- **I ∘ D = id** — integrating the differences recovers the stream.
    The journal is complete: replaying deltas from zero reconstructs the
    world. -/
@[simp, cert] theorem derivative_integral (s : Stream a) : I (D s) = s := by
  funext t
  rw [integral_sum_vals, sum_vals_succ_n]

/-- **D ∘ I = id** — differentiating the accumulation recovers the deltas. -/
@[simp, cert] theorem integral_derivative (s : Stream a) : D (I s) = s := by
  show I s - delay (I s) = s
  calc I s - delay (I s)
      = (s + delay (I s)) - delay (I s) := by
        nth_rewrite 1 [integral_unfold s]
        rfl
    _ = s := add_sub_cancel_right _ _

/-- The inverse pair, stated as an equivalence: α is the integral of s
    iff s is the derivative of α. World history ↔ journal. -/
theorem derivative_integral_inverse (α s : Stream a) : α = I s ↔ D α = s :=
  ⟨fun h => by subst h; exact integral_derivative s,
   fun h => by subst h; exact (derivative_integral α).symm⟩

theorem i_d_comp : (I ∘ D : Stream a → Stream a) = id := by
  funext s
  exact derivative_integral s

theorem d_i_comp : (D ∘ I : Stream a → Stream a) = id := by
  funext s
  exact integral_derivative s

/-! ## The product commutations (needed by Dbsp.Circuit)

The streams of pairs plays well with D, I, and pointwise lifting —
`derivative_sprod`, `integral_sprod`, `integral_lift_comm` and the
projection corollaries `integral_fst_comm` / `integral_snd_comm`. The
circuit incrementalize theorem pushes D and I through the `par`
constructor on exactly these grounds. -/

/-- An additive function preserves zero. -/
theorem lifting_zero (f : a → b) (hlin : ∀ x y, f (x + y) = f x + f y) : f 0 = 0 := by
  have h0 : f 0 = f 0 + f 0 := by
    rw [← hlin 0 0, add_zero]
  exact (add_left_cancel (a := f 0) (b := 0) (c := f 0) (by rwa [add_zero])).symm

/-- `sumVals` commutes with the stream pairing operator. -/
theorem sumVals_sprod (s1 : Stream a) (s2 : Stream b) (n : Nat) :
    sumVals (sprod (s1, s2)) n = (sumVals s1 n, sumVals s2 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      sumVals (sprod (s1, s2)) (n + 1)
          = sprod (s1, s2) n + sumVals (sprod (s1, s2)) n := rfl
      _ = (s1 n, s2 n) + (sumVals s1 n, sumVals s2 n) := by
          rw [ih]
          rfl
      _ = (s1 n + sumVals s1 n, s2 n + sumVals s2 n) := rfl
      _ = (sumVals s1 (n + 1), sumVals s2 (n + 1)) := rfl

/-- Summing the pointwise lifting is lifting the partial sums. -/
theorem sumVals_lifting (f : a → b) (s : Stream a) (n : Nat)
    (hlin : ∀ x y, f (x + y) = f x + f y) :
    sumVals (lifting f s) n = f (sumVals s n) := by
  induction n with
  | zero =>
    simp only [sumVals_0]
    exact (lifting_zero f hlin).symm
  | succ n ih =>
    simp only [sumVals, lifting_eq]
    rw [ih]
    exact (hlin (s n) (sumVals s n)).symm

/-- D commutes with the stream pairing operator. -/
theorem derivative_sprod (s1 : Stream a) (s2 : Stream b) :
    D (sprod (s1, s2)) = sprod (D s1, D s2) := by
  funext t
  cases t with
  | zero => simp [D]
  | succ n =>
    show (s1 (n + 1), s2 (n + 1)) - (s1 n, s2 n)
      = (s1 (n + 1) - s1 n, s2 (n + 1) - s2 n)
    rfl

/-- I commutes with the stream pairing operator. -/
theorem integral_sprod (s1 : Stream a) (s2 : Stream b) :
    I (sprod (s1, s2)) = sprod (I s1, I s2) := by
  funext t
  rw [integral_sum_vals (sprod (s1, s2)) t]
  change sumVals (sprod (s1, s2)) (t + 1) = (I s1 t, I s2 t)
  rw [integral_sum_vals s1 t, integral_sum_vals s2 t]
  exact sumVals_sprod s1 s2 (t + 1)

/-- I commutes with a pointwise lifting of an additive function. -/
theorem integral_lift_comm (f : a → b) (s : Stream a)
    (hlin : ∀ x y, f (x + y) = f x + f y) :
    I (lifting f s) = lifting f (I s) := by
  funext t
  rw [integral_sum_vals (lifting f s) t]
  change sumVals (lifting f s) (t + 1) = f (I s t)
  rw [integral_sum_vals s t]
  exact sumVals_lifting f s (t + 1) hlin

/-- I commutes with the first stream projection. -/
theorem integral_fst_comm (s : Stream (a × b)) :
    I (lifting Prod.fst s) = lifting Prod.fst (I s) := by
  exact integral_lift_comm Prod.fst s (fun x y => by simp)

/-- I commutes with the second stream projection. -/
theorem integral_snd_comm (s : Stream (a × b)) :
    I (lifting Prod.snd s) = lifting Prod.snd (I s) := by
  exact integral_lift_comm Prod.snd s (fun x y => by simp)

end Dbsp

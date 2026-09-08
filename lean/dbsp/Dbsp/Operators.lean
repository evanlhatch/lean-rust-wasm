/-
# Dbsp.Operators — causality, strictness, and the fixpoint

Ports tchajed/database-stream-processing-theory `src/operators.lean`
(Lean 3) to Lean 4 (notes/lean/lean-v3.md Part 3).

The crown jewels, ported with their proofs:

- `fix_eq` — a STRICT operator's `fix` is a fixpoint (`fix F = F (fix F)`).
- `fix_unique` — and it is THE fixpoint. In flatland terms: any schedule
  that computes a fixpoint of the same strict operator computes the same
  answer. This is the central lemma of the stage-walker ≡ queue-cascade
  equivalence (SPEC-core.md §7.4).

## The strictness discipline (flatland reading)

An operator is strict when its output at pass n+1 depends only on inputs
from passes ≤ n. The cascade's kernel wiring is strict BY CONSTRUCTION
(deltas apply between passes). The exception — self-read pointwise kernels
(`x = f(x)`, ARCH Part 5's row-order contract) — is non-strict and carries
its own legality argument; it is NOT covered by `fix_unique`.
-/

import Dbsp.Certs
import Dbsp.Stream

namespace Dbsp

/-- An operator is a function between streams. -/
abbrev Operator (a b : Type) := Stream a → Stream b

/-- A two-input operator (joins etc.). Isomorphic to `Operator (a × b) c`;
    the curried form is easier to use. -/
abbrev Operator2 (a b c : Type) := Stream a → Stream b → Stream c

/-- Pointwise lifting of a function to a stream operator. -/
def lifting (f : a → b) : Operator a b := fun s n => f (s n)

/-- Pointwise lifting of a two-argument function (the source's ↑²). -/
def lifting2 (f : a → b → c) : Operator2 a b c := fun s1 s2 n => f (s1 n) (s2 n)

@[simp] theorem lifting_eq (f : a → b) (s : Stream a) (n : Nat) :
    lifting f s n = f (s n) := rfl

/-- Causal: output at time `t` depends only on inputs at times ≤ t. -/
def Causal (S : Operator a b) : Prop :=
  ∀ s s' t, (∀ i, i ≤ t → s i = s' i) → S s t = S s' t

/-- Strict (strictly causal): output at time `t` depends only on inputs at
    times < t. The feedback edge of the cascade goes through a delay, so
    kernel compositions are strict by construction. -/
def Strict (S : Operator a b) : Prop :=
  ∀ s s' t, (∀ i, i < t → s i = s' i) → S s t = S s' t

/-- Strict operators have a unique output at time 0 (they may not look at
    the input at time 0). -/
theorem strict_unique_zero (S : Operator a b) (h : Strict S) :
    ∀ s s', S s 0 = S s' 0 := by
  intro s s'
  apply h
  intro i hlt
  exact absurd hlt (Nat.not_lt_zero i)

theorem strict_causal_to_causal (S : Operator a b) : Strict S → Causal S := by
  intro hs s s' t hpre
  apply hs
  intro i hlt
  exact hpre i (Nat.le_of_lt hlt)

/-- The delay operator z⁻¹: shift the stream one tick into the future. -/
def delay [Zero a] (s : Stream a) : Stream a
  | 0 => 0
  | n + 1 => s n

@[simp] theorem delay_zero [Zero a] (s : Stream a) : delay s 0 = 0 := rfl
@[simp] theorem delay_succ [Zero a] (s : Stream a) (n : Nat) : delay s (n + 1) = s n := rfl

theorem delay_strict [Zero a] : Strict (@delay a _) := by
  intro s s' t hpre
  cases t with
  | zero => rfl
  | succ n => exact hpre n (Nat.lt_succ_self n)

/-- causal ∘ strict is strict. -/
theorem causal_strict_strict (F : Operator a b) (hstrict : Strict F)
    (T : Operator b c) (hcausal : Causal T) : Strict (fun α => T (F α)) := by
  intro s1 s2 n hagree
  apply hcausal
  intro i hle
  apply hstrict
  intro j hjlt
  exact hagree j (Nat.lt_of_lt_of_le hjlt hle)

/-- strict ∘ causal is strict. -/
theorem strict_causal_strict (F : Operator a b) (hcausal : Causal F)
    (T : Operator b c) (hstrict : Strict T) : Strict (fun α => T (F α)) := by
  intro s1 s2 n hagree
  apply hstrict
  intro i hlt
  apply hcausal
  intro j hjle
  exact hagree j (Nat.lt_of_le_of_lt hjle hlt)

/-- Strictness extends agreement by one step through the operator. -/
theorem agree_upto_strict_extend (S : Operator a b) (hstrict : Strict S)
    (s s' : Stream a) (n : Nat) :
    agreeUpto n s s' → agreeUpto (n + 1) (S s) (S s') := by
  intro h t ht
  apply hstrict
  intro i hi
  exact h i (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hi ht))

/-- The n-th iterate: `nthIter F n` is F applied to a zero stream n+1 times.
    (The source's `nth`; we apply F at the bottom so `fix F 0 = F 0 0` —
    the paper's generalization for operators without `F 0 0 = 0`.) -/
def nthIter [Zero a] (F : Operator a a) : Nat → Stream a
  | 0 => F 0
  | n + 1 => F (nthIter F n)

@[simp] theorem nthIter_zero [Zero a] (F : Operator a a) : nthIter F 0 = F 0 := rfl
@[simp] theorem nthIter_succ [Zero a] (F : Operator a a) (n : Nat) :
    nthIter F (n + 1) = F (nthIter F n) := rfl

/-- The fixpoint of a strict operator: `fix F t` is the t-th iterate read at
    time t — the t-th iterate is correct up to time t. -/
def fix [Zero a] (F : Operator a a) : Stream a := fun t => nthIter F t t

theorem fix_zero [Zero a] (F : Operator a a) : fix F 0 = F 0 0 := rfl

/-- The heart of the fixpoint theorems: at time n, the n-th iterate, the
    fixpoint, and one more application of F all agree. -/
private theorem nth_fix_agree_aux [Zero a] (F : Operator a a) (hstrict : Strict F)
    (n : Nat) : agreeUpto n (nthIter F n) (fix F) ∧ agreeUpto n (fix F) (F (fix F)) := by
  induction n with
  | zero =>
    rw [agree_upto_0, agree_upto_0]
    constructor
    · rfl
    · show fix F 0 = F (fix F) 0
      have h0 := strict_unique_zero F hstrict 0 (fix F)
      -- F 0 0 = F (fix F) 0; fix F 0 = F 0 0 definitionally
      exact h0
  | succ n ih =>
    obtain ⟨h_fix, h_unfold⟩ := ih
    have h : agreeUpto (n + 1) (F (nthIter F n)) (F (fix F)) :=
      agree_upto_strict_extend F hstrict _ _ n h_fix
    have h2 : agreeUpto (n + 1) (fix F) (F (fix F)) := by
      apply agree_upto_extend n _ _ h_unfold
      show fix F (n + 1) = F (fix F) (n + 1)
      show nthIter F (n + 1) (n + 1) = F (fix F) (n + 1)
      rw [nthIter_succ]
      exact h (n + 1) (Nat.le_refl _)
    constructor
    · show agreeUpto (n + 1) (nthIter F (n + 1)) (fix F)
      rw [nthIter_succ]
      exact agree_trans _ _ _ h (agree_symm _ _ _ h2)
    · exact h2

/-- `fix_eq` — the key characterization: for strict F, `fix F` is a fixpoint. -/
theorem fix_eq [Zero a] (F : Operator a a) (hstrict : Strict F) :
    fix F = F (fix F) := by
  funext t
  have h := (nth_fix_agree_aux F hstrict t).2
  exact h t (Nat.le_refl t)

/-- Fixpoints of a strict operator are unique. -/
protected theorem fixpoints_unique [Zero a] (F : Operator a a) (hstrict : Strict F)
    (α β : Stream a) : α = F α → β = F β → α = β := by
  intro hα hβ
  rw [agree_everywhere_eq]
  intro n
  induction n with
  | zero =>
    rw [agree_upto_0, hα, hβ]
    exact strict_unique_zero F hstrict α β
  | succ n ih =>
    rw [hα, hβ]
    exact agree_upto_strict_extend F hstrict α β n ih

/-- `fix_unique` — any fixpoint of a strict F IS `fix F`. In flatland terms:
    any schedule that computes a fixpoint of the same strict operator
    computes THE fixpoint (order-independence of the cascade). -/
@[cert] theorem fix_unique [Zero a] (F : Operator a a) (hstrict : Strict F)
    (α : Stream a) (h_fix : α = F α) : α = fix F := by
  apply Dbsp.fixpoints_unique F hstrict α (fix F) h_fix
  exact fix_eq F hstrict

/-- Time invariance: the operator commutes with delay (z⁻¹). -/
def TimeInvariant [Zero a] [Zero b] (S : Operator a b) : Prop :=
  ∀ s, S (delay s) = delay (S s)

/-- Time invariance, applied pointwise. -/
theorem time_invariant_t [Zero a] [Zero b] {S : Operator a b} (h : TimeInvariant S)
    (s : Stream a) (t : Nat) : S (delay s) t = delay (S s) t :=
  congr_fun (h s) t

/-- Causality lifts to agreement: causal operators respect `agreeUpto`. -/
theorem causal_respects_agreeUpto (S : Operator a b) (h : Causal S)
    (s1 s2 : Stream a) (n : Nat) :
    agreeUpto n s1 s2 → agreeUpto n (S s1) (S s2) := by
  intro heq t ht
  exact h s1 s2 t (fun i hi => heq i (Nat.le_trans hi ht))

/-- `Causal` restated in `agreeUpto` form (the induction-friendly shape). -/
theorem causal_to_agree (S : Operator a b) :
    Causal S ↔ (∀ s1 s2 n, agreeUpto n s1 s2 → agreeUpto n (S s1) (S s2)) :=
  ⟨fun h => causal_respects_agreeUpto S h,
   fun h s s' t hpre => h s s' t hpre t (Nat.le_refl t)⟩

/-- Agreement extends one step through a delay. -/
theorem delay_succ_upto [Zero a] (s1 s2 : Stream a) (n : Nat) :
    agreeUpto n s1 s2 → agreeUpto (n + 1) (delay s1) (delay s2) := by
  intro h t ht
  cases t with
  | zero => rfl
  | succ m => exact h m (Nat.le_of_succ_le_succ ht)

/-- Pair of streams as a stream of pairs. -/
def sprod : Stream a × Stream b → Stream (a × b) := fun s n => (s.1 n, s.2 n)

@[simp] theorem sprod_apply (s : Stream a × Stream b) (n : Nat) :
    sprod s n = (s.1 n, s.2 n) := rfl

/-- Convert a curried two-input operator into an operator over pairs. -/
def uncurryOp (T : Operator2 a b c) : Operator (a × b) c :=
  fun s => T (lifting Prod.fst s) (lifting Prod.snd s)

/-- Causality of a curried two-input operator, componentwise. -/
theorem causal2 (T : Operator2 a b c) :
    Causal (uncurryOp T) ↔
      (∀ s1 s1' s2 s2' n, agreeUpto n s1 s1' → agreeUpto n s2 s2' →
        T s1 s2 n = T s1' s2' n) := by
  constructor
  · intro h s1 s1' s2 s2' n h1 h2
    exact h (sprod (s1, s2)) (sprod (s1', s2')) n (fun i hi => by
      show (s1 i, s2 i) = (s1' i, s2' i)
      rw [h1 i hi, h2 i hi])
  · intro h s s' n heq
    show T (lifting Prod.fst s) (lifting Prod.snd s) n
       = T (lifting Prod.fst s') (lifting Prod.snd s') n
    apply h
    · intro i hi; exact congrArg Prod.fst (heq i hi)
    · intro i hi; exact congrArg Prod.snd (heq i hi)

/-- Causality of `uncurryOp T` gives causality with the first input fixed. -/
theorem causal_uncurryOp_fixed (T : Operator2 a b b) :
    Causal (uncurryOp T) → ∀ s, Causal (T s) := by
  rw [causal2]
  intro h s s' s2' n heq
  exact h s s s' s2' n (agree_refl _ _) heq

/-- Composition of causal operators is causal. -/
theorem causal_comp_causal (S1 : Operator a b) (h1 : Causal S1)
    (S2 : Operator b c) (h2 : Causal S2) : Causal (fun s => S2 (S1 s)) := by
  intro s1 s2 n heq
  apply h2
  intro i hi
  exact h1 _ _ _ (fun j hj => heq j (Nat.le_trans hj hi))

/-- Lifted operators are causal. -/
theorem lifting_causal (f : a → b) : Causal (lifting f) := by
  intro s s' t h
  exact congrArg f (h t (Nat.le_refl t))

/-- `uncurryOp` of a lifted two-argument function is a lifted function
    (needed by the seminaive equivalence). -/
theorem uncurryOp_lifting2 (f : a → b → c) :
    uncurryOp (lifting2 f) = lifting (fun xy => f xy.1 xy.2) := rfl

/-- Delay away from zero reads the predecessor. -/
theorem delay_sub_1 [Zero a] (s : Stream a) (t : Nat) (h : 0 < t) :
    delay s t = s (t - 1) := by
  cases t with
  | zero => exact absurd h (Nat.lt_irrefl 0)
  | succ n => rfl

/-- The zero stream delayed is the zero stream. -/
theorem delay_zero_stream [Zero a] : delay (0 : Stream a) = 0 := by
  funext t
  cases t <;> rfl

/-- A time-invariant operator maps the zero stream to zero at time 0. -/
theorem time_invariant_0_0 [Zero a] [Zero b] (S : Operator a b) (h : TimeInvariant S) :
    S 0 0 = 0 := by
  calc S 0 0 = S (delay 0) 0 := by rw [delay_zero_stream]
    _ = delay (S 0) 0 := congr_fun (h 0) 0
    _ = 0 := rfl

/-- Zero-preservation: a time-invariant operator maps the zero stream to
    the zero stream. -/
theorem time_invariant_zpp [Zero a] [Zero b] (S : Operator a b) (h : TimeInvariant S) :
    S 0 = 0 := by
  funext t
  show S 0 t = 0
  induction t with
  | zero => exact time_invariant_0_0 S h
  | succ n ih =>
    calc S 0 (n + 1) = S (delay 0) (n + 1) := by rw [delay_zero_stream]
      _ = delay (S 0) (n + 1) := time_invariant_t h 0 (n + 1)
      _ = S 0 n := rfl
      _ = 0 := ih

/-- A lifted zero-preserving function is time-invariant. -/
theorem lifting_time_invariant [Zero a] [Zero b] (f : a → b) (h : f 0 = 0) :
    TimeInvariant (lifting f) := by
  intro s
  funext t
  cases t with
  | zero => show f (delay s 0) = 0; rw [delay_zero]; exact h
  | succ n => rfl

/-- An operator over pairs of streams applied to a pair of streams. -/
theorem uncurryOp_intro (T : Operator2 a b c) (s1 : Stream a) (s2 : Stream b) :
    T s1 s2 = uncurryOp T (sprod (s1, s2)) := rfl

/-- Delay commutes with pairing. -/
theorem sprod_time_invariant [Zero a] [Zero b] (s1 : Stream a) (s2 : Stream b) :
    sprod (delay s1, delay s2) = delay (sprod (s1, s2)) := by
  funext t
  cases t <;> rfl

/-- Delay commutes with the first projection of a stream of pairs. -/
theorem time_invariant_map_fst [Zero a] [Zero b] (s : Stream (a × b)) (n : Nat) :
    (delay s n).1 = delay (fun n => (s n).1) n := by
  cases n <;> rfl

/-- Delay commutes with the second projection of a stream of pairs. -/
theorem time_invariant_map_snd [Zero a] [Zero b] (s : Stream (a × b)) (n : Nat) :
    (delay s n).2 = delay (fun n => (s n).2) n := by
  cases n <;> rfl

/-- Two-input time invariance, curried form. -/
theorem time_invariant2 [Zero a] [Zero b] [Zero c] (T : Operator2 a b c) :
    TimeInvariant (uncurryOp T) ↔
      (∀ s1 s2, T (delay s1) (delay s2) = delay (T s1 s2)) := by
  constructor
  · intro hti s1 s2
    calc T (delay s1) (delay s2)
        = uncurryOp T (sprod (delay s1, delay s2)) := uncurryOp_intro _ _ _
      _ = uncurryOp T (delay (sprod (s1, s2))) := by rw [sprod_time_invariant]
      _ = delay (uncurryOp T (sprod (s1, s2))) := hti _
      _ = delay (T s1 s2) := by rw [← uncurryOp_intro]
  · intro h s
    have h1 : lifting Prod.fst (delay s) = delay (lifting Prod.fst s) := by
      funext t
      exact time_invariant_map_fst s t
    have h2 : lifting Prod.snd (delay s) = delay (lifting Prod.snd s) := by
      funext t
      exact time_invariant_map_snd s t
    show T (lifting Prod.fst (delay s)) (lifting Prod.snd (delay s))
       = delay (T (lifting Prod.fst s) (lifting Prod.snd s))
    rw [h1, h2, h]

/-- Two-input time invariance of a lifted function is exactly
    zero-preservation at (0, 0). -/
theorem lifting2_time_invariant [Zero a] [Zero b] [Zero c] (f : a → b → c) :
    TimeInvariant (uncurryOp (lifting2 f)) ↔ f 0 0 = 0 := by
  constructor
  · intro h
    have hh := congr_fun (h 0) 0
    rw [delay_zero_stream] at hh
    -- hh : uncurryOp (lifting2 f) 0 0 = delay (uncurryOp (lifting2 f) 0) 0
    exact hh
  · intro h0 s
    funext t
    cases t with
    | zero =>
      show f (delay s 0).1 (delay s 0).2 = 0
      exact h0
    | succ n => rfl

/-! ## The two-input agreement and circuit feedback facts

Causality of a curried two-input operator restated as pointwise two-sided
agreement (`causal2_agree`), and the feedback-loop facts used by the
circuit DSL (`feedback_ckt_body_strict`, `feedback_ckt_unfold`,
`feedback_ckt_causal`). The circuit `feedback` constructor builds its
loop as `s ↦ fix (α ↦ T s (z⁻¹ α))`; the theorems here are what make
that well-founded and causal. -/

/-- Causal `uncurryOp T` in pointwise two-sided `agreeUpto` form. -/
theorem causal2_agree (T : Operator2 a b c) :
    Causal (uncurryOp T) →
    (∀ s1 s1' s2 s2' n, agreeUpto n s1 s1' → agreeUpto n s2 s2' →
      agreeUpto n (T s1 s2) (T s1' s2')) := by
  intro hcausal s1 s1' s2 s2' n heq1 heq2 m hle
  apply (causal2 T).mp hcausal
  · exact agree_upto_weaken s1 s1' n m heq1 hle
  · exact agree_upto_weaken s2 s2' n m heq2 hle

/-- The feedback body `α ↦ T s (F α)` is strict when `F` is strict and
    `uncurryOp T` is causal. -/
theorem feedback_ckt_body_strict (F : Operator b b) (hstrict : Strict F)
    (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) (s : Stream a) :
    Strict (fun α => T s (F α)) :=
  causal_strict_strict F hstrict (T s) (causal_uncurryOp_fixed T hcausal s)

/-- Unfolding the feedback fixpoint through the strict body. -/
theorem feedback_ckt_unfold [Zero b] (F : Operator b b) (hstrict : Strict F)
    (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) (s : Stream a) :
    fix (fun α => T s (F α)) = T s (F (fix (fun α => T s (F α)))) :=
  fix_eq _ (feedback_ckt_body_strict F hstrict T hcausal s)

/-- Feedback through a strict body is causal: the loop shape
    `s ↦ fix (α ↦ T s (F α))` respects `agreeUpto`. -/
theorem feedback_ckt_causal [Zero b] (F : Operator b b) (hstrict : Strict F)
    (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    Causal (fun s => fix (fun α => T s (F α))) := by
  rw [causal_to_agree]
  intro s1 s2 n heq
  induction n with
  | zero =>
      rw [feedback_ckt_unfold F hstrict T hcausal s1,
          feedback_ckt_unfold F hstrict T hcausal s2]
      rw [agree_upto_0]
      apply (causal2 T).mp hcausal
      · exact heq
      · rw [agree_upto_0]
        exact strict_unique_zero F hstrict (fix (fun α => T s1 (F α))) (fix (fun α => T s2 (F α)))
  | succ n ih =>
      rw [feedback_ckt_unfold F hstrict T hcausal s1,
          feedback_ckt_unfold F hstrict T hcausal s2]
      apply causal2_agree T hcausal
      · exact heq
      · apply agree_upto_strict_extend F hstrict
        exact ih (agree_upto_weaken s1 s2 (n + 1) n heq (Nat.le_succ n))

end Dbsp

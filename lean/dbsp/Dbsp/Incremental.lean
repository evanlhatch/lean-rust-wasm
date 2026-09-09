/-
# Dbsp.Incremental — the incrementalization family

Ports tchajed/database-stream-processing-theory `src/incremental.lean`
(Lean 3) to Lean 4 (notes/lean/lean-v3.md Part 3). The source's postfix
`Q^Δ` notation is deliberately dropped: `^` tokenization fights mathlib's
HPow, and plain `incremental Q` reads fine.

The core definition: `incremental Q := D ∘ Q ∘ I` — the incremental form
of an operator consumes and produces *changes*. The theorems are the
engine's rewrite licenses:

- `integrate_push` / `derivative_push` — I and D commute through any
  operator by shifting to its incremental form. The cascade may integrate,
  run batch, differentiate — or stay in delta-land. Same answer.
- `chain_incremental` — composition incrementalizes compositionally:
  `incremental (Q1 ∘ Q2) = incremental Q1 ∘ incremental Q2`. Plans compile
  kernel-by-kernel.
- `lti_incremental` — an LTI operator is its own incremental form.
  Linear kernels never need the old state beyond their inputs: this is the
  `old_values`-policy license (lean-v3 Part 3 port map).
- `cycle_incremental` — a feedback loop incrementalizes into an incremental
  feedback loop. Recursion is incrementalizable: the cascade's fixpoint
  over deltas computes the same fixpoint as the batch loop over states.

Deferred from the source: the nested-stream machinery (`strict2`,
`causal_nested`, `cycle2_incremental`, sprod product forms) — the
two-input nested cycle story lands with the multi-input cascade work.

UPDATE: this is no longer deferred — `Dbsp.NestedCycle` ports it
(`fix2_eq`, `fix2_unique`, `cycle2_incremental`, `strict2`,
`causal_nested`). This header predates that module.
-/

import Dbsp.Linear

namespace Dbsp

variable {a b c : Type} [AddCommGroup a] [AddCommGroup b] [AddCommGroup c]

/-- The incremental version of Q: `incremental Q := D ∘ Q ∘ I`. Same type
    as Q, but it takes a stream of changes and produces a stream of
    changes. -/
def incremental (Q : Operator a b) : Operator a b := fun s => D (Q (I s))

/-- The incremental version of a two-input operator. -/
def incremental2 (T : Operator2 a b c) : Operator2 a b c :=
  fun s1 s2 => D (T (I s1) (I s2))

theorem incremental_unfold (Q : Operator a b) (s : Stream a) :
    incremental Q s = D (Q (I s)) := rfl

/-! ## The inversion: incremental forms are a bijection on operators -/

private def incrementalInv (Q : Operator a b) : Operator a b := I ∘ Q ∘ D

theorem incremental_inversion_l :
    Function.LeftInverse (@incrementalInv a b _ _) (@incremental a b _ _) := by
  intro Q
  funext s
  simp [incremental, incrementalInv, Function.comp_apply]

theorem incremental_inversion_r :
    Function.RightInverse (@incrementalInv a b _ _) (@incremental a b _ _) := by
  intro Q
  funext s
  simp [incremental, incrementalInv, Function.comp_apply]

/-- Every operator has exactly one incremental form (up to the D/I pair):
    incrementalization loses nothing. -/
theorem incremental_bijection : Function.Bijective (@incremental a b _ _) :=
  ⟨incremental_inversion_l.injective, incremental_inversion_r.surjective⟩

/-! ## Invariances and the push rules -/

theorem delay_invariance : incremental (@delay a _) = delay := by
  funext s
  show D (delay (I s)) = delay s
  rw [derivative_time_invariant, integral_derivative]

theorem integral_invariance : incremental (@I a _) = I := by
  funext s
  simp [incremental]

theorem derivative_invariance : incremental (@D a _) = D := by
  funext s
  simp [incremental]

/-- `Q ∘ I = I ∘ incremental Q` — running the batch operator on the
    integrated stream is integrating the incremental operator's output.
    The checkpoint/tick commutation license. -/
theorem integrate_push (Q : Operator a b) : Q ∘ I = I ∘ incremental Q := by
  funext s
  simp [incremental, Function.comp_apply]

/-- `D ∘ Q = incremental Q ∘ D` — differentiating the batch output is
    running the incremental operator on the deltas. The journal/tick
    commutation license. -/
theorem derivative_push (Q : Operator a b) : D ∘ Q = incremental Q ∘ D := by
  funext s
  simp [incremental, Function.comp_apply]

theorem I_push (Q : Operator a b) (s : Stream a) :
    Q (I s) = I (incremental Q s) := by
  simp [incremental]

theorem D_push (Q : Operator a b) (s : Stream a) :
    D (Q s) = incremental Q (D s) := by
  simp [incremental]

theorem D_push2 (Q : Operator2 a b c) (s1 : Stream a) (s2 : Stream b) :
    D (Q s1 s2) = incremental2 Q (D s1) (D s2) := by
  simp [incremental2]

/-- **Composition incrementalizes compositionally** — plans compile
    kernel-by-kernel, no global reasoning needed. -/
theorem chain_incremental (Q1 : Operator b c) (Q2 : Operator a b) :
    incremental (Q1 ∘ Q2) = incremental Q1 ∘ incremental Q2 := by
  funext s
  simp [incremental, Function.comp_apply]

theorem incremental_comp (Q1 : Operator b c) (Q2 : Operator a b) (s : Stream a) :
    incremental (fun s => Q1 (Q2 s)) s = incremental Q1 (incremental Q2 s) := by
  simp [incremental]

theorem add_incremental (Q1 Q2 : Operator a b) :
    incremental (Q1 + Q2) = incremental Q1 + incremental Q2 := by
  funext s
  show D ((Q1 + Q2) (I s)) = D (Q1 (I s)) + D (Q2 (I s))
  rw [show (Q1 + Q2) (I s) = Q1 (I s) + Q2 (I s) from rfl]
  exact derivative_linear _ _

/-! ## LTI operators are their own incremental form -/

/-- **The old_values license**: an LTI operator's incremental form is
    itself — a linear time-invariant kernel applied to deltas IS the delta
    of the kernel applied to states. No old-state reads beyond inputs. -/
theorem lti_incremental (Q : Operator a b) (h : Lti Q) : incremental Q = Q := by
  funext s
  show Q (I s) - delay (Q (I s)) = Q s
  rw [← h.2, ← integral_time_invariant, ← linear_sub h.1, ← linear_sub integral_linear]
  show Q (I (D s)) = Q s
  rw [derivative_integral]

@[simp] theorem I_incremental : incremental (@I a _) = I :=
  lti_incremental I integral_lti

@[simp] theorem D_incremental : incremental (@D a _) = D :=
  lti_incremental D derivative_lti

theorem delay_lti : Lti (@delay a _) := ⟨delay_linear, delay_time_invariant⟩

@[simp] theorem delay_incremental : incremental (@delay a _) = delay :=
  lti_incremental delay delay_lti

/-! ## Recursion incrementalizes -/

/-- The cycle body (feedback through a two-input causal operator) is
    strict, hence has a unique fixpoint. -/
theorem cycle_body_strict (T : Operator2 a b b) (hcausal : Causal (uncurryOp T))
    (s : Stream a) : Strict (fun α => T s (delay α)) :=
  causal_strict_strict delay delay_strict (T s) (causal_uncurryOp_fixed T hcausal s)

/-- The integrated cycle body is strict. -/
theorem cycle_body_integral_strict (T : Operator2 a b b) (hcausal : Causal (uncurryOp T))
    (s : Stream a) : Strict (fun α => T (I s) (delay α)) :=
  causal_strict_strict delay delay_strict (T (I s)) (causal_uncurryOp_fixed T hcausal (I s))

/-- The incrementalized cycle body is strict. -/
theorem cycle_body_incremental_strict (T : Operator2 a b b)
    (hcausal : Causal (uncurryOp T)) (s : Stream a) :
    Strict (fun α => incremental2 T s (delay α)) := by
  have h1 : Strict (fun α => T (I s) (I (delay α))) :=
    causal_strict_strict delay delay_strict _
      (causal_comp_causal I integral_causal (T (I s)) (causal_uncurryOp_fixed T hcausal (I s)))
  exact causal_strict_strict _ h1 D derivative_causal

/-- **The cascade theorem**: a feedback loop's incremental form is the
    feedback loop of the incremental form. The engine may run its recursive
    rules (fixpoint per tick) entirely on deltas; the result equals
    differentiating the batch fixpoint. This licenses the whole
    delta-driven architecture for recursive rules. -/
theorem cycle_incremental (T : Operator2 a b b) (hcausal : Causal (uncurryOp T)) :
    incremental (fun s => fix (fun α => T s (delay α)))
      = fun s => fix (fun α => incremental2 T s (delay α)) := by
  funext s
  apply fix_unique _ (cycle_body_incremental_strict T hcausal s)
  show D (fix (fun α => T (I s) (delay α)))
    = D (T (I s) (I (delay (D (fix (fun α => T (I s) (delay α)))))))
  rw [integral_time_invariant, derivative_integral]
  congr 1
  exact fix_eq _ (cycle_body_integral_strict T hcausal s)

/-! ## Causality of incremental forms -/

/-- Incrementalization preserves causality. -/
@[simp]
theorem causal_incremental (Q : Operator a b) (h : Causal Q) :
    Causal (incremental Q) :=
  causal_comp_causal _ (causal_comp_causal I integral_causal Q h) D derivative_causal

/-- The two-input form, uncurried. -/
theorem causal_incremental2 (Q : Operator2 a b c) (h : Causal (uncurryOp Q)) :
    Causal (fun s => incremental2 Q (lifting Prod.fst s) (lifting Prod.snd s)) := by
  rw [causal2] at h
  apply causal_comp_causal (fun s => Q (I (lifting Prod.fst s)) (I (lifting Prod.snd s)))
    _ D derivative_causal
  intro s1 s2 n heq
  apply h
  · apply causal_respects_agreeUpto _ integral_causal
    apply causal_respects_agreeUpto _ (lifting_causal _)
    exact heq
  · apply causal_respects_agreeUpto _ integral_causal
    apply causal_respects_agreeUpto _ (lifting_causal _)
    exact heq

@[simp] theorem incremental_id' : incremental (@id (Stream a)) = id := by
  funext s
  simp [incremental]

/-! ## The bilinear three-term rule (the incremental join) -/

/-- The three-term form: `a⋆b + I(z⁻¹a)⋆b + a⋆I(z⁻¹b)`. For a bilinear
    operator (join, product) this is its incremental form — the classic
    incremental-join expansion. -/
def timesIncremental (times : Operator2 a b c) : Operator2 a b c :=
  fun a b => times a b + times (I (delay a)) b + times a (I (delay b))

/-- **The incremental join theorem** (the paper's bilinear rule, ported
    via the source's short calc proof): for a time-invariant bilinear
    operator, the incremental form is the three-term expansion. This is
    the license for the engine's delta-join kernels: a join consumes the
    left delta against the right state, the right delta against the left
    state (one tick back), plus delta-against-delta. -/
theorem bilinear_incremental (times : Operator2 a b c)
    (hti : TimeInvariant (uncurryOp times)) (hbil : Bilinear times) :
    incremental2 times = timesIncremental times := by
  funext s1 s2
  calc incremental2 times s1 s2
      = D (times (I s1) (I s2)) := rfl
    _ = times (I s1) (I s2) - delay (times (I s1) (I s2)) := rfl
    _ = times (I s1) (I s2) - times (delay (I s1)) (delay (I s2)) := by
        rw [← (time_invariant2 times).mp hti]
    _ = times (s1 + delay (I s1)) (s2 + delay (I s2)) - times (delay (I s1)) (delay (I s2)) := by
        nth_rewrite 1 [integral_unfold s1]
        nth_rewrite 1 [integral_unfold s2]
        rfl
    _ = times s1 s2 + times (delay (I s1)) s2 + times s1 (delay (I s2))
          + times (delay (I s1)) (delay (I s2))
          - times (delay (I s1)) (delay (I s2)) := by
        rw [hbil.2, hbil.1, hbil.1]
        abel
    _ = times s1 s2 + times (delay (I s1)) s2 + times s1 (delay (I s2)) := by
        abel
    _ = times s1 s2 + times (I (delay s1)) s2 + times s1 (I (delay s2)) := by
        rw [integral_time_invariant, integral_time_invariant]
    _ = timesIncremental times s1 s2 := rfl

/-- The incrementalization of a pairing operator is the paired
    incrementalizations (needed by `Ckt.incrementalize_ok` for the `par`
    constructor). -/
theorem incremental_sprod (f : Operator (a × b) c) (s1 : Stream a) (s2 : Stream b) :
    incremental f (sprod (s1, s2)) =
      incremental2 (fun s1 s2 => f (sprod (s1, s2))) s1 s2 := by
  unfold incremental incremental2
  rw [integral_sprod]

end Dbsp

/-
# Dbsp.Recursive — recursive rules, naive vs semi-naive evaluation

Ports tchajed/database-stream-processing-theory `src/recursive.lean`
(Lean 3) to Lean 4 (notes/lean/lean-v3.md Part 3).

The theorems:

- `recursive_fixpoint_ok` — when the iterate sequence of a recursive rule
  stabilizes at pass n, the stream-level fixpoint machinery computes
  exactly that value. The bounded-pass engine is the certified evaluator.
- `seminaive_equiv` — **naive ≡ semi-naive**: running the incrementalized
  feedback loop on the input delta produces the same answer as the batch
  loop on integrated states. This is the pregel/datalog license (lean-v3
  port map: seminaive → pregel).
- `naive_ok` / `seminaive_ok` — both compute the stabilizing iterate.

Intentional strengthening over the source: the source works over `Z[a]`
(zsets) but only ever uses the group structure — this port is generalized
to any `AddCommGroup`. Flatland's world-as-zset-bundle instantiates it.

The classical choice inside `streamElim` stays inert: every use comes with
a `ZeroAfter` certificate (here: iterate stabilization).
-/

import Dbsp.Certs
import Dbsp.StreamElim
import Mathlib.Logic.Function.Iterate

namespace Dbsp

variable {G A B : Type} [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]

/-- The approximation stream of a recursive rule R: the fixpoint of
    `o = R (z⁻¹ o)`, i.e. `approxs R n = R^[n+1] 0` (`approxs_apply`). -/
def approxs (R : G → G) : Stream G := fix (fun o => lifting R (delay o))

theorem approxs_unfold (R : G → G) : approxs R = lifting R (delay (approxs R)) :=
  fix_eq _ (causal_strict_strict delay delay_strict (lifting R) (lifting_causal R))

theorem approxs_apply (R : G → G) (n : Nat) : approxs R n = (R^[n + 1]) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := congr_fun (approxs_unfold R) (n + 1)
    show approxs R (n + 1) = R^[n + 1 + 1] 0
    rw [h]
    show R (delay (approxs R) (n + 1)) = R^[n + 1 + 1] 0
    rw [delay_succ, ih]
    have step : R^[n + 1 + 1] 0 = R (R^[n + 1] 0) := by
      rw [Function.iterate_succ', Function.comp_apply]
    exact step.symm

theorem approxs_unfold_succ (R : G → G) (n : Nat) :
    approxs R (n + 1) = R (approxs R n) := by
  have h := congr_fun (approxs_unfold R) (n + 1)
  rw [h]
  rfl

/-- Once the iterates stabilize, they stay stable. -/
theorem eq_succ_is_fixpoint (R : G → G) (n : Nat)
    (heqn : R^[n + 1] 0 = R^[n] 0) : ∀ m ≥ n, R^[m] 0 = R^[n] 0 := by
  intro m hge
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show n + (d + 1) = (n + d) + 1 by omega, Function.iterate_succ',
      Function.comp_apply]
    rw [ih (by omega)]
    have step : R^[n + 1] 0 = R (R^[n] 0) := by
      rw [Function.iterate_succ', Function.comp_apply]
    rw [← step]
    exact heqn

/-- After stabilization, the derivative of the approximation stream is
    zero — the convergence certificate for `streamElim`. -/
theorem derivative_approx_almost_zero (R : G → G) (n : Nat)
    (heqn : R^[n + 1] 0 = R^[n] 0) : ZeroAfter (D (approxs R)) (n + 1) := by
  intro m hge
  rw [derivative_difference _ m (by omega)]
  rw [approxs_apply, approxs_apply, show m - 1 + 1 = m by omega]
  rw [eq_succ_is_fixpoint R n heqn (m + 1) (by omega),
      eq_succ_is_fixpoint R n heqn m (by omega)]
  exact sub_self _

/-- The limit of the approximation stream: the recursive rule's fixpoint
    value, read off via `streamElim`. -/
noncomputable def recursiveFixpoint (R : G → G) : G := streamElim (D (approxs R))

/-- **Correctness of the bounded evaluator**: when the iterates stabilize
    at pass n, the stream fixpoint computes the n-th iterate. The engine's
    fuel-bounded convergence check (SPEC-core §7.1) is exactly the
    decidable form of the hypothesis. -/
theorem recursive_fixpoint_ok (R : G → G) (n : Nat)
    (heqn : R^[n + 1] 0 = R^[n] 0) : recursiveFixpoint R = R^[n] 0 := by
  unfold recursiveFixpoint
  rw [stream_elim_zero_after _ _ (derivative_approx_almost_zero R n heqn)]
  rw [sum_vals_succ_n, approxs_apply]
  exact heqn

/-! ## Naive vs semi-naive -/

/-- Naive evaluation: integrate the input impulse, run the feedback loop
    on full states, differentiate, read the limit. -/
noncomputable def naive (R : B → A → A) : B → A :=
  fun i => streamElim (D (fix (fun o => lifting2 R (I (δ0 i)) (delay o))))

/-- Semi-naive evaluation: run the incrementalized feedback loop directly
    on the input delta, read the limit. -/
noncomputable def seminaive (R : B → A → A) : B → A :=
  fun i => streamElim (fix (fun o => incremental2 (lifting2 R) (δ0 i) (delay o)))

/-- **Naive ≡ semi-naive.** The datalog/pregel license: evaluating the
    incrementalized recursion on deltas equals evaluating the batch
    recursion on integrated states. Direct corollary of
    `cycle_incremental` — recursion incrementalizes. -/
theorem seminaive_equiv (R : B → A → A) : seminaive R = naive R := by
  funext x
  show streamElim _ = streamElim _
  congr 1
  have hcausal : Causal (uncurryOp (lifting2 R)) := by
    rw [uncurryOp_lifting2]
    exact lifting_causal _
  exact (congr_fun (cycle_incremental (lifting2 R) hcausal) (δ0 x)).symm

/-- The naive evaluator computes the stabilizing iterate. -/
theorem naive_ok (R : B → A → A) (i : B) (n : Nat)
    (heqn : (R i)^[n + 1] 0 = (R i)^[n] 0) : naive R i = (R i)^[n] 0 := by
  have hfix : (fun o : Stream A => lifting2 R (I (δ0 i)) (delay o))
            = (fun o : Stream A => lifting (R i) (delay o)) := by
    funext o t
    show R (I (δ0 i) t) (delay o t) = R i (delay o t)
    rw [integral_delta_apply]
  show streamElim (D (fix (fun o => lifting2 R (I (δ0 i)) (delay o)))) = (R i)^[n] 0
  rw [hfix]
  exact recursive_fixpoint_ok (R i) n heqn

/-- The semi-naive evaluator computes the stabilizing iterate. -/
@[cert] theorem seminaive_ok (R : B → A → A) (i : B) (n : Nat)
    (heqn : (R i)^[n + 1] 0 = (R i)^[n] 0) : seminaive R i = (R i)^[n] 0 := by
  rw [seminaive_equiv]
  exact naive_ok R i n heqn

end Dbsp

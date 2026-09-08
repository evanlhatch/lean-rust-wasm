/- Axioms gate (drift CI 7.3.3): headline theorems must print only the core
   triple. Checked by `just lean-axioms`. -/
import Dbsp
#print axioms Dbsp.fix_unique
#print axioms Dbsp.derivative_integral
#print axioms Dbsp.integral_derivative
#print axioms Dbsp.seminaive_equiv
#print axioms Dbsp.equiJoin_incremental
#print axioms Dbsp.distinct_incremental_ok
#print axioms Dbsp.incrementalize_ok
#print axioms Dbsp.staged_eq_joint
#print axioms Dbsp.derivative_pos_counter_example
#print axioms Dbsp.stagedN_eq_jointN

-- cert citations resolve (lean-v3 §4.4): names + required shapes, CI-pinned
#check_cert Dbsp.fix_unique : ∀ {a : Type} [Zero a] (F : Dbsp.Operator a a),
    Dbsp.Strict F → ∀ (s : Dbsp.Stream a), s = F s → s = Dbsp.fix F
#check_cert Dbsp.derivative_integral : ∀ {a : Type} [AddCommGroup a] (s : Dbsp.Stream a),
    Dbsp.I (Dbsp.D s) = s
#check_cert Dbsp.integral_derivative : ∀ {a : Type} [AddCommGroup a] (s : Dbsp.Stream a),
    Dbsp.D (Dbsp.I s) = s
#check_cert Dbsp.seminaive_ok : ∀ {A B : Type} [AddCommGroup A] [AddCommGroup B] (R : B → A → A) (i : B) (n : Nat),
    (R i)^[n + 1] 0 = (R i)^[n] 0 → Dbsp.seminaive R i = (R i)^[n] 0

-- §4.3 readings (Dbsp.Subsystems)
#print axioms Dbsp.journal_complete
#print axioms Dbsp.journal_invertible
#print axioms Dbsp.checkpoint_is_state
#print axioms Dbsp.replica_divergence_cancels

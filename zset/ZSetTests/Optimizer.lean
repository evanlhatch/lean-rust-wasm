/-
# ZSetTests.Optimizer — the equational theory's pins (F5)

Positive pins + the MANDATORY negative controls (15-patterns #5):

1. The rules' positive pins: selection fusion, the factored pushdown,
   the join's weight-commutation face, the Bool union-idempotence, the
   empty-relation annihilators, the lifted-through-`evaluate` forms.
2. The negative controls: the UNFACTORED pushdown genuinely differs
   (the `ReadsThrough` premise is load-bearing, not decorative), and
   union-idempotence is FALSE over ℤ (2 ≠ 1 — the weight kind is the
   rule's premise, as data).

Axiom self-check: the `#print axioms` pins at the bottom — the
core-triple-only surface or the build fails.
-/

import ZSet
import ZSet.Optimizer
import TestingKit.Spec
import TestingKit.Harness
import LintKit.Basic  -- the `@[nolint … "reason"]` attr (the control twins' opt-out below)

namespace ZSetTests.Optimizer

open ZSet TestingKit

/-! ## Fixtures -/

/-- The worked relation: rows 12 and 5, weights 2 and 1 (ℤ). -/
def m1 : Weighted Int Nat := fromListW [(12, 2), (5, 1)]

/-- The projection map: row → its decade. -/
def decade (n : Nat) : Nat := n / 10

/-- The factored selection: `p = p' ∘ decade` — the pushdown's
    witness holds BY `rfl`. -/
def pFactored (n : Nat) : Bool := decade n > 0
def p'Sel (b : Nat) : Bool := b > 0

theorem pFactored_factors : ZSet.ReadsThrough decade pFactored p'Sel :=
  fun _ => rfl

/-- The UNFACTORED selection: parity is not a function of the decade.
    (The twins are deliberately alpha-equivalent: the negative control's
    assertion is that the UNFACTORED rule genuinely differs — which only
    reads if the two sides' predicates ARE the same body, so the
    duplication is the differential's content, not an accident. The
    QueryTests differential-twin precedent.) -/
@[nolint linter.guestlang.dupDefBodies "the negative-control twins: body-equality IS the control's assertion — the unfactored pushdown's refutation needs both sides to carry the SAME parity predicate (parity is not a function of the decade); the differential-twin precedent (QueryTests)"]
def pBad (n : Nat) : Bool := n % 2 == 0
@[nolint linter.guestlang.dupDefBodies "the negative-control twins: body-equality IS the control's assertion — the unfactored pushdown's refutation needs both sides to carry the SAME parity predicate (parity is not a function of the decade); the differential-twin precedent (QueryTests)"]
def p'Bad (b : Nat) : Bool := b % 2 == 0

/-- The Bool-weighted twin (the set-semantics instance). -/
def mB : Weighted Bool Nat := fromListW [(1, true)]

/-- The cascade's outer pick: odd decade (the factored twin's `g1`). -/
def odd10 (b : Nat) : Nat := b % 2

/-- The cascade's factoring witness: `gA n = odd10 (decade n)` — holds
    BY `rfl` (the sublist premise as data). -/
def oddDecade (n : Nat) : Nat := odd10 (decade n)

theorem oddDecade_factors : ∀ n, oddDecade n = odd10 (decade n) := fun _ => rfl

/-- The UNFACTORED twin: the constant-1 map does not factor through
    the decade (12's decade is 1 but 5's is 0 — not one class). -/
def gBad (_b : Nat) : Nat := 1

/-! ## Suite -/

def optimizerSpec : Spec :=
  Spec.ofList "the equational theory: fusion, pushdown, comm, idem, annihilators"
    (fun _ => do
      -- SELECTION FUSION: σ p (σ q R) = σ (p ∧ q) R
      assert
        (weightW (filterW pFactored (filterW (fun n => n < 20) m1)) 12 == 2
          && weightW (filterW (fun a => pFactored a && (fun n => n < 20) a) m1) 12 == 2
          && weightW (filterW pFactored (filterW (fun n => n < 20) m1)) 5 == 0
          && weightW (filterW pFactored (filterW (fun n => n < 20) m1)) 99 == 0)
        "the fused selection drifted"
      -- THE LIFTED FORM through evaluate (ONE unfolding, same row)
      assert
        (weightW (evaluate (Query.filter pFactored (Query.filter (fun n => n < 20) .idQ)) m1) 12 == 2)
        "the lifted fusion drifted"
      -- THE FACTORED PUSHDOWN: π g (σ p R) = σ p' (π g R)
      assert
        (weightW (projectW decade (filterW pFactored m1)) 1 == 2
          && weightW (filterW p'Sel (projectW decade m1)) 1 == 2
          && weightW (projectW decade (filterW pFactored m1)) 0 == 0
          && weightW (filterW p'Sel (projectW decade m1)) 0 == 0)
        "the factored pushdown drifted"
      -- JOIN-COMMUTATIVITY'S WEIGHT FACE (the ORDER note: weights, not rows)
      assert
        (weightW (joinW (fromListW [(1, 3)]) (fromListW [(1, 4)])) 1 == 12
          && weightW (joinW (fromListW [(1, 4)]) (fromListW [(1, 3)])) 1 == 12)
        "the join's weight face drifted"
      -- UNION-IDEMPOTENCE under Bool
      assert (weightW (addW mB mB) 1 == true)
        "the Bool idempotence drifted"
      -- THE EMPTY-RELATION ANNIHILATORS
      assert
        (weightW (joinW zeroW m1) 12 == 0
          && weightW (joinW m1 zeroW) 12 == 0
          && weightW (filterW (fun _ => true) zeroW) 12 == 0
          && weightW (projectW decade zeroW) 0 == 0
          && weightW
              (evaluate (Query.join .idQ (Query.union .idQ .idQ)) (zeroW (K := Int))) 1 == 0)
        "the annihilators drifted"
      -- JOIN-ASSOCIATIVITY'S WEIGHT FACE (the premise: mul ASSOCIATES —
      -- not a `WKind` field, carried as data; the cross term is the
      -- Change-side face, 03 §9)
      assert
        (weightW (joinW (joinW m1 (fromListW [(12, 3)])) (fromListW [(12, 5)])) 12 == 30
          && weightW (joinW m1 (joinW (fromListW [(12, 3)]) (fromListW [(12, 5)]))) 12 == 30
          && weightW
              (evaluate (Query.join (Query.join .idQ .idQ) .idQ) m1) 12 == 8
          && weightW
              (evaluate (Query.join .idQ (Query.join .idQ .idQ)) m1) 12 == 8)
        "the join's regrouping drifted"
      -- THE PROJECTION CASCADE: π_A (π_B R) = π_A R — the factoring as
      -- data (gA = g1 ∘ g2 pointwise)
      assert
        (weightW (projectW odd10 (projectW decade m1)) 1 == 2
          && weightW (projectW (fun n => odd10 (decade n)) m1) 1 == 2
          && weightW (projectW odd10 (projectW decade m1)) 0 == 1
          && weightW (projectW (fun n => odd10 (decade n)) m1) 0 == 1)
        "the projection cascade drifted"
      -- THE CONSTANT-FOLD: a constant-false selection is the empty
      -- relation (the feasibility discipline's consumer)
      assert
        (weightW (filterW (fun _ => false) m1) 12 == 0
          && weightW (filterW (fun _ => false) m1) 5 == 0
          && weightW (evaluate (Query.filter (fun _ => false) .idQ) m1) 12 == 0)
        "the constant-fold drifted"
      -- UNION-COMMUTATIVITY under the observer (the add commutes for
      -- EVERY WKind — the law is a field; the canonical face, not a
      -- row order)
      assert
        (weightW (evaluate (Query.union (Query.filter (fun n : Nat => n > 5) .idQ) .idQ) m1) 12
          == weightW (evaluate (Query.union .idQ (Query.filter (fun n : Nat => n > 5) .idQ)) m1) 12
          && weightW (evaluate (Query.union (Query.filter (fun n : Nat => n > 5) .idQ) .idQ) m1) 12
          == 4)
        "the union's reordering drifted")
    [ ("sabotage: the UNFACTORED pushdown differs — the premise is load-bearing",
        fun _ =>
          -- the WRONG-arithmetic claim: the unfactored pushdown 'commutes'
          assert
            (weightW (projectW decade (filterW pBad m1)) 1
              == weightW (filterW p'Bad (projectW decade m1)) 1)
            "control")
    , ("sabotage: union-idempotence is FALSE over ℤ — the weight kind is the premise",
        fun _ =>
          -- the WRONG claim: doubling a ℤ-weighted relation changes nothing
          assert
            (weightW (addW (fromListW [(1, 5)]) (fromListW [(1, 5)])) 1
              == weightW (fromListW [(1, 5)]) 1)
            "control")
    , ("sabotage: the UNFACTORED cascade differs — the factoring is load-bearing",
        fun _ =>
          -- the WRONG claim: a gA that does not factor through g2
          -- regroups the same
          assert
            (weightW (projectW odd10 (projectW decade m1)) 0
              == weightW (projectW (fun _ => 1) m1) 0)
            "control")
    , ("sabotage: a non-constant-false selection is NOT the empty relation",
        fun _ =>
          -- the WRONG claim: every selection folds away
          assert
            (weightW (filterW (fun n : Nat => n > 5) m1) 12 == 0)
            "control") ]
    1 42

/-! ## The axiom self-check -/

/-- info: 'ZSet.filterW_fuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.filterW_fuse

/-- info: 'ZSet.projectW_pushdown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.projectW_pushdown

/-- info: 'ZSet.joinW_comm_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.joinW_comm_weight

/-- info: 'ZSet.evaluate_zeroW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.evaluate_zeroW

/-- info: 'ZSet.evaluate_join_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.evaluate_join_assoc

/-- info: 'ZSet.projectW_cascade' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.projectW_cascade

/-- info: 'ZSet.filterW_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.filterW_false

/-- info: 'ZSet.evaluate_union_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.evaluate_union_comm

end ZSetTests.Optimizer

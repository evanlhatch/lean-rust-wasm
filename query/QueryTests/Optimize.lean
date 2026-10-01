/-
# QueryTests.Optimize — the checked rewriter's teeth (F5)

The qlang! pipeline end-to-end (02 §6): `qlang!{…}` → the certificate
(`Cert`) → the optimized plan evaluates EXACTLY as the original — the
contract (`Cert.eval_eq`/`Optimized.agrees`) + the spec face
(`Cert.qsat_iff`, composed through the landed bridge). The mandatory
negative controls (15-patterns #5):

- the UNFACTORED pushdown's witness is refuted at a row (`decide` —
  the kernel refusing the constructor's payload, at the data level);
- the union rule's shape-check is load-bearing: fusing DISTINCT
  branches loses rows.

Axiom self-check: the `#print axioms` pins at the bottom.
-/

import Query
import Query.Optimize
import TestingKit.Spec
import TestingKit.Harness

namespace QueryTests.Optimize

open Query SchemaCore ZSet TestingKit

/-! ## Fixtures (the independent-rig discipline: this suite's own) -/

@[nolint linter.guestlang.dupDefBodies "the worked schema's per-suite fixture — the suites are independent rigs, not copies"]
def optFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "cust", ty := .u64 },
    { name := "amt", ty := .u64 }]

@[nolint linter.guestlang.dupDefBodies "the worked row's per-suite fixture — the suites are independent rigs, not copies"]
def optRow (i c a : UInt64) : RowVals optFields :=
  .cons (.u64 i) (.cons (.u64 c) (.cons (.u64 a) .nil))

def optRows : List (RowVals optFields) :=
  [optRow 1 10 200, optRow 2 11 50, optRow 3 10 500]

/-! ## The fusion pipeline: qlang!{…} → Cert → the optimized plan -/

/-- The qlang! query with TWO selections (the fusion's target). -/
def qNested := qlang!{ from optFields then select (cust == 10) then select (amt > 100) }

/-- The optimized plan: the fused selection (the rule's output). -/
def qFused : Q optFields optFields :=
  .select (.and (.u64GtLit "amt" 100) (.u64EqLit "cust" 10)) .table

/-- THE CERTIFICATE: the untrusted proposer's rewrite sequence — the
    kernel checks every step (the `selFuse` ctor's shape + the rules'
    theorems behind `OptStep.eval_eq`). -/
def fuseCert : Cert qNested qFused := .step .selFuse .done

/-- THE OPTIMIZER'S OUTPUT (02 §6's interface): optimized query +
    proof. -/
def fuseOut : Optimized qNested := ⟨qFused, fuseCert⟩

/-- The contract's face at a row: the optimized plan evaluates
    EXACTLY as the original. -/
theorem agreesAt (r : RowVals optFields) :
    weightW (evalQ qFused (tableW optRows true)) r
      = weightW (evalQ qNested (tableW optRows true)) r :=
  congrArg (fun m => weightW m r) (fuseOut.agrees optRows)

/-! ## The pushdown pipeline: the witness rides the step -/

/-- The order-preserving drop: keep `id` and `amt`, skip `cust`. -/
def keepIdsAmt : Cols optFields := .keep (.skip (.keep .nil))

/-- The qlang! selection AFTER a projection (the pushdown's target). -/
def qSelProj := qlang!{ from optFields then project [.id, .amt] then select (amt > 100) }

/-- THE FACTORING WITNESS (the premise as data): the top selection
    reads `amt`, which the pick carries — `p = p' ∘ pick`. -/
theorem pushWitness : ∀ r : RowVals optFields,
    Pred.check (.u64GtLit "amt" 100) (keepIdsAmt.pick optFields r)
      = Pred.check (.u64GtLit "amt" 100) r := by
  intro r
  cases r with
  | cons a rest =>
      cases rest with
      | cons b rest2 =>
          cases rest2 with
          | cons c rest3 =>
              cases rest3 with
              | nil => rfl

/-- The projected row's ascribed form (the computed index pinned). -/
def projRow (i a : UInt64) : RowVals (keepIdsAmt.fields optFields) :=
  .cons (.u64 i) (.cons (.u64 a) .nil)

/-- The pushed plan + its checked step + the certificate. -/
def pushPlan : Q optFields (keepIdsAmt.fields optFields) :=
  .project keepIdsAmt (.select (.u64GtLit "amt" 100) .table)

def pushStep : OptStep qSelProj pushPlan := .projPush pushWitness

def pushCert : Cert qSelProj pushPlan := .step pushStep .done

/-- The pushdown's end-to-end: same rows satisfied, same plan result. -/
theorem pushAgreesAt (r : RowVals (keepIdsAmt.fields optFields)) :
    weightW (evalQ pushPlan (tableW optRows true)) r
      = weightW (evalQ qSelProj (tableW optRows true)) r :=
  congrArg (fun m => weightW m r) (pushCert.eval_eq optRows)

/-! ## The union-idempotence pipeline -/

def qUnion := qlang!{ from optFields then select (id > 2)
  then union qlang!{ from optFields then select (id > 2) } }

def qUnionOpt : Q optFields optFields := .select (.u64GtLit "id" 2) .table

def unionCert : Cert qUnion qUnionOpt := .step .unionIdem .done

/-- The spec face: the optimized plan satisfies exactly the rows the
    original does — composed through the LANDED bridge. -/
theorem unionOptSatisfies (r : RowVals optFields)
    (h : QSat optFields optRows qUnionOpt r) :
    QSat optFields optRows qUnion r :=
  unionCert.qsat_iff optRows r |>.mp h

example : QSat optFields optRows qUnionOpt (optRow 3 10 500) :=
  QSat.select (QSat.table _ (by decide)) (by decide)

/-! ## The selection-through-join pipeline: the factoring rides the step -/

/-- The self-join on `cust` (the pairs sharing a customer) with a
    selection on the LEFT schema's `id` — the pushdown's target
    (the qlang! pipeline: select → join). -/
def qJoinSel : Q optFields (optFields ++ optFields) :=
  qlang!{ from optFields then join .cust .cust qlang!{ from optFields }
    then select (id == 2) }

/-- The pushed plan: the selection moved into the LEFT branch. -/
def joinPushPlan : Q optFields (optFields ++ optFields) :=
  .join "cust" "cust" (.select (.u64EqLit "id" 2) .table) .table

/-- THE FACTORING WITNESS (the premise as data): the top selection
    reads the LEFT `id` — through the joined row's append it agrees
    with the left-row predicate. -/
theorem joinPushWitness : ∀ (la rb : RowVals optFields),
    Pred.check (.u64EqLit "id" 2) (Row.append la rb)
      = Pred.check (.u64EqLit "id" 2) la := by
  intro la
  cases la with
  | cons a rest =>
      intro rb
      rfl

def joinPushStep : OptStep qJoinSel joinPushPlan := .selJoinPush joinPushWitness

def joinPushCert : Cert qJoinSel joinPushPlan := .step joinPushStep .done

/-- The pushdown's end-to-end: the pushed join evaluates exactly as
    the original. -/
theorem joinPushAgreesAt (r : RowVals (optFields ++ optFields)) :
    weightW (evalQ joinPushPlan (tableW optRows true)) r
      = weightW (evalQ qJoinSel (tableW optRows true)) r :=
  congrArg (fun m => weightW m r) (joinPushCert.eval_eq optRows)

/-! ## The fold pipelines: the redundant + the constant-false selection -/

/-- The redundant selection: `.lit true` folds away (the witness is
    `rfl` — the premise as data). -/
def qRedundant : Q optFields optFields :=
  .select (.lit true) (.select (.u64GtLit "id" 2) .table)

def redCert : Cert qRedundant (.select (.u64GtLit "id" 2) .table) :=
  .step (.selTrue fun _ => rfl) .done

/-- The constant-false selection: the feasibility discipline's
    consumer — a checked-infeasible condition folds to the empty
    relation (the weight face; the fragment has no empty-plan node —
    the named boundary). -/
def qDead : Q optFields optFields :=
  .select (.lit false) (.select (.u64GtLit "id" 2) .table)

/-- The constant-false face at the fixture: the dead selection weighs
    zero at every row (the `evalQ_select_false` row's instance). -/
theorem deadEmptyAt (r : RowVals optFields) :
    weightW (evalQ qDead (tableW optRows true)) r = false := by
  have h := evalQ_select_false (p := Pred.lit false)
    (inner := .select (.u64GtLit "id" 2) .table)
    (h := fun _ => rfl) (m := tableW optRows true)
  show weightW (evalQ (.select (Pred.lit false)
      (.select (.u64GtLit "id" 2) .table)) (tableW optRows true)) r = false
  rw [h]
  exact (zeroW_ok (a := r)).trans (by rfl)

/-! ## The union-commutativity pipeline (the observer discipline) -/

def qUnion2 := qlang!{ from optFields then select (id > 2)
  then union qlang!{ from optFields then select (cust == 10) } }

/-- The reordered plan: the branches swap (the SAME schema — union
    preserves it; the observer discipline: the claim is the canonical
    relation, not a row order). -/
def qUnion2Rev : Q optFields optFields :=
  .union (.select (.u64EqLit "cust" 10) .table) (.select (.u64GtLit "id" 2) .table)

def union2Cert : Cert qUnion2 qUnion2Rev := .step .unionComm .done

theorem union2AgreesAt (r : RowVals optFields) :
    weightW (evalQ qUnion2Rev (tableW optRows true)) r
      = weightW (evalQ qUnion2 (tableW optRows true)) r :=
  congrArg (fun m => weightW m r) (union2Cert.eval_eq optRows)

/-! ## The refusal teeth (the data level) -/

/-- THE PREMISE-LESS PUSHDOWN REFUSES: the wrong `p'` (reading the
    DROPPED `cust`) does not witness — the kernel refuses the
    constructor's payload. -/
theorem badPushWitnessFalse :
    ¬ ∀ r : RowVals optFields,
        Pred.check (.u64GtLit "amt" 100) (keepIdsAmt.pick optFields r)
          = Pred.check (.u64GtLit "cust" 100) r := by
  intro h
  exact absurd (h (optRow 3 10 500)) (by decide)

/-- THE JOIN-PUSHDOWN'S WRONG WITNESS REFUSES: a `p'` reading the
    RIGHT schema's column does not witness the factoring — refuted at
    a concrete left row (id = 2 satisfies the left reading; the
    wrong `p'` reads `cust` = 11). -/
theorem badJoinPushWitnessFalse :
    ¬ ∀ (la rb : RowVals optFields),
        Pred.check (.u64EqLit "id" 2) (Row.append la rb)
          = Pred.check (.u64EqLit "cust" 2) la := by
  intro h
  exact absurd (h (optRow 2 11 50) (optRow 1 10 200)) (by decide)

/-! ## Suite -/

def optimizeSpec : Spec :=
  Spec.ofList "the checked rewriter: qlang! → Cert → the optimized plan evaluates identically"
    (fun _ => do
      -- THE FUSION END-TO-END: the optimized plan's support IS the original's
      assert
        (decide (weightW (evalQ qFused (tableW optRows true)) (optRow 1 10 200) = true)
          && decide (weightW (evalQ qNested (tableW optRows true)) (optRow 1 10 200) = true)
          && decide (weightW (evalQ qFused (tableW optRows true)) (optRow 2 11 50) = false)
          && decide (weightW (evalQ qNested (tableW optRows true)) (optRow 2 11 50) = false))
        "the fused pipeline drifted"
      -- THE CONTRACT at a row: the optimized plan's weight IS the original's
      assert
        (decide (weightW (evalQ qFused (tableW optRows true)) (optRow 1 10 200)
            = weightW (evalQ qNested (tableW optRows true)) (optRow 1 10 200))
          && decide (weightW (evalQ qFused (tableW optRows true)) (optRow 2 11 50)
            = weightW (evalQ qNested (tableW optRows true)) (optRow 2 11 50)))
        "the optimizer's contract drifted"
      -- THE PUSHDOWN END-TO-END: the pushed plan's projected rows agree
      assert
        (decide (weightW (evalQ pushPlan (tableW optRows true)) (projRow 3 500) = true)
          && decide (weightW (evalQ qSelProj (tableW optRows true)) (projRow 3 500) = true)
          && decide (weightW (evalQ pushPlan (tableW optRows true)) (projRow 2 50) = false))
        "the pushdown pipeline drifted"
      -- THE UNION END-TO-END
      assert
        (decide (weightW (evalQ qUnionOpt (tableW optRows true)) (optRow 3 10 500) = true)
          && decide (weightW (evalQ qUnion (tableW optRows true)) (optRow 3 10 500) = true)
          && decide (weightW (evalQ qUnionOpt (tableW optRows true)) (optRow 1 10 200) = false))
        "the union pipeline drifted"
      -- THE SELECTION-THROUGH-JOIN END-TO-END: the pushed join's rows
      -- agree; the pair surviving the selection is pinned + the pair
      -- the selection kills
      assert
        (decide (weightW (evalQ joinPushPlan (tableW optRows true))
              (Row.append (optRow 2 11 50) (optRow 2 11 50)) = true)
          && decide (weightW (evalQ qJoinSel (tableW optRows true))
              (Row.append (optRow 2 11 50) (optRow 2 11 50)) = true)
          && decide (weightW (evalQ joinPushPlan (tableW optRows true))
              (Row.append (optRow 1 10 200) (optRow 1 10 200)) = false)
          && decide (weightW (evalQ qJoinSel (tableW optRows true))
              (Row.append (optRow 1 10 200) (optRow 1 10 200)) = false))
        "the join pushdown pipeline drifted"
      -- THE FOLDS END-TO-END: the redundant selection folds away (same
      -- support as the bare selection); the dead selection is empty
      assert
        (decide (weightW (evalQ (.select (.u64GtLit "id" 2) .table)
              (tableW optRows true)) (optRow 3 10 500) = true)
          && decide (weightW (evalQ qRedundant (tableW optRows true)) (optRow 3 10 500) = true)
          && decide (weightW (evalQ qDead (tableW optRows true)) (optRow 3 10 500) = false)
          && decide (weightW (evalQ qDead (tableW optRows true)) (optRow 1 10 200) = false))
        "the fold pipelines drifted"
      -- THE UNION-COMMUTATIVITY END-TO-END (the observer discipline:
      -- the reordered plan's canonical relation IS the original's)
      assert
        (decide (weightW (evalQ qUnion2Rev (tableW optRows true)) (optRow 1 10 200) = true)
          && decide (weightW (evalQ qUnion2 (tableW optRows true)) (optRow 1 10 200) = true)
          && decide (weightW (evalQ qUnion2Rev (tableW optRows true)) (optRow 2 11 50) = false)
          && decide (weightW (evalQ qUnion2 (tableW optRows true)) (optRow 2 11 50) = false))
        "the union reordering drifted")
    [ ("sabotage: the UNFACTORED pushdown's witness fails at a row (the kernel refuses)",
        fun _ =>
          -- the WRONG claim: the dropped-column reading witnesses the pushdown
          assert
            (decide (Pred.check (.u64GtLit "amt" 100)
                  (keepIdsAmt.pick optFields (optRow 3 10 500))
                = Pred.check (.u64GtLit "cust" 100) (optRow 3 10 500)))
            "control")
    , ("sabotage: fusing DISTINCT union branches loses rows (the shape-check is load-bearing)",
        fun _ =>
          -- the WRONG claim: collapsing the union to one branch is harmless
          assert
            (decide (weightW (evalQ (.union (.select (.u64GtLit "id" 2) .table)
                        (.select (.u64EqLit "cust" 10) .table))
                    (tableW optRows true)) (optRow 1 10 200)
                = weightW (evalQ (.select (.u64GtLit "id" 2) .table)
                    (tableW optRows true)) (optRow 1 10 200)))
            "control")
    , ("sabotage: the WRONG join pushdown (a `p'` reading the left `cust`) drops rows",
        fun _ =>
          -- the WRONG claim: the right-column reading 'witnesses' the push
          assert
            (decide (weightW (evalQ (.join "cust" "cust"
                  (.select (.u64EqLit "cust" 2) .table) .table)
                (tableW optRows true))
              (Row.append (optRow 2 11 50) (optRow 2 11 50)) = true))
            "control") ]
    1 42

/-! ## The axiom self-check -/

/-- info: 'Query.evalQ_select_fuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.evalQ_select_fuse

/-- info: 'Query.evalQ_select_project_pushdown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.evalQ_select_project_pushdown

/-- info: 'Query.Cert.eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.Cert.eval_eq

/-- info: 'Query.Cert.qsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.Cert.qsat_iff

/-- info: 'Query.OptStep.union_branches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Query.OptStep.union_branches

/-- info: 'Query.OptStep.noStepFromBadShape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Query.OptStep.noStepFromBadShape

/-- info: 'Query.evalQ_select_join_pushdown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.evalQ_select_join_pushdown

/-- info: 'Query.evalQ_select_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.evalQ_select_true

/-- info: 'Query.evalQ_select_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.evalQ_select_false

/-- info: 'Query.evalQ_union_comm_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.evalQ_union_comm_bool

/-- info: 'Query.OptStep.noStepFromJoin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Query.OptStep.noStepFromJoin

/-- info: 'Query.OptStep.noStepFromProject' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Query.OptStep.noStepFromProject

end QueryTests.Optimize

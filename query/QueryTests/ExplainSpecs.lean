/-
# QueryTests.ExplainSpecs — the explanations lane's pins

Positive pins + the MANDATORY negative controls (15-patterns #5). The
runner is TestingKit's (`mainOfSuites`). Suites:

1. `the why-present derivation` — the derivation tree as data: the
   worked answer's render names the base FACT and the filter's RULE
   (which facts/rules produced the answer); the negative controls are
   the lying renders (a universal-proof claim; a fabricated column).
2. `the why-absent discipline` — the blocking condition + the NAMED
   completeness assumption; the REFUSAL tooth (no declared assumption
   → a refusal, never a guess — the refusal must NOT claim absence);
   the blocker's soundness exercised at runtime (the blocked row's
   Bool weight IS false); the negative controls are the lying renders
   and the false absence claim.
3. `the key-join's missing partner + the repair seed` — the key-join
   miss renders the missing partner and the pair is absent from the
   result (the soundness's runtime face); the candidate repairs (the
   credit, the keyed removal), the SPECIFICATION'S VERDICTS (residual
   violations as data; the two-step repair is CLEAN), the duplicate's
   honest NONE; the negative controls are the fabricated candidate,
   the premature-clean verdict, and the missing-partner join.

Axiom self-check: `Axioms.lean` (imported by Main) pins #print axioms
over the lane's theorems.
-/

import Query
import SchemaCore.Violate
import TestingKit.Spec
import TestingKit.Harness

open Query SchemaCore TestingKit ZSet

/-! ## The worked fixtures (the violation lane's two-table shape) -/

/-- The transfer row constructor. -/
def tRow (t s d a : UInt64) : RowVals transferFields :=
  .cons (.u64 t) (.cons (.u64 s) (.cons (.u64 d) (.cons (.u64 a) .nil)))

/-- The account row constructor. -/
def aRow (i : UInt64) (o : String) (b : Int64) : RowVals accountFields :=
  .cons (.u64 i) (.cons (.string o) (.cons (.i64 b) .nil))

/-- The fixture's transfer table (one big transfer, one small
    dangling one). -/
def tRows : List (RowVals transferFields) :=
  [tRow 10 1 2 30, tRow 11 1 99 7]

/-- The fixture's world (the account table + the transfer table). -/
def rDb : Db :=
  { accounts := [aRow 1 "ann" 100, aRow 2 "bob" (-5)]
    transfers := tRows }

/-- The filtered query: the big transfers (`amount > 20`). -/
def bigAmt : Q transferFields transferFields :=
  .select (.u64GtLit "amount" 20) .table

/-- WHY PRESENT: the `amount = 30` transfer's derivation. -/
def tPresent :
    Derivation transferFields tRows bigAmt (tRow 10 1 2 30) :=
  .select (.table _ (List.mem_cons_self ..)) (by decide)

/-- WHY ABSENT (blocked): the `amount = 7` transfer — the filter's
    failed predicate, the sub-answer present, under the declared
    completeness. -/
def tAbsent :
    WhyAbsent transferFields tRows bigAmt (tRow 11 1 99 7) :=
  .blocked { scope := "the fixture's transfer table as committed" }
    (.select (QSat.table _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (by decide))

/-- WHY ABSENT (REFUSED): the same shape, NO declared completeness. -/
def tRefused :
    WhyAbsent transferFields tRows bigAmt (tRow 11 1 99 7) :=
  .refusal

/-! ## Suite 1 — the why-present derivation -/

def explainPresentSpec : Spec :=
  Spec.ofList "the why-present derivation: the fact + the rule, as data"
    (fun _ => do
      let ren := tPresent.renderTop
      assert (ren.contains "present: [tid=10; src=1; dst=2; amount=30]")
        s!"the top line does not name the answer: {ren}"
      assert (ren.contains "fact: the base row [tid=10; src=1; dst=2; amount=30]")
        "the render omits the base FACT"
      assert (ren.contains "rule: the filter `amount > 20` accepts it")
        "the render omits the filter's RULE")
    [ ("the derivation claims a universal proof",
        fun _ => assert (tPresent.renderTop.contains "universal proof")
          "the render was honest")
    , ("the derivation names a column the query never mentions",
        fun _ => assert (tPresent.renderTop.contains "on `nope`")
          "the render was honest")
    ] 1 42

/-! ## Suite 2 — the why-absent discipline -/

def explainAbsentSpec : Spec :=
  Spec.ofList "the why-absent discipline: the blocker + the named completeness; the refusal tooth"
    (fun _ => do
      -- the blocked answer: the condition + the NAMED assumption
      let ren := tAbsent.render
      assert (ren.contains "why absent: the row is not in the result")
        "the blocked answer does not name its claim"
      assert (ren.contains "the filter's predicate rejects it: amount > 20")
        s!"the blocked answer omits the failed predicate: {ren}"
      assert (ren.contains
          "under the declared completeness assumption: the fixture's transfer table as committed")
        "the blocked answer omits the declared scope"
      assert (ren.contains "the absence claim is about the declared scope ONLY")
        "the blocked answer omits the scope-only disclaimer"
      -- THE REFUSAL TOOTH: without the assumption, no absence claim
      let ref := tRefused.render
      assert (ref.contains "why absent: REFUSED")
        "the refusal does not name itself"
      assert (ref.contains "absence claim would be a guess")
        "the refusal does not name the guess discipline"
      assert (!(ref.contains "the row is not in the result"))
        "the REFUSAL CLAIMED ABSENCE — the honesty tooth broke"
      -- the blocker's soundness, runtime face: the blocked row IS absent
      assert (weightW (evalQ bigAmt (tableW tRows true)) (tRow 11 1 99 7) = false)
        "the blocker answered absent but the row evaluates present"
      -- the base-absence face
      assert (weightW (evalQ (Q.table (fs := transferFields))
          (tableW tRows true)) (tRow 99 9 9 9) = false)
        "the base-absence control drifted")
    [ ("the refusal claims absence anyway",
        fun _ => assert (tRefused.render.contains "the row is not in the result")
          "the refusal was honest")
    , ("the blocked render omits the declared scope",
        fun _ => assert (!(tAbsent.render.contains "the fixture's transfer table as committed"))
          "the scope was rendered")
    , ("the blocked row evaluates present (the absence claim is false)",
        fun _ => assert (weightW (evalQ bigAmt (tableW tRows true)) (tRow 11 1 99 7) = true)
          "the absence claim held")
    ] 1 42

/-! ## Suite 3 — the key-join's missing partner + the repair seed -/

/-- The miss's two faces, computed (the projection + the lookup both
    reduce on the concrete fixture). -/
theorem tMissProj :
    RowVals.project? transferFields (tRow 12 99 2 5) "src"
      = some ⟨.u64, .u64 99⟩ := rfl

theorem tMissLookup :
    accountDecl.lookup? rDb.accounts ⟨.u64, .u64 99⟩ = none := rfl

def explainRepairSpec : Spec :=
  Spec.ofList "the key-join's missing partner + the repair seed: the candidates + the specification's verdicts"
    (fun _ => do
      -- THE KEY-JOIN'S MISSING PARTNER: the src = 99 transfer's miss
      let miss : KeyJoinMiss accountDecl "src" rDb.accounts
          [tRow 12 99 2 5] (tRow 12 99 2 5) :=
        .keyMiss ⟨.u64, .u64 99⟩ tMissProj tMissLookup
      assert (miss.render.contains "the join's missing partner")
        "the miss does not name the missing partner"
      assert (miss.render.contains "no account row carries the key")
        "the miss does not name the target table"
      -- the soundness's runtime face: the pair is NOT in the key-join
      assert ((keyJoinRows accountDecl "src" rDb.accounts [tRow 12 99 2 5]).length == 0)
        "the missing partner joined anyway"
      -- THE REPAIR SEED: the credit candidate — the credited row's
      -- balance IS zero (the keyed delta's data)
      let vneg := Violation.negative (aRow 2 "bob" (-5))
      match Violation.repair? vneg with
      | some (.account (.update r)) =>
          assert (Pred.renderRow accountFields r == "id=2; owner=\"bob\"; balance=0")
            s!"the credit candidate drifted: {Pred.renderRow accountFields r}"
      | _ => assert false "the credit candidate vanished"
      -- THE SPECIFICATION'S VERDICT: residuals are data — the credit
      -- alone leaves the dangling transfer
      match repairVerdict rDb vneg with
      | some vs =>
          assert (vs.length == 1) s!"the residual count drifted: {vs.length}"
          assert (((vs.map Violation.render).head?.getD "").contains "unresolved dst")
            s!"the residual drifted: {vs.map Violation.render}"
      | none => assert false "the credit verdict vanished"
      -- THE TWO-STEP REPAIR IS CLEAN: credit + remove → no residuals
      let step1 := Db.applyRepair rDb (.account (.update (aRow 2 "bob" 0)))
      let step2 := Db.applyRepair step1 (.transfer (.remove ⟨.u64, .u64 11⟩))
      assert ((violations step2).isEmpty)
        s!"the two-step repair left residuals: {(violations step2).map Violation.render}"
      -- THE HONEST NONE: the duplicate has no single-delta candidate
      assert ((Violation.repair? (Violation.dupId 5)).isNone)
        "the duplicate fabricated a candidate")
    [ ("the duplicate fabricates a candidate",
        fun _ => assert ((Violation.repair? (Violation.dupId 5)).isSome)
          "the duplicate was honest")
    , ("the single credit's verdict is already clean",
        fun _ =>
          match repairVerdict rDb (Violation.negative (aRow 2 "bob" (-5))) with
          | some vs => assert (vs.isEmpty) "the verdict was clean"
          | none => assert false "unreachable")
    , ("the missing partner joins anyway",
        fun _ => assert ((keyJoinRows accountDecl "src" rDb.accounts
            [tRow 12 99 2 5]).length == 1)
          "the key-join refused the miss")
    ] 1 42

/-! ## The driver's suite list -/

def explainSpecs : List Spec :=
  [explainPresentSpec, explainAbsentSpec, explainRepairSpec]

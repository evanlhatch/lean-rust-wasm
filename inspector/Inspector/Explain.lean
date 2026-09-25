/-
# Inspector.Explain — the explain command: the explanations lane rendered

Owner: the explanations-lane agent (the mandate tree, `inspector/`).
Driving decisions: notes/v3/02-data-plane.md §11 (explanations are
query semantics — why present → the supporting derivations; why absent
→ the blocking conditions under the DECLARED completeness assumptions;
which change repairs the constraint → a candidate repair checked
against the specification; a violation renders as the failing fact +
the completeness assumption + the required witness — never a generic
invariant failure) + notes/v3/03-bidirectional.md §5 (the evidence
chain rendered per row — the Why.lean discipline, at query scale).

Pure over the explanations lane's data (`Query.Explain` +
`Query.Repair`) — no IO, so the tests pin the rendering without an
environment; the exe (InspectorMain) owns the `explain` command and
prints this module's `explainReport` (the `whatif` precedent:
report-only, exit 0 — the explanations ARE the answer).

The worked examples (the committed honest data, over the violation
lane's two-table fixture):

- WHY PRESENT: the transfer with `amount = 30` in the filtered query
  — the derivation tree rendered innermost-first (the base fact, then
  the filter's acceptance).
- WHY ABSENT: the same query refusing `amount = 7` — the filter's
  failed predicate, riding the DECLARED completeness scope; and the
  REFUSAL face — the same shape with no declared assumption answers
  with a refusal, never a guess (the honesty tooth).
- THE JOIN'S MISSING PARTNER: the transfer whose `src = 99` resolves
  to no account — the key-join's key miss, named.
- WHICH CHANGE REPAIRS: the negative balance (credit to zero) and the
  dangling transfer (remove by `tid`) — each candidate followed by the
  SPECIFICATION'S OWN VERDICT (the residual violations of the repaired
  world); the duplicate-id violation renders its honest NONE (which
  duplicate wins is a policy, not a derivation).

The five questions (notes/v3/01-core.md):
- root: none — the rendering face over the explanations lane's data.
- carrier grade: none — strings are the human face; the derivation /
  blocker / verdict are the data.
- spine reading: the query lane's explanations rendered per question
  (present / absent / repair) and as the composite report (explain).
- ladder rung: n/a.
- gate row: InspectorTests' explain suite (the pins + the mandatory
  negative controls) + the axiom pins (InspectorTests.Axioms).

Core-only (imports Query.Explain + Query.Repair — the cone rule; the
inspector is host tooling, cone-high).
-/

import Query.Explain
import Query.Repair

namespace Inspector.Explain

open Query SchemaCore

/-! ## The fixture (the violation lane's two-table shape, at explain size) -/

/-- The account row constructor (the fixture's shape). -/
def xAcc (i : UInt64) (o : String) (b : Int64) : RowVals accountFields :=
  .cons (.u64 i) (.cons (.string o) (.cons (.i64 b) .nil))

/-- The transfer row constructor. -/
def xTr (t s d a : UInt64) : RowVals transferFields :=
  .cons (.u64 t) (.cons (.u64 s) (.cons (.u64 d) (.cons (.u64 a) .nil)))

/-- The fixture's world: one negative account, one dangling transfer. -/
def xDb : Db :=
  { accounts := [xAcc 1 "ann" 100, xAcc 2 "bob" (-5)]
    transfers := [xTr 10 1 2 30, xTr 11 1 99 7] }

/-- The fixture's declared completeness scope (the answer's honesty is
    bound to it). -/
def xScope : String := "the explain fixture's tables as committed"

/-! ## The worked query (over the transfer table) -/

/-- The filtered query: the big transfers (`amount > 20`). -/
def bigAmount : Q transferFields transferFields :=
  .select (.u64GtLit "amount" 20) .table

/-- WHY PRESENT — the worked derivation: the `amount = 30` transfer's
    answer, innermost-first (the base fact, then the filter's
    acceptance). -/
def xPresent :
    Derivation transferFields xDb.transfers bigAmount (xTr 10 1 2 30) :=
  .select (.table _ (List.mem_cons_self ..)) (by decide)

/-- WHY ABSENT (blocked) — the `amount = 7` transfer: the filter's
    failed predicate, the sub-answer PRESENT, under the declared
    completeness. -/
def xAbsentFilter :
    WhyAbsent transferFields xDb.transfers bigAmount (xTr 11 1 99 7) :=
  .blocked { scope := xScope }
    (.select (QSat.table _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (by decide))

/-- WHY ABSENT (REFUSED) — the same shape with NO declared
    completeness assumption: the answer is the refusal, never a guess
    (the honesty tooth). -/
def xRefused :
    WhyAbsent transferFields xDb.transfers bigAmount (xTr 11 1 99 7) :=
  .refusal

/-- THE JOIN'S MISSING PARTNER'S TWO FACES, computed (the projection
    + the lookup both reduce on the concrete fixture). -/
theorem xMissProj :
    RowVals.project? transferFields (xTr 12 99 2 5) "src"
      = some ⟨.u64, .u64 99⟩ := rfl

theorem xMissLookup :
    accountDecl.lookup? xDb.accounts ⟨.u64, .u64 99⟩ = none := rfl

def xMiss : KeyJoinMiss accountDecl "src" xDb.accounts
    [xTr 12 99 2 5] (xTr 12 99 2 5) :=
  .keyMiss ⟨.u64, .u64 99⟩ xMissProj xMissLookup

/-! ## The worked repairs (the violation lane's fixture) -/

/-- The negative-balance violation (the credited candidate's target). -/
def xNeg : Violation := .negative (xAcc 2 "bob" (-5))

/-- The dangling-destination violation (the removed candidate's
    target). -/
def xDang : Violation := .danglingDst (xTr 11 1 99 7)

/-- The duplicate-id violation — NO single-delta candidate (the
    honest none). -/
def xDup : Violation := .dupId 5

/-! ## The rendering -/

/-- The candidate delta's line. -/
def renderRepairDelta : RepairDelta → String
  | .account d =>
      match d with
      | .update r => "account ← update [" ++ Pred.renderRow accountFields r ++ "]"
      | .insert r => "account ← insert [" ++ Pred.renderRow accountFields r ++ "]"
      | .remove k => "account ← remove the row keyed " ++ Value.render k.ty k.val
  | .transfer d =>
      match d with
      | .update r => "transfer ← update [" ++ Pred.renderRow transferFields r ++ "]"
      | .insert r => "transfer ← insert [" ++ Pred.renderRow transferFields r ++ "]"
      | .remove k => "transfer ← remove the row keyed " ++ Value.render k.ty k.val

/-- One violation's repair block: the candidate + the SPECIFICATION'S
    OWN VERDICT (the residual violations of the repaired world —
    residuals are data, never hidden). -/
def renderRepair (db : Db) (v : Violation) : String :=
  let head := s!"violation: {v.render}"
  match Violation.repair? v with
  | none =>
      head ++ "\n  candidate repair: NONE — no single keyed delta repairs it\n" ++
        "  (which duplicate wins is a policy, not a derivation; the honest none)"
  | some d =>
      let verdict :=
        match repairVerdict db v with
        | none => "unavailable"
        | some vs =>
            if vs.isEmpty then "CLEAN — the repaired world is valid (valid_iff)"
            else
              "residual violations remain: " ++
                String.intercalate "; " (vs.map Violation.render)
      head ++ "\n  candidate repair: " ++ renderRepairDelta d ++
        "\n  the specification's verdict on the repaired world: " ++ verdict

/-- THE EXPLAIN REPORT — the command face's whole output: why present,
    why absent (blocked + refused), the join's missing partner, and
    the repair candidates with the specification's verdicts. -/
def explainReport : String :=
  String.intercalate "\n\n"
    [ "== the explanations lane (02 §11): why present / why absent / \
        which change repairs =="
    , "-- why present — the supporting derivation\n" ++ xPresent.renderTop
    , "-- why absent — the blocking condition under the declared completeness\n" ++
        xAbsentFilter.render
    , "-- why absent, REFUSED — no completeness assumption, no claim\n" ++
        xRefused.render
    , "-- the join's missing partner (the key-join's absence face)\n" ++ xMiss.render
    , "-- which change repairs the constraint — the candidates + the \
        specification's verdicts\n" ++
        String.intercalate "\n" [renderRepair xDb xNeg, renderRepair xDb xDang,
          renderRepair xDb xDup]
    , "-- the why-absent honesty: a blocked answer's absence claim is PROVED \
        (WhyAbsent.verdict_sound); a refusal makes NO claim — the type forces the \
        completeness assumption to be DECLARED before any absence is claimed" ]

end Inspector.Explain

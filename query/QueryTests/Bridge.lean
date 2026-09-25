/-
# QueryTests.Bridge — the Q↔Typed.Schema bridge's teeth

Positive pins + the MANDATORY negative controls (15-patterns #5) for
`Query.TypedBridge`:

1. `schema` — the field↔column crossing's round trips (Retraction
   grade: `colToField ∘ fieldToCol = id` pinned; the honest gap — the
   nullability bit's non-recovery — pinned as DATA), the schema
   bridge's names/length, the row codec's round trip.
2. `agreement` — the duel's runtime face: `evalQ`'s support vs the
   substrait evaluator's decoded output over the SAME base rows (the
   theorems' content, exercised on the worked query, through the
   `qToRel` lowering — now over the project-covering fragment).
3. `keep` — the wall-1 DISSOLVE's runtime face: the drop projection's
   lowered rel runs the keep walk, and the kept row IS the query lane's
   picked row (`toTypedRow_keep`'s content at runtime).
4. `refusals` — the mandatory negative controls: the join's NAMED
   refusal (QL0001 — the wall-2 disposition, the bridge refuses the
   QUERY), the mis-typed column's resolution refusal (the lowering
   refuses the QUERY where the checker refuses the ROW), the missing
   column, and the NULL cell's decode refusal (the Codec's honest
   partiality).
-/

import Query
import Query.TypedBridge
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness

namespace QueryTests.Bridge

open Query SchemaCore Substrait Substrait.Typed TestingKit ZSet

/-! ## The worked schema -/

-- The enforcement wave's dupDefBodies adjudication: the suites are
-- independent rigs, each carrying its OWN worked-schema fixture; the
-- alpha-equivalence across suites is the shared demo table, not concept
-- duplication (merging would couple the rigs for zero reuse).
@[nolint linter.guestlang.dupDefBodies "the worked schema's per-suite fixture — the suites are independent rigs, not copies"]
def bFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "name", ty := .string },
   { name := "total", ty := .u64 }]

@[nolint linter.guestlang.dupDefBodies "the worked schema's per-suite fixture — the suites are independent rigs, not copies"]
def bRow (i : UInt64) (nm : String) (t : UInt64) : RowVals bFields :=
  .cons (.u64 i) (.cons (.string nm) (.cons (.u64 t) .nil))

def bRows : List (RowVals bFields) :=
  [bRow 1 "ann" 200, bRow 2 "bob" 50, bRow 3 "cee" 300]

/-! ## The queries -/

/-- Selection: the big rows (total > 100). -/
def bigSel : Q bFields bFields := .select (.u64GtLit "total" 100) .table

/-- Union of the base with itself. -/
def unionSelf : Q bFields bFields := .union .table .table

/-- THE DROP PROJECTION (the wall-1 dissolve's fragment face): the
    query keeps `id` and drops `name`/`total` — the constructors apply
    HEAD-FIRST, so keep is the OUTERMOST: keep, skip, skip. -/
@[nolint linter.guestlang.dupDefBodies "the differential twin: body-equality to the qlang! elaboration IS the assertion under test"]
def idOnly : Cols bFields := .keep (.skip (.skip .nil))

def idProj : Q bFields (idOnly.fields bFields) := .project idOnly .table

/-- The projected row for row 1: the kept `id` cell alone. -/
def projRow1 : RowVals (idOnly.fields bFields) := .cons (.u64 1) .nil

/-- Run a lowered query over the bridge reader; the output rows,
    DECODED back to the query lane (the decode's `some` face is the
    soundness theorem's content at runtime). -/
def bridgeRun {gs : List Field} (q : Q bFields gs) :
    List (Option (RowVals gs)) :=
  match qToRel q with
  | .ok rel =>
      match evalRel (bridgeReader bRows) rel ([] : Table (fieldsSchema bFields)) with
      | .ok out => out.map (typedRowToVals _)
      | .error _ => []
  | .error _ => []

/-- The equijoin (the wall-2 fragment face): the bridge REFUSES it —
    the named QL0001, never a fabricated lowering. -/
def joinSelf : Q bFields (bFields ++ bFields) :=
  .join "id" "id" .table .table

/-! ## Suite — the bridge's teeth -/

def bridgeSpec : Spec :=
  Spec.ofList "the Q↔Typed.Schema bridge: the round trips + the agreement + the keep + the refusals"
    (fun _ =>
      assert
        (-- the row codec's round trip (the decode_encode law, runtime)
          decide (typedRowToVals bFields (toTypedRow bFields (bRow 1 "ann" 200))
            = some (bRow 1 "ann" 200))
        -- the schema bridge's names + length
        && decide ((fieldsSchema bFields).names = ["id", "name", "total"])
        && (fieldsSchema bFields).length == 3
        -- the duel: evalQ's support IS the decoded bridge output
        && decide (bridgeRun bigSel
            = [some (bRow 1 "ann" 200), some (bRow 3 "cee" 300)])
        && decide (bridgeRun unionSelf
            = [some (bRow 1 "ann" 200), some (bRow 2 "bob" 50), some (bRow 3 "cee" 300),
               some (bRow 1 "ann" 200), some (bRow 2 "bob" 50), some (bRow 3 "cee" 300)])
        && (weightW (evalQ bigSel (tableW bRows true)) (bRow 2 "bob" 50) = false)
        && (weightW (evalQ bigSel (tableW bRows true)) (bRow 3 "cee" 300) = true)
        -- THE KEEP: the drop projection's duel — both evaluators agree
        && decide (bridgeRun idProj
            = [some projRow1, some (.cons (.u64 2) .nil), some (.cons (.u64 3) .nil)])
        && (weightW (evalQ idProj (tableW bRows true)) projRow1 = true)
        && (match (qToRel idProj).map (fun rel =>
              match evalRel (bridgeReader bRows) rel
                  ([] : Table (fieldsSchema bFields)) with
              | .ok out => out.length
              | .error _ => 0) with
            | .ok n => decide (n = 3)
            | .error _ => false))
        "the bridge's round trips or the agreement drifted")
    [ ("the join LOWERS (caught: the bridge refuses — the wall-2 disposition, QL0001)",
        fun _ => assert
          (match qToRel joinSelf with
          | .error _ => false | .ok _ => true)
          "the join refusal was not exercised")
    , ("the nullability bit IS recoverable (caught: the Retraction's honest gap)",
        fun _ => assert (fieldToCol (colToField ("x", .i64, true)) = ("x", .i64, true))
          "the inverse recovered the bit")
    , ("a NULL cell decodes (caught: the Codec's partial face)",
        fun _ => assert (typedRowToVals [{ name := "a", ty := .u64 }]
          (Substrait.Typed.Row.cons (t := .u64) (name := "a") (n := false) none .nil)
          = some (.cons (.u64 0) .nil))
          "the NULL-face decode refusal was honest")
    , ("a mis-typed column RESOLVES (caught: the lowering refuses the query)",
        fun _ => assert
          (match predToExpr (Pred.u64EqLit "name" 5 : Pred bFields) with
          | .ok _ => true | .error _ => false)
          "the mis-typed column's refusal was honest")
    , ("a missing column RESOLVES (caught: the lowering refuses the query)",
        fun _ => assert
          (match predToExpr (Pred.u64EqLit "missing" 5 : Pred bFields) with
          | .ok _ => true | .error _ => false)
          "the missing column's refusal was honest") ]
    1 42

end QueryTests.Bridge

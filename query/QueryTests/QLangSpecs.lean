/-
# QueryTests.QLangSpecs — the qlang! surface's teeth

The surface's elaboration successes + the MANDATORY mis-typed refusals
as #guard_msgs controls (the structured Diags, QL0002–QL0005) + the
end-to-end: a qlang! query ≡ its hand-written `Q` — the bridge's
agreement theorems consume BOTH (the duel at runtime through
`qToRel` + `evalRel` vs `evalQ`).
-/

import Query
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness

namespace QueryTests.QLangSpecs

open Query SchemaCore Substrait.Typed TestingKit ZSet

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

/-! ## The elaboration successes (the surface is self-typed) -/

-- The differential twin's adjudication (all six below): the
-- hand-written twin's body-equality to the qlang! elaboration IS the
-- assertion under test — the duplication is the spec's content.
@[nolint linter.guestlang.dupDefBodies "the differential twin: body-equality to the hand-written Q IS the assertion under test"]
def qBig := qlang!{ from bFields then select (total > 100) }

/-- Selection + the drop projection. -/
def qAnnIds := qlang!{ from bFields then select (name == "ann") then project [.id] }

/-- Union of two branches (the nested body re-states the base). -/
@[nolint linter.guestlang.dupDefBodies "the differential twin: body-equality to the hand-written Q IS the assertion under test"]
def qUnion := qlang!{ from bFields then select (id > 2)
  then union qlang!{ from bFields then select (name == "bob") } }

/-- The HAND-WRITTEN twins (the end-to-end's other end). -/
@[nolint linter.guestlang.dupDefBodies "the differential twin: body-equality to the qlang! elaboration IS the assertion under test"]
def handBig : Q bFields bFields := .select (.u64GtLit "total" 100) .table

@[nolint linter.guestlang.dupDefBodies "the differential twin: body-equality to the qlang! elaboration IS the assertion under test"]
def handCols : Cols bFields := .keep (.skip (.skip .nil))

def handAnnIds : Q bFields (handCols.fields bFields) :=
  .project handCols (.select (.strEqLit "name" "ann") .table)

@[nolint linter.guestlang.dupDefBodies "the differential twin: body-equality to the qlang! elaboration IS the assertion under test"]
def handUnion : Q bFields bFields :=
  .union (.select (.u64GtLit "id" 2) .table)
         (.select (.strEqLit "name" "bob") .table)

/-- The JOIN stage (the wall-2 dissolve's surface face): the pipeline's
    self-join on `id` ≡ the hand-written equijoin (the appended result
    schema typed free). -/
@[nolint linter.guestlang.dupDefBodies "the differential twin: elaborating to the hand-written Q's body IS the assertion under test"]
def qJoin := qlang!{ from bFields then join .id .id qlang!{ from bFields } }

@[nolint linter.guestlang.dupDefBodies "the differential twin: body-equality to the qlang! elaboration IS the assertion under test"]
def handJoin : Q bFields (bFields ++ bFields) :=
  .join "id" "id" .table .table

/-! ## Suite — the surface's teeth -/

def qlangSpec : Spec :=
  Spec.ofList "the qlang! surface: elaboration ≡ the hand-written Q, both evaluators agree"
    (fun _ =>
      assert
        (-- THE END-TO-END: the qlang! query's evalQ support IS the
          -- hand-written twin's (the weight-pinned agreement)
          (weightW (evalQ qBig (tableW bRows true)) (bRow 3 "cee" 300) = true)
        && (weightW (evalQ qBig (tableW bRows true)) (bRow 2 "bob" 50) = false)
        && (weightW (evalQ handBig (tableW bRows true)) (bRow 3 "cee" 300) = true)
        && (weightW (evalQ handBig (tableW bRows true)) (bRow 2 "bob" 50) = false)
        -- the projected query: the kept row IS the hand-written pick
        && (weightW (evalQ qAnnIds (tableW bRows true)) (.cons (.u64 1) .nil) = true)
        && (weightW (evalQ handAnnIds (tableW bRows true)) (.cons (.u64 1) .nil) = true)
        && (weightW (evalQ qAnnIds (tableW bRows true)) (.cons (.u64 2) .nil) = false)
        -- the union: both branches' rows present
        && (weightW (evalQ qUnion (tableW bRows true)) (bRow 2 "bob" 50) = true)
        && (weightW (evalQ handUnion (tableW bRows true)) (bRow 2 "bob" 50) = true)
        && (weightW (evalQ qUnion (tableW bRows true)) (bRow 1 "ann" 200) = false)
        -- the duel through the BRIDGE: the qlang! query's lowered rel,
        -- evaluated by the substrait evaluator, decodes to the same rows
        && (match qToRel qBig with
            | .ok rel =>
                match evalRel (bridgeReader bRows) rel
                    ([] : Table (fieldsSchema bFields)) with
                | .ok out => decide (out.map (typedRowToVals _)
                  = [some (bRow 1 "ann" 200), some (bRow 3 "cee" 300)])
                | .error _ => false
            | .error _ => false)
        && (match qToRel qAnnIds with
            | .ok rel =>
                match evalRel (bridgeReader bRows) rel
                    ([] : Table (fieldsSchema bFields)) with
                | .ok out => decide (out.map (typedRowToVals _)
                  = [some (.cons (.u64 1) .nil)])
                | .error _ => false
            | .error _ => false)
        -- the JOIN stage: the elaborated equijoin's support IS the
        -- hand-written twin's (the appended rows, ON-satisfying alone)
        && (weightW (evalQ qJoin (tableW bRows true))
              (Query.Row.append (bRow 2 "bob" 50) (bRow 2 "bob" 50)) = true)
        && (weightW (evalQ qJoin (tableW bRows true))
              (Query.Row.append (bRow 1 "ann" 200) (bRow 2 "bob" 50)) = false)
        && (weightW (evalQ handJoin (tableW bRows true))
              (Query.Row.append (bRow 2 "bob" 50) (bRow 2 "bob" 50)) = true)
        -- the join stage's lowered rel agrees through the BRIDGE too
        && (match qToRel qJoin with
            | .ok rel =>
                match evalRel (bridgeReader bRows) rel
                    ([] : Table (fieldsSchema bFields)) with
                | .ok out => decide (out.map (typedRowToVals _)
                  = [some (Query.Row.append (bRow 1 "ann" 200) (bRow 1 "ann" 200)),
                     some (Query.Row.append (bRow 2 "bob" 50) (bRow 2 "bob" 50)),
                     some (Query.Row.append (bRow 3 "cee" 300) (bRow 3 "cee" 300))])
                | .error _ => false
            | .error _ => false))
        "the qlang! surface's agreement drifted")
    [ ("the surface's project REORDERS (caught: the drop is order-preserving —
        the named narrowing)",
        fun _ => assert
          (handCols.fields bFields
            = [{ name := "total", ty := .u64 }, { name := "id", ty := .u64 }])
          "the reordering projection was not refused")
    , ("a mis-typed column's query EVALUATES (caught: the checker refuses the row —
        the elaboration refusal is the guards below)",
        fun _ => assert (weightW (evalQ (.select (.u64EqLit "name" 5) .table)
          (tableW bRows true)) (bRow 1 "ann" 200) = true)
          "the mis-typed column's refusal was not exercised") ]
    1 42

/-! ## The mis-typed refusals (the #guard_msgs controls) -/

/-- error: [QL0002] error: qlang: column `nmae` does not resolve in the current schema (got: nmae) — valid: id, name, total — did you mean: name? -/
#guard_msgs in
def miss1 := qlang!{ from bFields then select (nmae == "ann") }

/-- error: [QL0003] error: qlang: column `name` has type SchemaCore.Ty.string, not u64 — the `== <num>` form needs a u64 column -/
#guard_msgs in
def miss2 := qlang!{ from bFields then select (name == 5) }

/-- error: [QL0004] error: qlang: column `id` is listed twice — the drop projection is duplicate-free (the bag reading of duplicates is the named boundary) -/
#guard_msgs in
def miss3 := qlang!{ from bFields then project [.id, .id] }

/-- error: [QL0005] error: qlang: the union's branch reads a different base schema — valid: the enclosing query's base -/
#guard_msgs in
def miss4 := qlang!{ from bFields
  then union qlang!{ from [{ name := "x", ty := .u64 }] } }

end QueryTests.QLangSpecs

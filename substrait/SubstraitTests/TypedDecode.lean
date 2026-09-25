/- # SubstraitTests.TypedDecode — the typed decode's sweeps + the refusal teeth + the full-circle pin

The decode ladder's executable face (Substrait.Decode — the read
direction: Proto → Typed):

1. The REL LAW's per-arm instances (`decTypedRel?_ok` consumed at
   every rel arm over the worked rels — read/filter/join/aggregate/
   sort/fetch/set; decode ∘ lower is the identity AT THE TYPED LEVEL,
   the law consumed, never re-proved) + the schemas' Bool echo.
2. THE FULL CIRCLE (the wire law lifted, the header's promise):
   `Query.TypedBridge.qToRel` lowers a qlang query to a typed rel, the
   rel lowers to a plan (`toPlan`), the plan encodes to bytes
   (`encPlan`), the wire decodes the bytes (`decPlan?` — the wire
   law's face), and the typed decode recovers the SAME rel
   (`decTypedPlan?_ok` — this lane's law). NOTE: the full-circle
   query's field list is i64 — the encode refuses u64 (the retarget's
   honest face, upstream), so the u64-schema query face cannot ride
   the byte leg.
3. The refusal teeth (mandatory negatives, the SS family's live rows):
   SS0001 (i32 has no typed face), SS0002 (the list element's
   nullability), SS0003 (the out-of-range reference), SS0004 (the
   non-boolean condition), SS0005 (the set's sides disagree), SS0006
   (the base schema's length disagreement + its absence), SS0007 (the
   project's unrecoverable names), SS0008 (the multi-name table path),
   SS0009 (the non-bare-rel plan), SS0010 (the measure's shape).
-/

import Substrait
import Query.TypedBridge
import SubstraitTests.Fixtures
import TestingKit.Spec
import TestingKit.Harness

namespace TypedDecodeTests

open Substrait Substrait.Proto Substrait.Typed Substrait.Decode Substrait.Text
open SchemaCore Query TestingKit

/-! ## the worked fragment (SubstraitTests.Fixtures — the ONE copy,
    Main.lean's rels imported, never retold) -/

/-- The rel's wire face (the lowering's ok arm; every worked rel is in
    the lowering's domain, so the error arm is dead weight). -/
def wireOf {inS outS : Schema} (rel : Rel inS outS) : Proto.Rel :=
  match rel.toProto with | .ok p => p | .error _ => .read (.namedTable []) none

/-! ## 1 — the rel law's per-arm instances (the fragment sweep) -/

/-- The READ arm's instance. -/
theorem readRoundTrip :
    decTypedRel? (wireOf readUnits) = .ok (AnyRel.mk units units readUnits) :=
  decTypedRel?_ok readUnits _ rfl (by simp only [readUnits, Rel.decodable])

/-- The FILTER arm's instance. -/
theorem filterRoundTrip :
    decTypedRel? (wireOf filterAdd) = .ok (AnyRel.mk units units filterAdd) :=
  decTypedRel?_ok filterAdd _ rfl
    (by simp only [filterAdd, readUnits, Rel.decodable])

/-- The JOIN arm's instance. -/
theorem joinRoundTrip :
    decTypedRel? (wireOf demoJoin)
      = .ok (AnyRel.mk (sa ++ sb) (sa ++ sb) demoJoin) :=
  decTypedRel?_ok demoJoin _ rfl ⟨trivial, trivial⟩

/-- The AGGREGATE arm's instance (the measures' arity tie is the
    domain condition's face: the singleton's tie is `rfl`). -/
theorem aggRoundTrip :
    decTypedRel? (wireOf aggRel)
      = .ok (AnyRel.mk units (aggregateOut units aggGrouping aggMeasures) aggRel) := by
  refine decTypedRel?_ok aggRel _ rfl ⟨?_, trivial⟩
  intro m hm
  simp only [aggMeasures, List.mem_singleton] at hm
  obtain rfl := hm
  rfl

/-- The SORT arm's instance. -/
theorem sortRoundTrip :
    decTypedRel? (wireOf sortRel) = .ok (AnyRel.mk units units sortRel) :=
  decTypedRel?_ok sortRel _ rfl (by simp only [sortRel, readUnits, Rel.decodable])

/-- The FETCH arm's instance. -/
theorem fetchRoundTrip :
    decTypedRel? (wireOf fetchRel) = .ok (AnyRel.mk units units fetchRel) :=
  decTypedRel?_ok fetchRel _ rfl (by simp only [fetchRel, readUnits, Rel.decodable])

/-- The SET arm's instance. -/
theorem setRoundTrip :
    decTypedRel? (wireOf setRel) = .ok (AnyRel.mk units units setRel) :=
  decTypedRel?_ok setRel _ rfl ⟨trivial, trivial⟩

/-- The decoded rels' schema face (the Bool echo of the law instances:
    every worked rel decodes .ok with its indices preserved). -/
def decFace (p : Proto.Rel) : Option (Nat × Nat) :=
  match decTypedRel? p with
  | .ok (AnyRel.mk i o _) => some (i.length, o.length)
  | .error _ => none

/-! ## 2 — the full circle (qlang → plan → bytes → wire → typed) -/

/-- The full-circle query's field list: i64 — the encode refuses u64
    (the retarget's honest face, upstream), so the u64-schema query
    face cannot ride the byte leg (the module header's note). -/
def circFields : List Field := [{ name := "n", ty := .i64 }]

/-- The qlang query: select over the base table (a literal-true
    predicate — the bridge's predToExpr face at its total arm). -/
def circQ : Q circFields circFields := .select (.lit true) .table

/-- The lowering's rel. -/
def circRel : Rel (fieldsSchema circFields) (fieldsSchema circFields) :=
  match qToRel circQ with
  | .ok r => r
  | .error _ => .read "query.base" (fieldsSchema circFields)

/-- The rel's plan. -/
def circPlan : Plan :=
  match circRel.toPlan with
  | .ok p => p
  | .error _ => Plan.empty

/-- THE FULL CIRCLE (the pin, the law's consumption): the typed decode
    of the lowered plan recovers the SAME rel the qlang lowering
    produced — `decTypedPlan?_ok` at the bridge's rel. -/
theorem fullCircle :
    decTypedPlan? circPlan
      = .ok (AnyRel.mk (fieldsSchema circFields) (fieldsSchema circFields) circRel) :=
  decTypedPlan?_ok circRel circPlan rfl
    (by
      -- circRel's match reduces to the filter rel (qToRel of the
      -- literal-true select, whnf); the decodable face reads through it
      have h : circRel = Typed.Rel.filter
          (Typed.Rel.read "query.base" (fieldsSchema circFields))
          (Expr.literal false (Value.bool true)) := rfl
      rw [h]
      simp [Rel.decodable])

/-! ## 3 — the refusal teeth (the SS family's live rows) -/

/-- The typed decode's refusal code (the tooth's read). -/
def decCode (p : Proto.Rel) : Option String :=
  match decTypedRel? p with
  | .error d => some d.code.code
  | .ok _ => none

/-- The plan face's refusal code. -/
def decPlanCode (p : Plan) : Option String :=
  match decTypedPlan? p with
  | .error d => some d.code.code
  | .ok _ => none

def ptI64 : PType := PType.i64 .required

/-! ## the suite -/

def typedDecodeSpec : Spec :=
  Spec.ofList "the typed decode: the rel law's arms + the full circle"
    (fun _ =>
      assert
        -- the per-arm law instances' Bool echo: every worked rel
        -- decodes .ok with its schema indices preserved
        (decFace (wireOf readUnits) == some (2, 2)
          && decFace (wireOf filterAdd) == some (2, 2)
          && decFace (wireOf demoJoin) == some (2, 2)
          && decFace (wireOf aggRel) == some (2, 2)
          && decFace (wireOf sortRel) == some (2, 2)
          && decFace (wireOf fetchRel) == some (2, 2)
          && decFace (wireOf setRel) == some (2, 2)
          -- the full circle's byte leg: the plan encodes and the wire
          -- decodes the bytes back to the plan (the wire law's face)
          && Substrait.Wire.inDomainPlan circPlan
          && (Substrait.Wire.decPlan? ((Substrait.Wire.encPlan circPlan).length + 1)
                (Substrait.Wire.encPlan circPlan) == some circPlan)
          -- the full circle's typed leg, executable echo: the BYTES'
          -- plan typed-decodes to the bridge's schemas (the SAME-rel
          -- claim is the file-level `fullCircle` theorem, the law's
          -- consumption)
          && (match Substrait.Wire.decPlan? ((Substrait.Wire.encPlan circPlan).length + 1)
                (Substrait.Wire.encPlan circPlan) with
              | some p =>
                  match decTypedPlan? p with
                  | .ok (AnyRel.mk i o _) =>
                      i == fieldsSchema circFields
                        && o == fieldsSchema circFields
                  | .error _ => false
              | none => false))
        "the typed decode's pins drifted")
    [ ("SS0001: the decode accepts i32 (caught: no typed face)",
        fun _ => assert
          (decCode (.read (.namedTable ["t"])
              (some { fields := [PType.i32 .required], names := ["a"] }))
            == none)
          "the i32 type decoded")
    , ("SS0002: the decode accepts a nullable list element (caught)",
        fun _ => assert
          (decCode (.read (.namedTable ["t"])
              (some { fields := [.list (PType.i64 .nullable) .required],
                      names := ["a"] }))
            == none)
          "the nullable list element decoded")
    , ("SS0003: the decode accepts an out-of-range reference (caught)",
        fun _ => assert
          (decCode (.filter (.field { ordinal := 9 }) (wireOf readUnits))
            == none)
          "the out-of-range reference decoded")
    , ("SS0004: the decode accepts a non-boolean condition (caught)",
        fun _ => assert
          (decCode (.filter (.literal { literalType := .i64 0 }) (wireOf readUnits))
            == none)
          "the non-boolean condition decoded")
    , ("SS0005: the decode accepts a set with disagreeing sides (caught)",
        fun _ => assert
          (decCode (.set .unionAll (wireOf readUnits)
              (.read (.namedTable ["u"])
                (some { fields := [ptI64], names := ["a"] })))
            == none)
          "the disagreeing set decoded")
    , ("SS0006: the decode accepts a fields/names length mismatch (caught)",
        fun _ => assert
          (decCode (.read (.namedTable ["t"])
              (some { fields := [ptI64, ptI64], names := ["a"] }))
            == none)
          "the length disagreement decoded")
    , ("SS0006: the decode accepts an ABSENT base schema (caught)",
        fun _ => assert
          (decCode (.read (.namedTable ["t"]) none) == none)
          "the schemaless read decoded")
    , ("SS0007: the decode accepts a project node (caught: no output names)",
        fun _ => assert
          (decCode (.project [] (wireOf readUnits)) == none)
          "the project decoded")
    , ("SS0008: the decode accepts a multi-name table path (caught)",
        fun _ => assert
          (decCode (.read (.namedTable ["a", "b"])
              (some { fields := [ptI64], names := ["a"] }))
            == none)
          "the multi-name path decoded")
    , ("SS0009: the plan face accepts a rooted plan (caught)",
        fun _ => assert
          (decPlanCode { functions := []
                         relations := [PlanRel.root ["n"] (wireOf readUnits)] }
            == none)
          "the rooted plan decoded")
    , ("SS0010: the decode accepts a non-invocation measure (caught)",
        fun _ => assert
          (decCode (.aggregate [] [.literal { literalType := .i64 0 }]
              (wireOf readUnits))
            == none)
          "the non-invocation measure decoded") ]
    1 42

end TypedDecodeTests

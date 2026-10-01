/-
# SubstraitTests — the port's pins: the typed layer + the format + the evaluator

Positive pins + the MANDATORY negative controls (15-patterns #5). The
runner is TestingKit's (`mainOfSuites`). Suites:

1. `typed` — the worked schema's pins: the by-name resolution (the
   `HasCol` ordinals, the `resolves` discipline exercised), the
   lowering's wire shapes (literal/field/call), the WF BRIDGE read
   back off the wire (the lowered ordinals are in range — the
   theorem's face, exercised at the checker level), the plan's
   declaration law, the width agreement — now over the SLICE-2 arms
   too (aggregate/sort/fetch/set: the computed aggregate schema, the
   preserved widths).
2. `types` — the format's round trips: the scalar round trip (the
   LAW's face + the run-entry COROLLARY), the list round trips
   (values — the deferred arm, the Text module header's note), the
   follow-set discipline, and the rel grammar's NAME-TOKEN round
   trips (`ofName_self`'s face) + the canonical rel LINES' spellings.
3. `eval` — the evaluator's known answers: the aggregate's buckets +
   count, the filter's bridge face (restricts), the join's conjunctive
   pairs + the left padding, the unionAll append, the fetch window,
   and the bridge kernels (u64/string/bool equality, u64 gt, not —
   `Query.TypedBridge`'s Pred lowering is the consumer).
4. Negative controls (mandatory): the malformed-type refusal, the u64
   wire refusal (the retarget's honest face), the sort/unionDistinct/
   unknown-function eval refusals (the named boundaries).
5. `wire` (SubstraitTests.Wire) — the protobuf wire's LCG sweeps (the
   drawn-fragment round trips + the truncation sweep) + the negative
   controls (the off-domain plan's gate + wire refusals, the trailing
   byte, the WireTarget row's pins).
6. `typedDecode` (SubstraitTests.TypedDecode) — the typed decode's
   face (Phase 4): the rel law's per-arm instances + the FULL-CIRCLE
   pin (qlang qToRel → toPlan → encPlan → decPlan? → decTypedPlan? =
   the same rel) + the refusal teeth (SS0001–SS0010).

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the lane's theorems — core-triple-only or the build fails.
-/

import Substrait
import Query.TypedBridge
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import SubstraitTests.Axioms
import SubstraitTests.Wire
import SubstraitTests.Fixtures
import SubstraitTests.TypedDecode

open Substrait Substrait.Proto Substrait.Typed Substrait.Text SchemaCore TestingKit

/-- the wire-equality pin helper (the Except face's read; the BEq over
    Except is not the pin's surface — the match is). -/
def toProtoIs {s : Schema} {t : Ty} {n : Bool} (e : Expr s t n) (p : Expression) : Bool :=
  match e.toProto with | .ok q => q == p | .error _ => false

/-- The width-agreement pin helper (the theorem's face, at the value
    level): the lowered rel's wire width equals the TYPED output
    schema's length. -/
def widthCheck {inS : Schema} {outS : Schema} (rel : Rel inS outS) : Bool :=
  match rel.toProto with
  | .ok p => p.width == outS.length
  | .error _ => false

/-- The wire's expected field-reference shape. -/
def expectedFieldRef : Expression := .field { ordinal := 0 }

/-- The type text's expected values (the round-trip tests read them). -/
def typeTexts : List (PType × String) :=
  [(PType.bool .required, "boolean"), (PType.i64 .nullable, "i64?"),
   (PType.string .required, "string"),
   (PType.list (PType.i64 .required) .required, "list<i64>"),
   (PType.list (PType.string .nullable) .nullable, "list<string?>?")]

/-! ## suite 1 — the typed layer's pins -/

def typedSpec : Spec :=
  Spec.ofList "the typed layer: by-name resolution, the lowering, the WF bridge, the plan"
    (fun _ =>
      assert
        -- the by-name resolution: the ordinal is the INSTANCE's index
        (toProtoIs (col "health" .i64 true : Expr units .i64 true) expectedFieldRef
          -- the literal's payload rides SchemaCore.Value (the retarget)
          && toProtoIs (litVal (.i64 42) : Expr units .i64 false)
               (.literal { literalType := .i64 42, nullable := false })
          -- the call's lowering: name + args + the explicit output type
          && (match addHealth0.toProto with
              | .ok (.scalarFunction nm args out) =>
                  nm == "add" && args.length == 2
                    && out == PType.i64 Nullability.nullable
              | _ => false)
          -- the WF bridge, READ OFF THE WIRE: the lowered call's
          -- ordinals are in range (the theorem's face, checked)
          && (match addHealth0.toProto with
              | .ok p => p.ordsLt units.length
              | .error _ => false)
          -- the plan's declaration law: the used functions are declared
          && (match filterAdd.toPlan with
              | .ok pl => pl.functions == ["gt", "add"]
                    && pl.relations.length == 1
              | .error _ => false)
          -- the type text's spellings (the table's both faces)
          && (typeTexts.map (fun (t, s) => typeText t == s) |>.all id)
          -- the width agreement over ALL arms (the computed
          -- aggregate schema included; the fuller-plan rows)
          && widthCheck readUnits
          && widthCheck filterAdd
          && widthCheck demoJoin
          && widthCheck aggRel
          && widthCheck sortRel
          && widthCheck fetchRel
          && widthCheck setRel
          && widthCheck crossRel
          && widthCheck writeRel
          -- the cross's wire shape: NO condition, two children (the
          -- CrossRel face); the write's: names + op + the table schema
          -- echo (fields = the typed output schema's lowered cols)
          && (match crossRel.toProto with
              | .ok (.cross l r) => l.width == 1 && r.width == 1
              | _ => false)
          && (match writeRel.toProto with
              | .ok (.write nms op ts _) =>
                  nms == ["mydb", "units"] && op == WriteOp.insert
                    && ts.names == ["health", "regen"]
              | _ => false)
          -- the aggregate's wire shape: grouping exprs then measures,
          -- both as plain scalar-function expressions
          && (match aggRel.toProto with
              | .ok (.aggregate gs ms _) =>
                  gs.length == 1 && ms.length == 1
                    && (match ms.head! with
                        | .scalarFunction nm args _ => nm == "count" && args.isEmpty
                        | _ => false)
              | _ => false)
          -- the sort key's wire shape: expr + the direction token's enum
          && (match sortRel.toProto with
              | .ok (.sort keys _) =>
                  keys.length == 1
                    && keys.head!.direction == SortDirection.ascNullsFirst
              | _ => false)
          -- the measure name rides the plan's declaration list too
          && (match aggRel.toPlan with
              | .ok pl => pl.functions == ["count"]
              | .error _ => false))
        "the typed layer's pins drifted")
    [ ("the WF bridge accepts an out-of-range ordinal (caught: it does not)",
        fun _ => assert
          (Expression.ordsLt (.field { ordinal := 9 }) units.length = true)
          "the out-of-range ordinal was not exercised")
    , ("the u64 literal lowers to the wire (caught: it refuses)",
        fun _ => assert
          (match (litVal (SchemaCore.Value.u64 7) : Expr units .u64 false).toProto with
          | .error _ => false
          | .ok _ => true)
          "the u64 refusal was not exercised")
    , ("the measure's arity drifts silently (caught: the wire shape pins it)",
        fun _ => assert
          (match aggRel.toProto with
          | .ok (.aggregate _ ms _) => ms.length == 2
          | _ => false)
          "the measure-arity drift was not exercised") ]
    1 42

/-! ## suite 2 — the format's round trips -/

/-- The scalar round trip: the LAW's face — parse (emit t ++ rest) =
    some (t, rest) at sufficient fuel, for every scalar ctor + wire
    nullability + clean suffix. The four CLEAN-SUFFIX samples (the
    empty-suffix rows) are THEOREM-PINNED, not just swept:
    `Substrait.Text.parseType_typeText_scalar` discharges the general
    law (every scalar ctor × nullability × FollowClean suffix) — these
    value-level rows are the law's executable echo, kept as a drift
    tripwire over the concrete spellings. -/
def scalarRoundTrips : Bool :=
  let samples : List (PType × List Char) :=
    [(PType.bool .required, []), (PType.bool .nullable, [',']),
     (PType.i32 .required, []), (PType.i32 .nullable, [')']),
     (PType.i64 .required, []), (PType.i64 .nullable, [',']),
     (PType.string .required, []), (PType.string .nullable, [')'])]
  samples.all (fun (t, rest) =>
    parseTypeGo (typeChars t).length ((typeChars t) ++ rest) == some (t, rest))

/-- The list round trips (VALUES — the deferred arm; the Text module
    header's note): one level + nested. -/
def listRoundTrips : Bool :=
  let t1 : PType := .list (PType.i64 .required) .required
  let t2 : PType := .list (PType.string .nullable) .nullable
  let t3 : PType := .list (PType.list (PType.bool .nullable) .required) .required
  [t1, t2, t3].all (fun t =>
    parseTypeGo (typeChars t).length ((typeChars t) ++ []) == some (t, []))

/-- The name-token tables' round trips (the `ofName_self` theorems'
    face, at the value level): every sort direction, set op, and join
    type's own token parses back to it. -/
def nameTokenRoundTrips : Bool :=
  [.ascNullsFirst, .descNullsFirst].all (fun d =>
    sortDirOfName (sortDirName d) == some d)
  && [.unionAll, .unionDistinct].all (fun op =>
    setOpOfName (setOpName op) == some op)
  && [.inner, .outer, .left, .right].all (fun jt =>
    joinTypeOfName (joinTypeName jt) == some jt)

/-- The canonical rel lines' spellings (the substrait-explain shapes,
    pinned on the worked schema's lowered rels). -/
def wireRead : Proto.Rel :=
  match readUnits.toProto with | .ok p => p | .error _ => .read (.namedTable []) none

def wireFilter : Proto.Rel :=
  match filterAdd.toProto with | .ok p => p | .error _ => wireRead

def wireAgg : Proto.Rel :=
  match aggRel.toProto with | .ok p => p | .error _ => wireRead

def wireSort : Proto.Rel :=
  match sortRel.toProto with | .ok p => p | .error _ => wireRead

def wireFetch : Proto.Rel :=
  match fetchRel.toProto with | .ok p => p | .error _ => wireRead

def wireSet : Proto.Rel :=
  match setRel.toProto with | .ok p => p | .error _ => wireRead

def relTexts : List (Proto.Rel × String) :=
  [(wireRead, "Read[units => health:i64?, regen:i64?]"),
   (wireFilter,
     "Filter[gt(add($0,0:i64):i64?,0:i64):boolean? => $0, $1]\n" ++
     "  Read[units => health:i64?, regen:i64?]"),
   (wireAgg,
     "Aggregate[$1 => $1, count():i64]\n" ++
     "  Read[units => health:i64?, regen:i64?]"),
   (wireSort,
     "Sort[($0, &AscNullsFirst) => $0, $1]\n" ++
     "  Read[units => health:i64?, regen:i64?]"),
   (wireFetch,
     "Fetch[limit=10 => $0, $1]\n" ++
     "  Read[units => health:i64?, regen:i64?]"),
   (wireSet,
     "Set[&UnionAll => $0, $1]\n" ++
     "  Read[units => health:i64?, regen:i64?]\n" ++
     "  Read[units => health:i64?, regen:i64?]")]

def typesSpec : Spec :=
  Spec.ofList "the format: the round-trip law + the list round trips + the name tokens + the rel lines"
    (fun _ =>
      assert (scalarRoundTrips && listRoundTrips && nameTokenRoundTrips
        && (typeText (PType.list (PType.i64 .nullable) .required) == "list<i64?>")
        -- the round-trip COROLLARY's face: the run entry's own fuel
        && (parseType (PType.i64 .nullable) (typeChars (PType.i64 .nullable))
              == some (PType.i64 .nullable, []))
        && (relTexts.map (fun (r, s) => relText r == s) |>.all id))
      "the format's round trips drifted")
    [ ("the parse accepts a truncated list type (caught: it refuses)",
        fun _ => assert
          ((parseTypeGo 20 ("list<".toList ++ "i64".toList)).isSome)
          "the truncated list type was not exercised")
    , ("the parse accepts a non-type text (caught: it refuses)",
        fun _ => assert
          ((parseTypeGo 20 ("widget".toList ++ [])).isSome)
          "the garbage text was not exercised")
    , ("the i8 token parses (caught: it is outside the narrowed table)",
        fun _ => assert
          ((parseTypeGo 5 ("i8".toList ++ [])).isSome)
          "the i8 token was not exercised")
    , ("the rel text renders a drifted width (caught: the output clause pins it)",
        fun _ => assert
          (relText wireFilter == "Filter[gt(add($0,0:i64):i64?,0:i64):boolean? => $0, $1, $2]\n" ++
            "  Read[units => health:i64?, regen:i64?]")
          "the width drift was not exercised") ]
    1 42

/-! ## suite 3 — the evaluator's known answers -/

/-- The units table's runtime rows: one row with a NULL health cell
    (the SQL-null discipline's exercise). -/
def unitRows : Table units :=
  [Row.ofCells units [some ⟨.i64, .i64 10⟩, some ⟨.i64, .i64 5⟩],
   Row.ofCells units [none, some ⟨.i64, .i64 7⟩]]

/-- The units reader. -/
def unitReader : Reader units :=
  fun name => match name with
  | "units" => .ok unitRows
  | other => .error s!"eval: unknown table {other}"

/-- The aggregate's first output row's cell payloads (grouping key,
    then the count) — the buckets appear in first-seen key order. -/
def aggOutCells : Option Int64 × Option Int64 :=
  match evalRel unitReader aggRel unitRows with
  | .ok (r0 :: _) =>
      (match r0.get 0 with | some ⟨_, some (.i64 v)⟩ => some v | _ => none,
       match r0.get 1 with | some ⟨_, some (.i64 v)⟩ => some v | _ => none)
  | _ => (none, none)

/-- The filter's output length: the NULL-health row DROPS (the cond is
    NULL → false — the query lane's `select` reading, executable). -/
def filterOutLen : Nat :=
  match evalRel unitReader filterAdd unitRows with
  | .ok rows => rows.length
  | .error _ => 42

/-- The join's inner pairs: a=0 matches b=1's side (the conjunctive
    reading, executable). -/
def saRows : Table sa := [Row.ofCells sa [some ⟨.i64, .i64 0⟩]]

def sbRows : Table sb := [Row.ofCells sb [some ⟨.i64, .i64 1⟩]]

def joinOutLen : Nat :=
  match evalJoin .inner joinCond saRows sbRows with
  | .ok rows => rows.length
  | .error _ => 42

/-- The LEFT join's padding: with no right rows, the unmatched left row
    survives at `none` padding (the full width is in the type). -/
def leftJoinOutLen : Nat :=
  match evalJoin .left joinCond saRows ([] : Table sb) with
  | .ok rows => rows.length
  | .error _ => 42

/-- The unionAll's append face. -/
def setOutLen : Nat :=
  match evalRel unitReader setRel unitRows with
  | .ok rows => rows.length
  | .error _ => 42

/-- The fetch window's face. -/
def fetchOutLen : Nat :=
  match evalRel unitReader fetchRel unitRows with
  | .ok rows => rows.length
  | .error _ => 42

/-- The cross's product face: 2 x 2 rows, full width (the condition-
    free join's kernel — evalJoin at the always-true cond). The full-
    width stream feeds BOTH children through the split-half readers
    (the join arm's reader discipline). -/
def saFullRows : Table (sa ++ sb) :=
  [Row.append (Row.ofCells sa [some ⟨.i64, .i64 0⟩])
    (Row.ofCells sb [some ⟨.i64, .i64 1⟩]),
   Row.append (Row.ofCells sa [some ⟨.i64, .i64 2⟩])
    (Row.ofCells sb [some ⟨.i64, .i64 3⟩])]

def crossOutLen : Nat :=
  match evalRel (fun _ => .ok saFullRows) crossRel saFullRows with
  | .ok rows => rows.length
  | .error _ => 42

/-- The write's refusal face: the evaluator is read-only (the named
    boundary — the rows' destiny is the consumer's table store). -/
def writeRefused : Bool :=
  match evalRel unitReader writeRel unitRows with
  | .error _ => true
  | .ok _ => false

/-- The unknown kernel's loud refusal face. -/
def unknownFnRefused : Bool :=
  match evalFunc { name := "frob", args := [], ret := .i64, retNullable := false }
    [] with
  | .error _ => false
  | .ok _ => true

/-- The bridge kernels' runtime cells (the `Σ`-packaged arguments). -/
def bridgeCellU64 (u : UInt64) : Σ t, Option (Value t) := ⟨.u64, some (.u64 u)⟩
def bridgeCellStr (s : String) : Σ t, Option (Value t) := ⟨.string, some (.string s)⟩
def bridgeCellBool (b : Bool) : Σ t, Option (Value t) := ⟨.bool, some (.bool b)⟩

def evalSpec : Spec :=
  Spec.ofList "the evaluator: the aggregate, the filter bridge's face, the join, the window"
    (fun _ =>
      assert
        -- the aggregate: group regen=5 first, count 1 row in it
        (aggOutCells == (some (5 : Int64), some (1 : Int64))
          -- the filter RESTRICTS: the null-health row drops
          && filterOutLen == 1
          -- the join's conjunctive core: one matching pair
          && joinOutLen == 1
          -- the left join's padding: the unmatched left survives
          && leftJoinOutLen == 1
          -- the unionAll's append: 2 + 2
          && setOutLen == 4
          -- the fetch window: limit 10 over 2 rows
          && fetchOutLen == 2
          -- the cross's product: 2 x 2 (the always-true cond's join)
          && crossOutLen == 4
          -- the write's read-only refusal (the named boundary)
          && writeRefused
          -- the bridge kernels (Query.TypedBridge's Pred lowering is
          -- the consumer): u64 equal/gt, string + bool equality, not
          && (match evalFunc Query.u64EqSig
                [bridgeCellU64 3, bridgeCellU64 3] with
              | .ok (some (.bool b)) => b | _ => false)
          && (match evalFunc Query.u64EqSig
                [bridgeCellU64 3, bridgeCellU64 4] with
              | .ok (some (.bool b)) => !b | _ => false)
          && (match evalFunc Query.u64GtSig
                [bridgeCellU64 4, bridgeCellU64 3] with
              | .ok (some (.bool b)) => b | _ => false)
          && (match evalFunc Query.strEqSig
                [bridgeCellStr "x", bridgeCellStr "x"] with
              | .ok (some (.bool b)) => b | _ => false)
          && (match evalFunc Query.notSig [bridgeCellBool true] with
              | .ok (some (.bool b)) => !b | _ => false)
          && (match evalFunc Query.notSig [bridgeCellBool false] with
              | .ok (some (.bool b)) => b | _ => false))
        "the evaluator's pins drifted")
    [ ("the evaluator implements sort (caught: it refuses loudly)",
        fun _ => assert
          (match evalRel unitReader (Rel.sort readUnits ([] : List (SortKey units))) unitRows with
          | .error _ => false
          | .ok _ => true)
          "the sort refusal was not exercised")
    , ("the evaluator implements unionDistinct (caught: it refuses loudly)",
        fun _ => assert
          (match evalRel unitReader (.set .unionDistinct readUnits readUnits) unitRows with
          | .error _ => false
          | .ok _ => true)
          "the unionDistinct refusal was not exercised")
    , ("the evaluator knows every extension function (caught: it refuses loudly)",
        fun _ => assert
          unknownFnRefused
          "the unknown-function refusal was not exercised")
    , ("the erased field read returns a cell at ordinal 9 of an empty row (caught: none)",
        fun _ => assert
          (match (Row.nil : Row []).get 9 with
          | none => false
          | some _ => true)
          "the out-of-range read was not exercised") ]
    1 42

/-! ## the driver -/

def main : IO UInt32 :=
  mainOfSuites [("SubstraitTests",
    [typedSpec, typesSpec, evalSpec, wireSpec, TypedDecodeTests.typedDecodeSpec])]

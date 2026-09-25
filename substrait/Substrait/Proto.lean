/-
# Substrait.Proto — the wire-faithful plan model (the honest minimal core)

Owner: the substrait port agent (the mandate tree, `substrait/`).
Provenance: ported FRESH from `legacy/lean/substrait/Substrait/Proto/*`
(the message-shape content), NARROWED to the fragment the new tree's
consumers need (notes/v3/14-build-map.md's `substrait` row: "the Proto
types + typed layer + Grammar tables port"). This is the seed, not the
whole format — the narrowings are DELIBERATE and named:

- `PType`: `bool/i32/i64/string/list` only. The legacy's i8/i16/fp32/
  fp64/binary/decimal/map/struct/userDefined arms port with their first
  consumers (the emitter columns / typed-layer ops that need them).
  NOTE: SchemaCore's closed `Ty` HAS no unsigned scalar — the typed
  layer's `u64` lowers to a REFUSAL (Substrait.Typed), not to a lossy
  cast.
- `Expression`: `literal/field/scalarFunction`. The legacy's ifThen/
  cast/subquery port with their grammar rows (Phase 4's decode ladder).
- `scalarFunction` carries the function NAME directly, not a wire
  anchor: the anchor-assignment ladder (legacy `Typed/ToProto.lean`'s
  ExtCtx — first-use ordering, urn anchors, `=== Extensions` sections)
  ports when the extensions section is this slice's consumer. A
  name-carrying seed is honest: the wire anchor is a plan-local index
  into a table the seed does not yet build.
- `Rel`: `read/filter/project/join/aggregate/sort/fetch/set` — the
  relational core + the slice-2 rows (below). `cross/write/extension*`
  port with their text grammar rows' first consumers.
- `Plan`: relations + the distinct function-name list (the seed's
  stand-in for the extension-declaration table); the version header
  ports with the anchors (above).

Nullability keeps all three proto values (`unspecified` included — the
wire value exists); the TYPED layer never produces it (the legacy
contract, kept).

The slice-2 growth (the aggregate/sort/fetch/set rows, ported from
legacy `Proto/Rel.lean`'s message shapes, every narrowing named):

- `SortDirection`: `ascNullsFirst/descNullsFirst` only. The legacy's
  unspecified/ascNullsLast/descNullsLast/clustered port with their
  text-table rows' consumers (the emitter writes what the decoder
  reads — the narrowed table keeps the bijection closed).
- `SetOp`: `unionAll/unionDistinct`. The legacy's minus/intersection
  families port with their eval kernels (the evaluator refuses
  non-union ops loudly — the legacy's own skeleton discipline).
- `Rel.aggregate`: groupings and measures are BOTH plain `Expression`
  lists on the wire (the legacy's `AggregateMeasure` structure
  collapses: a measure's function invocation IS a scalar-function
  expression — the wire shape's narrowing is named here).
- `Rel.sort`: `SortField` (expr + direction); `Rel.fetch`: limit/
  offset options; `Rel.set`: BINARY (the legacy's N-input `SetRel` —
  the typed layer's same-schema discipline makes two the honest
  arity; the N-input shape ports with its first consumer).

Plain total data, no proofs (the low-level currency: the typed layer
lowers into it, the text emitter reads it).

MECHANICS NOTE: the ordinals fold is a STRUCTURAL mutual family
(`ordinals`/`ordinalsList`) — a flatMap spelling compiles to WF
recursion, kernel-opaque, and the typed-correctness bridge's
definitional reductions die (06's structural-recursion discipline; the
probe's finding).

The five questions (notes/v3/01-core.md):
- root: Universe — first-order data mirroring the proto message shapes.
- carrier grade: none — no semantic mapping at this layer.
- spine reading: none — the lowering TARGET the typed layer emits into.
- ladder rung: rung 1 — plain structural definitions, `rfl`-reducible.
- gate row: the axiom report (Substrait is gated; no own gate rows —
  the byte-tie applies when the text artifact lands).
-/

namespace Substrait.Proto

/-! ## nullability + types -/

/-- Proto `Type.Nullability` (values 0,1,2). -/
inductive Nullability where
  | unspecified
  | nullable
  | required
deriving Repr, BEq, DecidableEq, Inhabited

/-- Proto `Type` — the narrow skeleton set (see the module header).
    Nullability rides every constructor (the wire shape). -/
inductive PType where
  | bool (n : Nullability)
  | i32 (n : Nullability)
  | i64 (n : Nullability)
  | string (n : Nullability)
  | list (elem : PType) (n : Nullability)
deriving Repr, BEq, Inhabited

/-- The nullability of a type (helper accessor). -/
def PType.nullability : PType → Nullability
  | .bool n => n
  | .i32 n => n
  | .i64 n => n
  | .string n => n
  | .list _ n => n

/-- Rebuild a type at a given nullability (the lowering's
    withNullable face; the 5-arm rebuild is the whole body). -/
def PType.setNull (n : Nullability) : PType → PType
  | .bool _ => .bool n
  | .i32 _ => .i32 n
  | .i64 _ => .i64 n
  | .string _ => .string n
  | .list e _ => .list e n

/-- setNull sets ONLY the nullability (the lowering law the typed
    layer's width agreement stands on). -/
theorem PType.setNull_nullability (t : PType) (n : Nullability) :
    (t.setNull n).nullability = n := by
  cases t <;> rfl

/-! ## expressions -/

/-- Proto `Expression.Literal.LiteralType` (the narrow scalar set). -/
inductive LiteralType where
  | bool (b : Bool)
  | i32 (v : Int)
  | i64 (v : Int)
  | string (s : String)
deriving Repr, BEq, Inhabited

/-- Proto `Expression.Literal` — a typed literal with its nullability flag. -/
structure Literal where
  literalType : LiteralType
  nullable : Bool := false
deriving Repr, BEq, Inhabited

/-- Proto `Expression.FieldReference` — a root-anchored ordinal reference
    (the `direct_reference { struct_field { field } }` shape; the deeper
    segment port with their grammar rows). -/
structure FieldReference where
  ordinal : Nat
deriving Repr, BEq, Inhabited

/-- Proto `Expression` — the narrow union (see the module header). -/
inductive Expression where
  | literal (lit : Literal)
  | field (ref : FieldReference)
  | scalarFunction (name : String) (args : List Expression) (outputType : PType)
deriving Repr, BEq, Inhabited

/- The field ordinals an expression references (the WF bridge's read
    side: the typed layer's lowering keeps them in range —
    Substrait.Typed's `Expr.toProto_ords`). The list arm is the MUTUAL
    sibling: a flatMap compiles the fold to WF recursion —
    kernel-opaque, killing the bridge's definitional reductions (06's
    structural-recursion discipline, the probe's finding). -/
mutual
  def Expression.ordinals : Expression → List Nat
    | .literal _ => []
    | .field f => [f.ordinal]
    | .scalarFunction _ args _ => Expression.ordinalsList args

  def Expression.ordinalsList : List Expression → List Nat
    | [] => []
    | e :: es => (Expression.ordinals e) ++ (Expression.ordinalsList es)
end

/-- Every ordinal an expression references is `< bound`. -/
def Expression.ordsLt (e : Expression) (bound : Nat) : Bool :=
  e.ordinals.all (· < bound)

/-- The list face of the bridge's statement (the spine's predicate —
    `ordsLt` at the list level). -/
def Expression.ordsLtList (es : List Expression) (bound : Nat) : Bool :=
  (Expression.ordinalsList es).all (· < bound)

/-! ## relations -/

/-- Proto `NamedStruct` — a struct type plus column names. -/
structure NamedStruct where
  fields : List PType
  names : List String
deriving Repr, BEq, Inhabited

/-- Proto `ReadRel.ReadType` — NamedTable (`names` is the dotted path).
    The legacy's virtualTable port with its first consumer. -/
inductive ReadType where
  | namedTable (names : List String)
deriving Repr, BEq, Inhabited

/-- Proto `join_rel.JoinType` — the narrow display set. The legacy's
    semi/anti/single/mark rows port with their width rows' consumers. -/
inductive JoinType where
  | inner | outer | left | right
deriving Repr, BEq, DecidableEq, Inhabited

/-- The output width of a join, given the left/right input widths
    (the shared width rule — the legacy's ONE-width-rule discipline:
    emitter and decoder read the same function). -/
def JoinType.width (jt : JoinType) (l r : Nat) : Nat :=
  match jt with
  | .inner | .outer | .left | .right => l + r

/-- The width law: a join's output width is the SUM of the input widths
    for every join type in the narrow set (the typed layer's width
    agreement theorem stands on this). -/
theorem JoinType.width_add (jt : JoinType) (l r : Nat) :
    jt.width l r = l + r := by
  cases jt <;> rfl

/-- Proto `sort_field.SortDirection` — the narrow display set (the
    module header's named narrowing). -/
inductive SortDirection where
  | ascNullsFirst | descNullsFirst
deriving Repr, BEq, DecidableEq, Inhabited

/-- Proto `SortField` — a sort key: expression + direction. -/
structure SortField where
  expr : Expression
  direction : SortDirection
deriving Repr, BEq, Inhabited

/-- Proto `set_rel.SetOp` — the narrow display set (the module
    header's named narrowing). -/
inductive SetOp where
  | unionAll | unionDistinct
deriving Repr, BEq, DecidableEq, Inhabited

/-- Proto `Rel` — the narrow relation union (read/filter/project/join/
    aggregate/sort/fetch/set; see the module header). -/
inductive Rel where
  | read (readType : ReadType) (baseSchema : Option NamedStruct)
  | filter (condition : Expression) (input : Rel)
  | project (expressions : List Expression) (input : Rel)
  | join (joinType : JoinType) (left : Rel) (right : Rel) (condition : Expression)
  | aggregate (groupings : List Expression) (measures : List Expression) (input : Rel)
  | sort (keys : List SortField) (input : Rel)
  | fetch (limit : Option Nat) (offset : Option Nat) (input : Rel)
  | set (op : SetOp) (left : Rel) (right : Rel)
deriving Repr, BEq, Inhabited

/-- The declared name of a rel (the substrait-explain `NamedRelation`). -/
def Rel.name : Rel → String
  | .read _ _ => "Read"
  | .filter _ _ => "Filter"
  | .project _ _ => "Project"
  | .join _ _ _ _ => "Join"
  | .aggregate _ _ _ => "Aggregate"
  | .sort _ _ => "Sort"
  | .fetch _ _ _ => "Fetch"
  | .set _ _ _ => "Set"

/-- The output width of a rel (the wire-side width rule the typed
    layer's lowering-agreement theorem consumes). A Read's width is its
    base schema's field count (0 when absent). -/
def Rel.width : Rel → Nat
  | .read _ baseSchema =>
      match baseSchema with
      | some s => s.fields.length
      | none => 0
  | .filter _ input => input.width
  | .project expressions input => input.width + expressions.length
  | .join jt left right _ => jt.width left.width right.width
  -- the grouping keys + the measures (the legacy relWidth's aggregate
  -- row: `groupingExpressions.length + measures.length`)
  | .aggregate groupings measures _ => groupings.length + measures.length
  | .sort _ input => input.width
  | .fetch _ _ input => input.width
  -- the typed layer's same-schema discipline makes the set's width the
  -- shared width (the legacy's N-input average narrows to binary)
  | .set _ left _ => left.width

/-! ## the plan container -/

/-- Proto `PlanRel` — either a bare relation or a `RelRoot` (with output
    names). -/
inductive PlanRel where
  | rel (r : Rel)
  | root (names : List String) (input : Rel)
deriving Repr, BEq, Inhabited

/-- Proto `Plan` — the top-level container, narrowed to relations (the
    version header + extension declarations port with the anchor
    ladder; see the module header). `functions` collects the distinct
    scalar-function names a plan uses, first-use order — the seed's
    stand-in for the wire's extension-declaration table. -/
structure Plan where
  functions : List String
  relations : List PlanRel
deriving Repr, BEq, Inhabited

/-- The empty plan. -/
def Plan.empty : Plan := { functions := [], relations := [] }

end Substrait.Proto

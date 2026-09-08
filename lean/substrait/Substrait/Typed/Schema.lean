/-
# Substrait.Typed.Schema

Schema-indexed types for the typed layer.

A `Schema` is a list of columns: `name × SType × nullability`.  Column lookup
is by name via the `HasCol` typeclass, resolved by head/tail instance search
over _literal_ schema abbreviations.  This mirrors lean-linq's `Row`/`HasCol`
pattern; the two things that make it work are:

1. Schemas must be declared as `abbrev` (definitions the elaborator sees
   through) — instance search unfolds abbreviations but not regular `def`s.
2. The head instance has `priority := high` so a name matching the head column
   never falls through to the recursive instance.

Nullability convention (matching lean-linq's C#-style divergence): a bare
type is *required* (`n := false`) and `n := true` is nullable.  The emitter
always writes *explicit* Substrait nullability (REQUIRED/NULLABLE, never
UNSPECIFIED).

The `SType` universe is the user-facing type language.  It is nullability-free:
nullability is carried separately (the `n : Bool` index on `Expr`, and the
third component of a schema column).  `toProtoType` in `Substrait.Typed`
maps both into the wire `Proto.Type`.
-/
import Substrait.Proto.Type

namespace Substrait.Typed

/- User-facing type universe: nests like the wire `Proto.PType` but without
   nullability; extension types are referenced by (urn, name, params) and
   their wire anchors are assigned at emission. -/
mutual
  inductive SType where
    | bool
    | i8 | i16 | i32 | i64
    | fp32 | fp64
    | string | binary
    | decimal (precision scale : Nat)
    | list (elem : SType)
    | map (key value : SType)
    | struct (fields : List SType)
    | userDefined (urn : String) (name : String) (params : List SParam)
  deriving Repr, BEq, Inhabited

  /-- Parameter values for parameterized/user-defined types (wire `Type.Parameter`). -/
  inductive SParam where
    | boolean (b : Bool)
    | integer (i : Int)
    | string (s : String)
    | enum (e : String)
    | null (t : SType)
    | dataType (t : SType)
  deriving Repr, BEq, Inhabited
end

/-- A schema column: name × type × nullable. -/
abbrev SchemaCol := String × SType × Bool

/-- A schema is a list of columns, in ordinal order. -/
abbrev Schema := List SchemaCol

/-- Column count. -/
def Schema.width : Schema → Nat
  | [] => 0
  | _ :: tl => 1 + Schema.width tl

/-- The nth column of a schema, or `none` when out of range. -/
def Schema.get? : Schema → Nat → Option SchemaCol
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: tl, n + 1 => Schema.get? tl n

/-- Column *types* only (used by `toProto` for `NamedStruct`). -/
def Schema.types : Schema → List SType
  | [] => []
  | (_, t, _) :: tl => t :: Schema.types tl

/-- Column names only. -/
def Schema.names : Schema → List String
  | [] => []
  | (name, _, _) :: tl => name :: Schema.names tl

-- `(x, y, z) :: tl` pattern for a triple cons — syntax sugar kept explicit.

/--
`HasCol s name t n` — evidence that column `name` sits at a known ordinal in
`s`, with type `t` and nullability `n`.  Both `t` and `n` are `outParam`s so a
lookup like `col "health" .i32 true` synthesizes the instance and yields the
ordinal.  The search is purely syntactic (head/tail over literal schema
abbreviations); misspelled columns fail at elaboration time with a
`failed to synthesize` `HasCol` message.
-/
class HasCol (s : Schema) (name : String) (t : outParam SType) (n : outParam Bool) where
  /-- The ordinal of the column in `s`. -/
  index : Nat
  /-- The resolution is CORRECT: the schema's `index`-th column IS this
      (name, type, nullability) triple. Before this field the class carried
      only the ordinal — a proof obligation stated in the doc comment but
      unchecked. -/
  resolves : Schema.get? s index = some (name, t, n)

instance (priority := high) : HasCol ((name, t, n) :: s) name t n where
  index := 0
  resolves := rfl

instance [h : HasCol s name t n] : HasCol ((name', t', n') :: s) name t n where
  index := h.index + 1
  resolves := h.resolves

/-- A resolved column reference: its ordinal and name. -/
structure Column where
  name : String
  ordinal : Nat
deriving Repr, BEq, Inhabited

/--
`column name t n` — resolve a column name to its ordinal via `HasCol`
instance search (head/tail over the literal schema abbreviation).
-/
def column (name : String) (t : SType) (n : Bool) [h : HasCol s name t n] : Column :=
  { name := name, ordinal := h.index }

/-! ## Proof-carrying type equality (used by `DslExpr` compilation) -/

/-- A proven-or-not answer, `Prop`-safe (`Option` cannot hold a `Prop`). -/
inductive EqAns (a b : α) : Type where
  | yes (h : a = b)
  | no

mutual
  /--
  Runtime type equality with a proof.  The negation branch is proof-free
  (`.no` carries no obligation): this is a *directed* check — the DSL only
  needs positive evidence to reindex a typed expression.  Mirrors the
  pattern-refinement `Eval.castCell` uses (no `DecidableEq` class available
  for open `SType` terms).
  -/
  def SType.eqAns : (a b : SType) → EqAns a b
    | .bool, .bool     => .yes rfl
    | .i8, .i8         => .yes rfl
    | .i16, .i16       => .yes rfl
    | .i32, .i32       => .yes rfl
    | .i64, .i64       => .yes rfl
    | .fp32, .fp32     => .yes rfl
    | .fp64, .fp64     => .yes rfl
    | .string, .string => .yes rfl
    | .binary, .binary => .yes rfl
    | .decimal p s, .decimal p' s' =>
        if hp : p = p' then
          if hs : s = s' then .yes (by rw [hp, hs]) else .no
        else .no
    | .list e1, .list e2 =>
        match SType.eqAns e1 e2 with
        | .yes h => .yes (by rw [h])
        | .no => .no
    | .map k1 v1, .map k2 v2 =>
        match SType.eqAns k1 k2, SType.eqAns v1 v2 with
        | .yes hk, .yes hv => .yes (by rw [hk, hv])
        | _, _ => .no
    | .struct fs1, .struct fs2 =>
        match eqListType fs1 fs2 with
        | .yes h => .yes (by rw [h])
        | .no => .no
    | .userDefined u1 n1 p1, .userDefined u2 n2 p2 =>
        if hu : u1 = u2 then
          if hn : n1 = n2 then
            match eqListParam p1 p2 with
            | .yes h => .yes (by rw [hu, hn, h])
            | .no => .no
          else .no
        else .no
    | _, _ => .no

  /-- Pairwise `SType` list equality (in the mutual block so the terminator
  sees structural recursion). -/
  def eqListType : (xs ys : List SType) → EqAns xs ys
    | [], [] => .yes rfl
    | x :: xs, y :: ys =>
        match SType.eqAns x y, eqListType xs ys with
        | .yes hx, .yes hys => .yes (by rw [hx, hys])
        | _, _ => .no
    | [], _ => .no
    | _, [] => .no

  /-- Parameter equality (wire `Type.Parameter` values). -/
  def SParam.eqAns : (a b : SParam) → EqAns a b
    | .boolean b1, .boolean b2 =>
        if h : b1 = b2 then .yes (by rw [h]) else .no
    | .integer i1, .integer i2 =>
        if h : i1 = i2 then .yes (by rw [h]) else .no
    | .string s1, .string s2 =>
        if h : s1 = s2 then .yes (by rw [h]) else .no
    | .enum e1, .enum e2 =>
        if h : e1 = e2 then .yes (by rw [h]) else .no
    | .null t1, .null t2 =>
        match SType.eqAns t1 t2 with
        | .yes h => .yes (by rw [h])
        | .no => .no
    | .dataType t1, .dataType t2 =>
        match SType.eqAns t1 t2 with
        | .yes h => .yes (by rw [h])
        | .no => .no
    | _, _ => .no

  /-- Pairwise `SParam` list equality. -/
  def eqListParam : (xs ys : List SParam) → EqAns xs ys
    | [], [] => .yes rfl
    | x :: xs, y :: ys =>
        match SParam.eqAns x y, eqListParam xs ys with
        | .yes hx, .yes hys => .yes (by rw [hx, hys])
        | _, _ => .no
    | [], _ => .no
    | _, [] => .no
end

end Substrait.Typed

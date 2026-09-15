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
  deriving Repr, Inhabited

  /-- Parameter values for parameterized/user-defined types (wire `Type.Parameter`). -/
  inductive SParam where
    | boolean (b : Bool)
    | integer (i : Int)
    | string (s : String)
    | enum (e : String)
    | null (t : SType)
    | dataType (t : SType)
  deriving Repr, Inhabited
end

/-- A schema column: name × type × nullable. -/
abbrev SchemaCol := String × SType × Bool

/-- A schema is a list of columns, in ordinal order. -/
abbrev Schema := List SchemaCol

/-- The nth column of a schema, or `none` when out of range. -/
def Schema.get? : Schema → Nat → Option SchemaCol
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: tl, n + 1 => Schema.get? tl n

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


/-! ## Decidable equality (the lawful BEq route)

Hand-written structural equality + the `beq_iff_eq` family (the DERIVED
`BEq`'s generated matcher is not a proof surface — the hand-written
function is). The instances live next to the type. `eqAns` above stays:
the proof-carrying directed answer for elaboration-time reflection. -/

mutual
  /-- Structural equality over the schema types. -/
  def SType.beq : SType → SType → Bool
    | .bool, .bool => true
    | .i8, .i8 => true
    | .i16, .i16 => true
    | .i32, .i32 => true
    | .i64, .i64 => true
    | .fp32, .fp32 => true
    | .fp64, .fp64 => true
    | .string, .string => true
    | .binary, .binary => true
    | .decimal p s, .decimal p' s' => p == p' && s == s'
    | .list e1, .list e2 => SType.beq e1 e2
    | .map k1 v1, .map k2 v2 => SType.beq k1 k2 && SType.beq v1 v2
    | .struct fs1, .struct fs2 => SType.beqFields fs1 fs2
    | .userDefined u1 n1 p1, .userDefined u2 n2 p2 =>
        u1 == u2 && n1 == n2 && SParam.beqParams p1 p2
    | _, _ => false

  /-- Pairwise list equality (in the mutual block so the terminator sees
      structural recursion). -/
  def SType.beqFields : List SType → List SType → Bool
    | [], [] => true
    | x :: xs, y :: ys => SType.beq x y && SType.beqFields xs ys
    | _, _ => false

  /-- Structural equality over the wire `Type.Parameter` values. -/
  def SParam.beq : SParam → SParam → Bool
    | .boolean b1, .boolean b2 => b1 == b2
    | .integer i1, .integer i2 => i1 == i2
    | .string s1, .string s2 => s1 == s2
    | .enum e1, .enum e2 => e1 == e2
    | .null t1, .null t2 => SType.beq t1 t2
    | .dataType t1, .dataType t2 => SType.beq t1 t2
    | _, _ => false

  /-- Pairwise parameter-list equality. -/
  def SParam.beqParams : List SParam → List SParam → Bool
    | [], [] => true
    | x :: xs, y :: ys => SParam.beq x y && SParam.beqParams xs ys
    | _, _ => false
end

mutual
  /-- The lawful direction both ways: structural equality IS equality. -/
  theorem SType.beq_iff_eq : ∀ (a b : SType), SType.beq a b = true ↔ a = b
    | .bool, b => by cases b <;> simp [SType.beq]
    | .i8, b => by cases b <;> simp [SType.beq]
    | .i16, b => by cases b <;> simp [SType.beq]
    | .i32, b => by cases b <;> simp [SType.beq]
    | .i64, b => by cases b <;> simp [SType.beq]
    | .fp32, b => by cases b <;> simp [SType.beq]
    | .fp64, b => by cases b <;> simp [SType.beq]
    | .string, b => by cases b <;> simp [SType.beq]
    | .binary, b => by cases b <;> simp [SType.beq]
    | .decimal p s, b => by cases b <;> simp [SType.beq]
    | .list e1, b => by
        cases b <;> simp [SType.beq]
        rename_i e2
        exact ⟨fun h => by rw [SType.beq_iff_eq e1 e2 |>.1 h],
               fun h => by cases h; exact SType.beq_iff_eq e1 e1 |>.2 rfl⟩
    | .map k1 v1, b => by
        cases b <;> simp [SType.beq]
        rename_i k2 v2
        exact ⟨fun h => by
                have ⟨hk, hv⟩ := h
                rw [SType.beq_iff_eq k1 k2 |>.1 hk, SType.beq_iff_eq v1 v2 |>.1 hv]
                exact ⟨rfl, rfl⟩,
               fun h => by
                have ⟨hk, hv⟩ := h
                subst hk; subst hv
                exact ⟨SType.beq_iff_eq _ _ |>.2 rfl, SType.beq_iff_eq _ _ |>.2 rfl⟩⟩
    | .struct fs1, b => by
        cases b <;> simp [SType.beq]
        rename_i fs2
        exact ⟨fun h => by rw [SType.beqFields_iff_eq fs1 fs2 |>.1 h],
               fun h => by cases h; exact SType.beqFields_iff_eq fs1 fs1 |>.2 rfl⟩
    | .userDefined u1 n1 p1, b => by
        cases b <;> simp [SType.beq]
        rename_i u2 n2 p2
        exact ⟨fun h => by
                have ⟨⟨hu, hn⟩, hp⟩ := h
                rw [hu, hn, SParam.beqParams_iff_eq p1 p2 |>.1 hp]
                exact ⟨rfl, rfl, rfl⟩,
               fun h => by
                have ⟨hu, hn, hp⟩ := h
                subst hu; subst hn; subst hp
                exact ⟨⟨rfl, rfl⟩, SParam.beqParams_iff_eq _ _ |>.2 rfl⟩⟩

  theorem SType.beqFields_iff_eq : ∀ (xs ys : List SType),
      SType.beqFields xs ys = true ↔ xs = ys
    | [], [] => by simp [SType.beqFields]
    | [], _ :: _ => by simp [SType.beqFields]
    | _ :: _, [] => by simp [SType.beqFields]
    | x :: xs, y :: ys => by
        simp only [SType.beqFields, Bool.and_eq_true]
        exact ⟨fun ⟨hx, hxs⟩ => by
                rw [SType.beq_iff_eq x y |>.1 hx, SType.beqFields_iff_eq xs ys |>.1 hxs],
               fun h => by cases h; exact ⟨SType.beq_iff_eq x x |>.2 rfl,
                SType.beqFields_iff_eq xs xs |>.2 rfl⟩⟩

  theorem SParam.beq_iff_eq : ∀ (a b : SParam), SParam.beq a b = true ↔ a = b
    | .boolean b1, b => by cases b <;> simp [SParam.beq]
    | .integer i1, b => by cases b <;> simp [SParam.beq]
    | .string s1, b => by cases b <;> simp [SParam.beq]
    | .enum e1, b => by cases b <;> simp [SParam.beq]
    | .null t1, b => by
        cases b <;> simp [SParam.beq]
        rename_i t2
        exact ⟨fun h => by rw [SType.beq_iff_eq t1 t2 |>.1 h],
               fun h => by cases h; exact SType.beq_iff_eq t1 t1 |>.2 rfl⟩
    | .dataType t1, b => by
        cases b <;> simp [SParam.beq]
        rename_i t2
        exact ⟨fun h => by rw [SType.beq_iff_eq t1 t2 |>.1 h],
               fun h => by cases h; exact SType.beq_iff_eq t1 t1 |>.2 rfl⟩

  theorem SParam.beqParams_iff_eq : ∀ (xs ys : List SParam),
      SParam.beqParams xs ys = true ↔ xs = ys
    | [], [] => by simp [SParam.beqParams]
    | [], _ :: _ => by simp [SParam.beqParams]
    | _ :: _, [] => by simp [SParam.beqParams]
    | x :: xs, y :: ys => by
        simp only [SParam.beqParams, Bool.and_eq_true]
        exact ⟨fun ⟨hx, hxs⟩ => by
                rw [SParam.beq_iff_eq x y |>.1 hx, SParam.beqParams_iff_eq xs ys |>.1 hxs],
               fun h => by cases h; exact ⟨SParam.beq_iff_eq x x |>.2 rfl,
                SParam.beqParams_iff_eq xs xs |>.2 rfl⟩⟩
end

instance : BEq SType := ⟨SType.beq⟩
instance : LawfulBEq SType where
  eq_of_beq := fun h => (SType.beq_iff_eq _ _).1 h
  rfl := (SType.beq_iff_eq _ _).2 rfl

instance : DecidableEq SType := fun a b => decidable_of_iff _ (SType.beq_iff_eq a b)

instance : BEq SParam := ⟨SParam.beq⟩
instance : LawfulBEq SParam where
  eq_of_beq := fun h => (SParam.beq_iff_eq _ _).1 h
  rfl := (SParam.beq_iff_eq _ _).2 rfl

instance : DecidableEq SParam := fun a b => decidable_of_iff _ (SParam.beq_iff_eq a b)


end Substrait.Typed
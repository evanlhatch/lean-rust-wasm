/-
# SchemaLang.Ty — the schema language's type universe

Target-NEUTRAL by design (the schema-lang rule): option/result/future/stream
are constructors HERE; how each target renders them is the target lowering's
job (WIT: option<T>/result<T,E>/future<T>/stream<T>; OpenAPI: nullable +
oneOf; Vortex: nullable flag). No wire knowledge lives in this module.

Type-driven surfaces, per the four-addresses axis (TOOLKIT Part 1):

- (a) data: `Ty` is a first-order inductive — emitters fold it, the oracle
  reads it, it serializes.
- (b) type-level: `Value : Ty → Type` — a value payload INDEXED by the
  type (a `.bool` value cannot carry a string). This is the bridge that
  later gives schema-typed validators and test-vector generation for free;
  Lean forbids Σ/nested-inductive under GADT params, so nothing here needs
  the wrapper (flatland's AnyExpr lesson — no heterogeneous lists yet).
- (c) proposition: `Ty.wellFormed` over a universe of known names.
- (d) instance: `EqAns` — DIRECTED, proof-carrying equality (`.yes h` /
  `.no`, no `Decidable` instance needed for open terms; the flatland
  Typed/Schema pattern). The `.yes` proof is what makes compat evidence
  and reindexing compositional downstream.

Deliberately omitted (containment, lean-v3 Part 10): nullability (WIT
`option<T>` IS the nullability; targets that use flags derive it),
generics (WIT has none — monomorphization is the emitters' job),
refinement predicates (the schema-indexed package owns `{x // P x}`;
v1 payloads are plain types).
-/

namespace SchemaLang

/-! ## The universe -/

/-- A named type reference: must resolve to a record/variant in the item
    universe (checked by `wellFormed`, not by this type). -/
abbrev TyRef := String

/-- The schema type universe. -/
inductive Ty where
  | bool
  | u8 | u16 | u32 | u64
  | i8 | i16 | i32 | i64
  | f32 | f64
  | string
  | bytes
  | option (α : Ty)
  | result (ok err : Ty)
  | list (α : Ty)
  | future (α : Ty)
  | stream (α : Ty)
  | ty (name : TyRef)
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Value payloads, indexed by type ((a) → (b) bridge)

A `Value t` can only hold data of type `t` — test vectors, fuzz corpora
and validators consume these; a mismatched payload is unconstructible. -/

mutual
inductive Value : Ty → Type where
  | bool : Bool → Value .bool
  | u8 : UInt8 → Value .u8
  | u16 : UInt16 → Value .u16
  | u32 : UInt32 → Value .u32
  | u64 : UInt64 → Value .u64
  | i8 : Int8 → Value .i8
  | i16 : Int16 → Value .i16
  | i32 : Int32 → Value .i32
  | i64 : Int64 → Value .i64
  | f32 : Float32 → Value .f32
  | f64 : Float → Value .f64
  | string : String → Value .string
  | bytes : List UInt8 → Value .bytes
  | some : {t : Ty} → Value t → Value (.option t)
  | none : {t : Ty} → Value (.option t)
  | ok : {ok err : Ty} → Value ok → Value (.result ok err)
  | err : {ok err : Ty} → Value err → Value (.result ok err)
  | list : {t : Ty} → VList t → Value (.list t)
  | future : {t : Ty} → Value t → Value (.future t)
  | stream : {t : Ty} → VList t → Value (.stream t)

/-- A value list. Nested inductives (`List (Value t)` inside the GADT)
    are forbidden by the kernel — the flatland `AnyExpr` lesson — so the
    list shape is its own sibling inductive in the mutual block. -/
inductive VList : Ty → Type where
  | nil : {t : Ty} → VList t
  | cons : {t : Ty} → Value t → VList t → VList t
end

/-! ## Proof-carrying directed equality

`EqAns a b` is `.yes h` (with the equational proof — composable evidence
for reindexing/compat) or `.no` (deliberately proof-free: the check is
directed, failure needs no justification).

NOT hand-rolled: `Ty` derives `DecidableEq` (first-order inductive — the
flatland `SType`/`SParam` mutual-block trap doesn't apply here), so the
decision is one `dite` and the proof rides the branch. The wrapper exists
only because `Option` cannot carry a `Prop`. -/

inductive EqAns {α : Type} (a b : α) : Type where
  | yes (h : a = b)
  | no

/-- The directed decision: kernel-derived decidability, proof in the
    `.yes` branch. -/
def Ty.eqAns (a b : Ty) : EqAns a b :=
  if h : a = b then .yes h else .no

end SchemaLang

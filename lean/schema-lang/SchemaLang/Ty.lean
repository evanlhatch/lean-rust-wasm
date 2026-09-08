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

import Substrait.Typed.Schema

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

`EqAns` lives in `Substrait.Typed` (the original — same `.yes h` /
`.no` shape, proof-carrying directed equality). SchemaLang consumes the
substrait type; no local re-declaration.

`Ty` derives `DecidableEq` (first-order inductive — the flatland
`SType`/`SParam` mutual-block trap doesn't apply here), so the decision
is one `dite` and the proof rides the branch. The wrapper exists only
because `Option` cannot carry a `Prop`. -/

/-- The directed decision: kernel-derived decidability, proof in the
    `.yes` branch. Returns substrait's `EqAns`. -/
def Ty.eqAns (a b : Ty) : Substrait.Typed.EqAns a b :=
  if h : a = b then .yes h else .no

/-! ## Reification: the schema universe as Lean types

`toType` turns data-describing-types into TYPES. Named references are
open-world: one `RefTy` instance per schema type; an unresolved
reference fails at ELABORATION TIME the moment `toType` is used - the
universe check becomes a type-class check, strictly stronger than the
runtime `wellFormed` scan.

`future`/`stream` erase to their payload: the async wrapping is an
emission concern (WASI 0.3 future/stream at the boundary), not a Lean
type-level one. -/

/-- Open-world semantics for named type references: a function from
    schema type names to Lean types. Provided per schema; v1 universes
    are acyclic (self-reference needs depth fuel). -/
abbrev TySem : Type 1 := String → Type

/-- Reify a schema type as a Lean type. Unresolved references become
    whatever `sem` says (typically `Empty`) — and if `sem` is total over
    the universe, the wellFormed scan is SUPERSEDED by the kernel:
    unresolved refs are elaboration errors at the use site. -/
def Ty.toType : Ty → TySem → Type
  | .bool, _ => Bool
  | .u8, _ => UInt8
  | .u16, _ => UInt16
  | .u32, _ => UInt32
  | .u64, _ => UInt64
  | .i8, _ => Int8
  | .i16, _ => Int16
  | .i32, _ => Int32
  | .i64, _ => Int64
  | .f32, _ => Float32
  | .f64, _ => Float
  | .string, _ => String
  | .bytes, _ => List UInt8
  | .option a, sem => Option (a.toType sem)
  | .result ok err, sem => Sum (ok.toType sem) (err.toType sem)
  | .list a, sem => List (a.toType sem)
  | .future a, sem => a.toType sem
  | .stream a, sem => a.toType sem
  | .ty n, sem => sem n

end SchemaLang

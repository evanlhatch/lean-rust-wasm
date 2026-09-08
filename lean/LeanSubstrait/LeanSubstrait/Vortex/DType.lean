/-
# LeanSubstrait.Vortex.DType — the vortex logical dtype algebra, as data

A hand-curated, wire-faithful model of the fork's `vortex-array::dtype`
(`vortex` fork, branch `flatland-v0.83`). This is the same move as
`LeanSubstrait.Proto.Type`: vortex ships proto/flatbuffer wire
representations of DType (`vortex-proto`, `vortex-flatbuffers`), so a Lean
model has a stable wire target, and the model is the schema vocabulary that
flatlandc's spec tables type-check against and every emitter projects from.

**Deliberately omitted** (mechanism, not meaning — containment, lean-v3
Part 10): `FieldMask`/`Field` projections, the visitor/downcast traits,
sessions/plugins, `Arc`-sharing. The fork's `PartialEq` is structural
(ptr_eq is a shortcut, not a semantics), so the derived `BEq` here is
faithful — including `Extension`: `ExtDTypeRef`'s equality is id +
metadata-bytes + storage, exactly the erased triple modeled here.

**The drift tie** (oracle doctrine, SPEC-core §11.6): this model and the
Rust enum agree by the serde handshake — Lean → flatbuffer bytes → Rust
parse, and back — proved on the Lean side, differential-fuzzed across. That
codec lands with the wire work; the model stands alone until then.

Reference points in the fork (vortex-array/src/dtype/):
  - ptype.rs            — `pub enum PType { U8 = 0, …, F64 = 10 }`
  - nullability.rs      — `NonNullable` (default) | `Nullable`
  - decimal/types.rs    — i256: `MAX_PRECISION = 76`, `MAX_SCALE = 76`
  - mod.rs              — `pub enum DType` (12 variants)
  - extension/erased.rs — `ExtDTypeRef` equality: id + metadata + storage
-/

namespace LeanSubstrait.Vortex

/-- Fork `Nullability`: two values (unlike Substrait's three). NonNullable
    is the fork's `#[default]`. -/
inductive Nullability where
  | nonNullable
  | nullable
deriving Repr, BEq, DecidableEq, Inhabited

/-- Fork `PType` — the in-memory physical layout enum. The discriminants
    (`u8 = 0 … f64 = 10`) are wire-stable (proto/flatbuffer tags);
    `toDiscriminant` is the model's record of them. -/
inductive PType where
  | u8 | u16 | u32 | u64
  | i8 | i16 | i32 | i64
  | f16 | f32 | f64
deriving Repr, BEq, DecidableEq, Inhabited

/-- Wire discriminant, matching the fork's declared values. -/
def PType.toDiscriminant : PType → Nat
  | .u8 => 0 | .u16 => 1 | .u32 => 2 | .u64 => 3
  | .i8 => 4 | .i16 => 5 | .i32 => 6 | .i64 => 7
  | .f16 => 8 | .f32 => 9 | .f64 => 10

/-- The inverse reading: every discriminant ≤ 10 names a unique PType. -/
def PType.ofDiscriminant : Nat → Option PType
  | 0 => some .u8 | 1 => some .u16 | 2 => some .u32 | 3 => some .u64
  | 4 => some .i8 | 5 => some .i16 | 6 => some .i32 | 7 => some .i64
  | 8 => some .f16 | 9 => some .f32 | 10 => some .f64
  | _ => none

theorem PType.ofDiscriminant_toDiscriminant (p : PType) :
    ofDiscriminant p.toDiscriminant = some p := by
  cases p <;> rfl

/-- The ENGINE's type name (flatland-core's lowercase spelling — the
    `batch_expr` catalog's naming universe). SSOT: the Rust table is
    generated from this; the names never drift. -/
def PType.engineName : PType → String
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .f16 => "f16" | .f32 => "f32" | .f64 => "f64"

/-- The name map is injective and total over the 11 variants — the emitted
    match has no collisions or gaps. -/
theorem PType.engineName_inj : Function.Injective engineName := by
  intro a b h
  cases a <;> cases b <;> simp [engineName] at h ⊢ <;> exact h

/-- Byte width of the physical layout (f16 = 2). -/def PType.byteWidth : PType → Nat
  | .u8 | .i8 => 1
  | .u16 | .i16 | .f16 => 2
  | .u32 | .i32 | .f32 => 4
  | .u64 | .i64 | .f64 => 8

/-- The fork's `IntegerPType` trait surface: the eight integer kinds. -/
def PType.isInteger : PType → Bool
  | .f16 | .f32 | .f64 => false
  | _ => true

/-- The fork's `UnsignedPType` trait surface. -/
def PType.isUnsigned : PType → Bool
  | .u8 | .u16 | .u32 | .u64 => true
  | _ => false

/-- The fork's `OffsetBuilderPType` surface: u32, i32, u64, i64. -/
def PType.isOffsetBuilder : PType → Bool
  | .u32 | .i32 | .u64 | .i64 => true
  | _ => false

/-- Fork `DecimalDType`: precision and scale over the i256 storage. -/
structure DecimalDType where
  precision : Nat
  scale : Int
deriving Repr, BEq, DecidableEq, Inhabited

/-- The i256 bounds (fork: `MAX_PRECISION = MAX_SCALE = 76`). Scale may be
    negative in the fork's `i8`; validity is `1 ≤ precision ≤ 76` and
    `|scale| ≤ 76`. -/
def DecimalDType.isValid (d : DecimalDType) : Bool :=
  d.precision ≥ 1 && d.precision ≤ 76 && d.scale.natAbs ≤ 76

/-- A struct field name; the fork's `FieldName` newtype. -/
abbrev FieldName := String

/-- A unique extension-type identifier (fork: `ExtId` — e.g.
    `flatland.position`). -/
abbrev ExtId := String

/-- Fork `DType` — the logical types of elements in Vortex arrays.
    `extension` is the ERASED reading (`ExtDTypeRef`): id + serialized
    metadata bytes + storage dtype. Metadata is `List UInt8` (raw bytes —
    `ByteArray` carries no `Repr` in core, and lists are the proof-friendly
    shape anyway). The typed reading is the registry's job: Codegen's
    `ExtDTypeItem` decodes `metadata` by its declared shape. -/
inductive DType where
  | null
  | bool (n : Nullability)
  | primitive (p : PType) (n : Nullability)
  | decimal (d : DecimalDType) (n : Nullability)
  | utf8 (n : Nullability)
  | binary (n : Nullability)
  | list (elem : DType) (n : Nullability)
  | fixedSizeList (elem : DType) (size : Nat) (n : Nullability)
  | struct (fields : List (FieldName × DType)) (n : Nullability)
  | union (variants : List (FieldName × DType)) (n : Nullability)
  | variant (n : Nullability)
  | extension (id : ExtId) (metadata : List UInt8) (storage : DType)
deriving Repr, BEq, Inhabited

/-- Ordered struct fields — the fork's `StructFields`. -/
abbrev StructFields := List (FieldName × DType)

/-- Union variants — the fork's `UnionVariants`. -/
abbrev UnionVariants := List (FieldName × DType)

/-- Nullability accessor. `null` reads nullable (its only value is null);
    `extension` reports its storage's, matching how the fork treats an
    extension array as storage + wrapper. -/
def DType.nullability : DType → Nullability
  | .null => .nullable
  | .bool n => n
  | .primitive _ n => n
  | .decimal _ n => n
  | .utf8 n => n
  | .binary n => n
  | .list _ n => n
  | .fixedSizeList _ _ n => n
  | .struct _ n => n
  | .union _ n => n
  | .variant n => n
  | .extension _ _ s => s.nullability

mutual
/-- Well-formedness: the checks the fork enforces at construction that are
    expressible without the registry (decimal bounds). Empty structs/unions
    are legal in the fork; FSL size is unconstrained at the dtype level.
    Extension metadata validity is NOT checkable here — that's the registry
    item's validity predicate (the whole point of raising it). -/
def DType.wellFormed : DType → Bool
  | .decimal d _ => d.isValid
  | .list e _ => e.wellFormed
  | .fixedSizeList e _ _ => e.wellFormed
  | .struct fs _ => fieldsWellFormed fs
  | .union vs _ => fieldsWellFormed vs
  | .extension _ _ s => s.wellFormed
  | _ => true

def DType.fieldsWellFormed : List (FieldName × DType) → Bool
  | [] => true
  | (_, t) :: rest => t.wellFormed && fieldsWellFormed rest
end

end LeanSubstrait.Vortex

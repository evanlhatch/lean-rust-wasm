/-
# SchemaLang.Vortex.Emit — the Vortex target

Fold `Item`s to `src/vortex_generated.rs`: one DType constant and one
`IntoVortex` impl per record. Discipline per codegen-core: names arrive
pre-mangled (`Emit.pascal`/`snake`/`rustIdent` — the one mangling
module), the item shape is the `CodegenCore.Emit.Rust.Item` AST, and
the ONLY string interpolation is inside leaf payloads (dtype
expressions, impl bodies — the audited leaves).

Lowering (target-neutral universe → Vortex, via `Vortex.Lower`):
- records → `DType::Struct(StructFields::new(vec![...]))` at top level,
  NonNullable (the schema universe is nullability-free; `.option t`
  flips the lowered nullability to Nullable per `Ty.lower`)
- variants → `DType::Union(UnionVariants::new(vec![...]))`; payload-free
  cases lower to `DType::Null` (v1: the union carries a slot per case)
- named refs (`.ty n`) resolve through a fuel-based semantics over the
  universe — acyclic v1 (self-reference needs depth fuel, the Row lesson)
- `future`/`stream` in field position fail the lowering; the record is
  skipped (the emitter may assume `wellFormed`-checked input — the
  flatland audit doctrine — so this is a defensive skip, not a path)

DType constants are `LazyLock` (Vortex DTypes are not const-constructible);
each record also gets `impl IntoVortex for <Struct>`, building the
struct array column-wise via `IntoArray`.
-/

import CodegenCore
import SchemaLang.Item
import SchemaLang.Vortex.DType
import SchemaLang.Vortex.Lower

namespace SchemaLang.Vortex.Emit

open CodegenCore.Emit (pascal rustIdent snake)

/-! ## DType → Rust expression -/

/-- `PType` as a Rust path (`PType::U64`). -/
def ptyRust : PType → String
  | .u8 => "PType::U8" | .u16 => "PType::U16"
  | .u32 => "PType::U32" | .u64 => "PType::U64"
  | .i8 => "PType::I8" | .i16 => "PType::I16"
  | .i32 => "PType::I32" | .i64 => "PType::I64"
  | .f16 => "PType::F16" | .f32 => "PType::F32" | .f64 => "PType::F64"

/-- `Nullability` as a Rust path. -/
def nullabilityRust : Nullability → String
  | .nonNullable => "Nullability::NonNullable"
  | .nullable => "Nullability::Nullable"

/-- Metadata bytes as a `vec![...]` literal. -/
private def bytesVecRust : List UInt8 → String
  | [] => "vec![]"
  | bs => "vec![" ++ String.intercalate ", " (bs.map fun b => s!"{b}u8") ++ "]"

mutual
/-- A comma-joined `("name".into(), dtype-expr)` item list for struct
    fields / union variants (brackets come from the caller's `vec![...]`).
    Names are the WIRE names (registry order — the dtype is
    wire-faithful; only `self.` accessors are mangled). -/
private def fieldsItemsRust : List (FieldName × DType) → String
  | [] => ""
  | (n, dt) :: rest =>
      let item := s!"(\"{n}\".into(), {dtypeRust dt})"
      match rest with
      | [] => item
      | _ => item ++ ", " ++ fieldsItemsRust rest

/-- Lower the DType model to a Rust expression constructing
    `vortex::dtype::DType`. Names are the short paths — the module
    header `use`s `vortex::dtype::{...}` (see `useItems`). -/
def dtypeRust : DType → String
  | .null => "DType::Null"
  | .bool n => s!"DType::Bool({nullabilityRust n})"
  | .primitive p n => s!"DType::Primitive({ptyRust p}, {nullabilityRust n})"
  | .decimal d n =>
      s!"DType::Decimal(DecimalDType::new({d.precision}, {d.scale}), {nullabilityRust n})"
  | .utf8 n => s!"DType::Utf8({nullabilityRust n})"
  | .binary n => s!"DType::Binary({nullabilityRust n})"
  | .list e n =>
      s!"DType::List(std::sync::Arc::new({dtypeRust e}), {nullabilityRust n})"
  | .fixedSizeList e size n =>
      s!"DType::FixedSizeList(std::sync::Arc::new({dtypeRust e}), {size}, {nullabilityRust n})"
  | .struct fs n =>
      s!"DType::Struct(StructFields::new(vec!["
        ++ fieldsItemsRust fs ++ s!"]), {nullabilityRust n})"
  | .union vs n =>
      s!"DType::Union(UnionVariants::new(vec!["
        ++ fieldsItemsRust vs ++ s!"]), {nullabilityRust n})"
  | .variant n => s!"DType::Variant({nullabilityRust n})"
  | .extension id metadata storage =>
      s!"DType::Extension(ExtDTypeRef::new(\"{id}\", {bytesVecRust metadata}, "
        ++ s!"std::sync::Arc::new({dtypeRust storage})))"
end

/-! ## IntoVortex impls -/

/-- One record → `impl IntoVortex for <Struct>`: build the Vortex
    struct array column-wise. Body is a `Body` leaf (the boring-template
    concession — audited, counted by the AST discipline). -/
def intoVortexImpl (structName : String) (fields : List (String × DType)) :
    CodegenCore.Emit.Rust.Item :=
  let pairs := fields.map fun (n, _) =>
    s!"(\"{n}\".into(), self.{rustIdent n}.into_array())"
  let body := "vortex::StructArray::from_fields(vec!["
    ++ String.intercalate ", " pairs
    ++ "]).expect(\"valid struct array\").into_array()"
  .implTrait "IntoVortex" (pascal structName) []
    [("into_vortex(&self) -> vortex::ArrayRef", body)]

/-! ## The universe semantics (named refs, fuel-bounded) -/

/-- Variant cases → union variants: payload cases lower their type;
    payload-free cases lower to `DType::Null` (v1: every case gets a
    slot in the union). -/
private def lowerVariantCases (sem : VortexSem) (cases : List SchemaLang.VariantCase) :
    List (FieldName × DType) :=
  cases.filterMap fun (c, payload) =>
    match payload with
    | some t => (fun dt => (c, dt)) <$> Ty.lower sem .nonNullable t
    | none => some (c, DType.null)

/-- Named-type semantics over a universe: a record resolves to its
    struct dtype, a variant to its union dtype. Fuel bounds the named
    reference depth (acyclic v1); exhausted fuel = unresolvable =
    `none`. -/
def refSem (items : List SchemaLang.Item) : Nat → VortexSem
  | 0 => fun _ => none
  | fuel + 1 =>
    let inner := refSem items fuel
    fun n =>
      (items.filterMap fun it =>
        match it with
        | .record m fields =>
            if m == n then
              (lowerFields inner .nonNullable (fields.map fun f => (f.name, f.ty)))
                |>.map fun fs => DType.struct fs .nonNullable
            else none
        | .variant m cases =>
            if m == n then
              some (DType.union (lowerVariantCases inner cases) .nonNullable)
            else none
        | _ => none) |>.head?

/-- Every record of the universe, lowered: (registry name, struct
    fields). Registration order; records whose lowering fails (an
    unresolved ref) are skipped. -/
def recordDTypes (items : List SchemaLang.Item) (fuel : Nat := 8) :
    List (String × StructFields) :=
  let sem := refSem items fuel
  items.filterMap fun it =>
    match it with
    | .record n fields =>
        (lowerFields sem .nonNullable (fields.map fun f => (f.name, f.ty)))
          |>.map fun fs => (n, fs)
    | _ => none

/-! ## The module -/

/-- Module header: the short paths `dtypeRust` emits rely on. -/
def useItems : List CodegenCore.Emit.Rust.Item :=
  [ .use_ "vortex::dtype::{DType, DecimalDType, ExtDTypeRef, Nullability, PType, StructFields, UnionVariants}"
  , .use_ "vortex::IntoArray"
  , .use_ "vortex::IntoVortex" ]

/-- One record → comment + DType constant + IntoVortex impl. -/
def recordItems (rec : String × StructFields) : List CodegenCore.Emit.Rust.Item :=
  let (n, fs) := rec
  let dtype : DType := DType.struct fs .nonNullable
  [ .comment s!"record: {n}"
  , .const ((snake n).toUpper ++ "_DTYPE")
      "std::sync::LazyLock<vortex::dtype::DType>"
      s!"std::sync::LazyLock::new(|| {dtypeRust dtype})"
  , intoVortexImpl n fs ]

/-- The Vortex emitter plugin: dtype constants + IntoVortex impls. -/
def vortexEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "vortex"
  style := .doubleSlash
  specSource := "SchemaLang/Spec/Demo.lean"
  outputs := ["../../src/vortex_generated.rs"]
  run items :=
    [ { path := "../../src/vortex_generated.rs"
        contents :=
          CodegenCore.Emit.Rust.renderModule
            (useItems ++ (recordDTypes items).flatMap recordItems) }
    ]

end SchemaLang.Vortex.Emit

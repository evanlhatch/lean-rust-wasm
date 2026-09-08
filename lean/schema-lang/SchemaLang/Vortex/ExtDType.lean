/-
# SchemaLang.Vortex.ExtDType — the ExtVTable emitter

Extension dtypes don't come from the schema universe — they are a
REGISTRY (flatland's `Codegen.Registry` / `Spec.extDTypes` pattern):
spec-as-data, each entry an `ExtDTypeItem` describing one Rust
`ExtVTable` impl. The emitter ignores the schema-item input entirely
(the zero-input plugin in the buf model) and folds the constant
`extDTypes` list instead.

Each non-external item emits:
- (u8Enum metadata only) a `Metadata` newtype + `impl Display`
- a unit struct for the vtable type
- the 11-member `impl ExtVTable for <rustName>` (2 assoc types +
  9 methods), bodies dispatched on `MetadataShape` /
  `StorageConstraint`

`external := true` marks fork-owned extension types (e.g. GeoArrow):
they are REGISTERED (so the lookup/`Ty.lower` story knows they exist)
but NOT emitted — the fork provides their impls.
-/

import CodegenCore
import SchemaLang.Item
import SchemaLang.Vortex.DType
import SchemaLang.Vortex.Lower
import SchemaLang.Vortex.Emit

namespace SchemaLang.Vortex

/-! ## The closed metadata-shape grammar -/

/-- The closed metadata-shape grammar: exactly the metadata shapes the
    registry admits. Adding a shape = adding a variant = the compiler
    forces the emitter dispatch to grow with it (no `Raw` escape). -/
inductive MetadataShape where
  | unit                                           -- EmptyMetadata
  | u8Enum (allowed : List UInt8) (displaySuffix : String)
  | utf8NonEmpty (displayPrefix : String)
  | fixedShapeTensor                               -- proto-serialized shape/names/permutation
  | geoArrow                                       -- fork's GeoMetadata (external)

/-- Storage-dtype constraint for `validate_dtype`. -/
inductive StorageConstraint where
  | fixed (p : PType)
  | free
  | fixedSizeListOfFloat

/-- An extension dtype item. -/
structure ExtDTypeItem where
  rustName : String          -- the Rust vtable struct, e.g. "PositionExt"
  id : String                -- "flatland.position" (the ExtId)
  metadata : MetadataShape
  storage : StorageConstraint
  external : Bool            -- fork-owned (skip emission) vs ours

/-- Well-formedness: a u8Enum over a FIXED storage must admit at least
    one value (the enum is useless otherwise). Everything else is
    structurally fine. -/
def ExtDTypeItem.wellFormed (it : ExtDTypeItem) : Bool :=
  match it.metadata, it.storage with
  | .u8Enum allowed _, .fixed _ => allowed.length > 0
  | _, _ => true

end SchemaLang.Vortex

namespace SchemaLang.Vortex.Emit

open CodegenCore.Emit (pascal)

/-! ## MetadataShape → Rust type expression -/

/-- The Rust `Metadata` type expression for a shape. The u8Enum case
    names the GENERATED newtype (derived from the display suffix —
    `position` → `PositionMetadata`); the others are vortex paths. -/
def metadataRust : MetadataShape → String
  | .unit => "vortex::EmptyMetadata"
  | .u8Enum _ suffix => pascal suffix ++ "Metadata"
  | .utf8NonEmpty _ => "NonEmptyUtf8Metadata"
  | .fixedShapeTensor => "vortex_tensor::FixedShapeTensorMetadata"
  | .geoArrow => "GeoMetadata"

/-! ## Body dispatch (the audited leaves) -/

/-- `fn serialize_metadata` body per shape. -/
private def serializeBody : MetadataShape → String
  | .unit => "vec![]"
  | .u8Enum _ _ => "vec![self.0]"
  | .utf8NonEmpty _ => "self.0.clone().into_bytes()"
  | .fixedShapeTensor => "self.encode_proto()"
  | .geoArrow => "self.to_json().into_bytes()"

/-- `fn deserialize_metadata` body per shape. Literal Rust braces come
    from plain-string segments (s! treats `{{` as `{...}` notation). -/
private def deserializeBody : MetadataShape → String
  | .unit => "if bytes.is_empty() { Some(vortex::EmptyMetadata) } else { None }"
  | .u8Enum allowed _ =>
      let allowedStr := String.intercalate ", " (allowed.map fun b => s!"{b}u8")
      let tyName := metadataRust (.u8Enum allowed "position")
      "if bytes.len() == 1 && [" ++ allowedStr
        ++ "].contains(&bytes[0]) { Some(" ++ tyName ++ "(bytes[0])) } else { None }"
  | .utf8NonEmpty _ =>
      "std::str::from_utf8(bytes).ok().filter(|s| !s.is_empty()).map(|s| s.to_string())"
  | .fixedShapeTensor => "vortex_tensor::FixedShapeTensorMetadata::decode_proto(bytes).ok()"
  | .geoArrow => "GeoMetadata::deserialize(bytes).ok()"

/-- `fn validate_dtype` body per storage constraint. -/
private def validateDTypeBody : StorageConstraint → String
  | .fixed p =>
      "match storage { vortex::dtype::DType::Primitive(" ++ ptyRust p
        ++ ", _) => Ok(()), other => Err(vortex::error::VortexError::InvalidDType(other.clone())) }"
  | .free => "Ok(())"
  | .fixedSizeListOfFloat =>
      "match storage { vortex::dtype::DType::FixedSizeList(elem, _, _) if matches!(&*elem, vortex::dtype::DType::Primitive(PType::F32 | PType::F64, _)) => Ok(()), other => Err(vortex::error::VortexError::InvalidDType(other.clone())) }"

/-! ## The ExtVTable impl -/

/-- One item → the full 11-member `impl ExtVTable for {rustName}`:
    2 associated types + 9 methods, per the fork's `ExtVTable` trait. -/
def extVTableImpl (item : ExtDTypeItem) : CodegenCore.Emit.Rust.Item :=
  let shape := item.metadata
  .implTrait "ExtVTable" item.rustName
    [ ("Metadata", metadataRust shape)
    , ("NativeValue<'a>", "&'a ScalarValue") ]
    [ ("id(&self) -> ExtId", s!"ExtId::new(\"{item.id}\")")
    , ("serialize_metadata(&self) -> Vec<u8>", serializeBody shape)
    , ("deserialize_metadata(bytes: &[u8]) -> Option<Self::Metadata>",
        deserializeBody shape)
    , ("validate_dtype(&self, storage: &DType) -> VortexResult<()>",
        validateDTypeBody item.storage)
    , ("least_supertype(&self, a: &DType, b: &DType) -> VortexResult<DType>",
        "if a == b { Ok(a.clone()) } else { Err(vortex::error::VortexError::MismatchedTypes(a.to_string(), b.to_string())) }")
    , ("unpack_native<'a>(&self, value: &'a ScalarValue) -> VortexResult<Self::NativeValue<'a>>",
        "Ok(value)")
    , ("can_coerce_from(&self, _input: &DType) -> bool", "true")
    , ("can_coerce_to(&self, _target: &DType) -> bool", "true")
    , ("validate_scalar_value(&self, _value: &ScalarValue) -> VortexResult<()>",
        "Ok(())")
    ]

/-! ## Per-item module items -/

/-- One non-external item → comment + (u8Enum: newtype + Display) +
    vtable unit struct + the ExtVTable impl. -/
private def itemItems (it : ExtDTypeItem) : List CodegenCore.Emit.Rust.Item :=
  let mty := it.metadata
  let metaItems : List CodegenCore.Emit.Rust.Item :=
    match mty with
    | .u8Enum _ suffix =>
        let name := metadataRust mty
        [ .newtype name "u8" ["Clone", "Debug", "PartialEq", "Eq"]
        , .implDisplay name ("write!(f, \"" ++ suffix ++ "{0}\", self.0)") ]
    | _ => []
  metaItems
    ++ [ .comment s!"ext dtype: {it.id}"
       , .unitStruct it.rustName ["Clone", "Copy", "Debug"]
       , extVTableImpl it ]

/-- The ext-dtype module: use-decls + per-item items for OUR entries
    (`external := true` is fork-owned — registered, not emitted). -/
def extDTypeModule (items : List ExtDTypeItem) : List CodegenCore.Emit.Rust.Item :=
  let header : List CodegenCore.Emit.Rust.Item :=
    [ .use_ "vortex::dtype::{DType, ExtDTypeRef, PType}"
    , .use_ "vortex::ext::{ExtId, ExtVTable, ScalarValue}"
    , .use_ "vortex::error::VortexResult" ]
  let ours := items.filter (fun (it : ExtDTypeItem) => !it.external)
  header ++ (ours.flatMap itemItems)

/-! ## The registry (spec-as-data) -/

/-- The extension-dtype registry. Spec-as-data (flatland's
    `Spec.extDTypes`): ext dtypes don't derive from schema items, they
    ARE the spec. `external := true` entries are fork-owned. -/
def extDTypes : List ExtDTypeItem :=
  [ { rustName := "PositionExt"
    , id := "flatland.position"
    , metadata := .u8Enum [0, 1, 2, 3] "position"
    , storage := .fixed .u8
    , external := false }
  , { rustName := "TensorExt"
    , id := "vortex.fixedshape.tensor"
    , metadata := .fixedShapeTensor
    , storage := .fixedSizeListOfFloat
    , external := false }
  , { rustName := "GeoExt"
    , id := "fork.geo"
    , metadata := .geoArrow
    , storage := .free
    , external := true }
  ]

/-! ## The emitter plugin (zero-input in the schema universe) -/

/-- The ext-dtype emitter: does NOT consume schema items (ext dtypes
    are registered separately, as the `extDTypes` constant above); the
    `List SchemaLang.Item` parameter is ignored. -/
def extVortexEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "ext-vortex"
  style := .doubleSlash
  specSource := "SchemaLang/Vortex/ExtDType.lean (extDTypes)"
  outputs := ["../../src/ext_dtypes_generated.rs"]
  run _ :=
    [ { path := "../../src/ext_dtypes_generated.rs"
        contents :=
          CodegenCore.Emit.Rust.renderModule (extDTypeModule extDTypes) }
    ]

end SchemaLang.Vortex.Emit

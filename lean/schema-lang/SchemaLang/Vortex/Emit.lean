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
import SchemaLang.Wf
import SchemaLang.Emit.GenCtx
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
    wire-faithful; only `self.` accessors are mangled). INSIDE the
    `mutual` block by necessity: `dtypeRust`'s termination is proven
    THROUGH this member's structural recursion over the field list, so
    the fold must stay a list-recursion (a `map`+`intercalate` one-liner
    would rob the block's termination witness). -/
private def fieldsItemsRust : List (FieldName × DType) → String
  | [] => ""
  | (n, dt) :: rest =>
      s!"(\"{n}\".into(), {dtypeRust dt})"
        ++ (match rest with | [] => "" | _ => ", " ++ fieldsItemsRust rest)

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

/-- The sem-parameterized record-table spine — the checked and
    unchecked views share it (`recordDTypes` instantiates `sem` with
    the fuel-bounded self-semantics). -/
private def recordDTypesWith (sem : VortexSem) (items : List SchemaLang.Item) :
    List (String × StructFields) :=
  items.filterMap fun it =>
    match it with
    | .record n fields =>
        (lowerFields sem .nonNullable (fields.map fun f => (f.name, f.ty)))
          |>.map fun fs => (n, fs)
    | _ => none

/-- Every record of the universe, lowered: (registry name, struct
    fields). Registration order; records whose lowering fails (an
    unresolved ref) are skipped. -/
def recordDTypes (items : List SchemaLang.Item) (fuel : Nat := 8) :
    List (String × StructFields) :=
  recordDTypesWith (refSem items fuel) items

/-! ## W7.9 phase 2 — the checked universe view

The emitter consumes a `CheckedUniverse` (`{ items // WellFormed items
}` — the well-formedness evidence riding the type, discharged once by
`GenCtx.checkedItems?` through `universeCheck_sound`). On the checked
path the fold's per-field `banAsync` evidence comes from the evidence
bundle, so `Ty.lowerChecked`'s async arms — the header's "defensive
skip" — are unrepresentable (`Bool.noConfusion`, not a fallback
`none`). `recordDTypesChecked_eq` certifies the bytes are the
unchecked path's own; `checked_field_ne_future`/`_ne_stream` are the
impossibility stated against the emitter's input. -/

/-- The checked record-table worker: the evidence is the per-record
    field banAsync lookup, projected ONCE from the `WellFormed` bundle
    at `recordDTypesChecked` and threaded through the recursion (the
    membership wall: a `filterMap` lambda carries no membership proof,
    so the fold is structural here). -/
private def recordDTypesCheckedGo (sem : VortexSem) :
    (items : List SchemaLang.Item) →
    (∀ n fields, SchemaLang.Item.record n fields ∈ items →
      ∀ f, f ∈ fields → f.ty.banAsync = true) →
    List (String × StructFields)
  | [], _ => []
  | it :: rest, hev =>
      match
        (match it with
        | .record n fields =>
            (lowerFieldsChecked sem .nonNullable
              (fields.map fun f => (f.name, f.ty))
              (fun p hp => by
                rcases List.mem_map.mp hp with ⟨f, hf, rfl⟩
                exact hev n fields List.mem_cons_self f hf))
              |>.map fun fs => (n, fs)
        | _ => none)
        with
      | none =>
          recordDTypesCheckedGo sem rest
            (fun n fields hit => hev n fields (List.mem_cons_of_mem _ hit))
      | some x =>
          x :: recordDTypesCheckedGo sem rest
            (fun n fields hit => hev n fields (List.mem_cons_of_mem _ hit))

/-- Every record of a CHECKED universe, lowered — the emitter's input.
    The per-field banAsync evidence is the `WellFormed` bundle's
    record-field arm (`WellFormed.noAsync_of_record_field`) read
    through the checker bridge (`banAsync_iff_noAsyncTy`). -/
def recordDTypesChecked (cu : SchemaLang.CheckedUniverse) (fuel : Nat := 8) :
    List (String × StructFields) :=
  recordDTypesCheckedGo (refSem cu.val fuel) cu.val
    (fun _n _fields hit _f hf =>
      SchemaLang.banAsync_iff_noAsyncTy.mpr
        (cu.property.noAsync_of_record_field hit hf))

/-- The worker agrees with the shared spine, item list by item list. -/
theorem recordDTypesCheckedGo_eq (sem : VortexSem) :
    (items : List SchemaLang.Item) →
    (hev : ∀ n fields, SchemaLang.Item.record n fields ∈ items →
      ∀ f, f ∈ fields → f.ty.banAsync = true) →
    recordDTypesCheckedGo sem items hev =
    items.filterMap fun it =>
      match it with
      | .record n fields =>
          (lowerFields sem .nonNullable (fields.map fun f => (f.name, f.ty)))
            |>.map fun fs => (n, fs)
      | _ => none
  | [], _ => rfl
  | it :: rest, hev => by
      have ih := recordDTypesCheckedGo_eq sem rest
        (fun n fields hit => hev n fields (List.mem_cons_of_mem _ hit))
      cases it with
      | record n fields =>
          -- case-split the lowering scrutinee FIRST: both sides'
          -- compiler-generated matchers (`recordDTypesCheckedGo.match_3`
          -- vs `List.filterMap.match_1`) iota-reduce on a concrete
          -- ctor; with a stuck scrutinee the two private splitters
          -- are syntactically distinct and no rfl/simp bridge exists.
          cases hL : lowerFields sem .nonNullable
              (fields.map fun f => (f.name, f.ty)) with
          | none =>
              simp only [recordDTypesCheckedGo, List.filterMap_cons,
                lowerFieldsChecked_eq_lowerFields, hL, Option.map, ih]
          | some fs =>
              simp only [recordDTypesCheckedGo, List.filterMap_cons,
                lowerFieldsChecked_eq_lowerFields, hL, Option.map, ih]
      | variant n cases =>
          simp only [recordDTypesCheckedGo, List.filterMap_cons, ih]
      | func s =>
          simp only [recordDTypesCheckedGo, List.filterMap_cons, ih]
      | resource n =>
          simp only [recordDTypesCheckedGo, List.filterMap_cons, ih]

/-- BYTES PRESERVED (the theorem half of the byte-tie): the checked
    record table IS the unchecked one — the evidence changes nothing
    computational. -/
theorem recordDTypesChecked_eq (cu : SchemaLang.CheckedUniverse) (fuel : Nat := 8) :
    recordDTypesChecked cu fuel = recordDTypes cu.val fuel :=
  recordDTypesCheckedGo_eq _ _ _

/-- The deep form: every field type of a checked record is async-free
    at EVERY depth (`Ty.banAsync` — the checker vocabulary the
    lowering consumes). -/
theorem checked_field_banAsync (cu : SchemaLang.CheckedUniverse)
    {n : String} {fields : List SchemaLang.Field}
    (hit : SchemaLang.Item.record n fields ∈ cu.val)
    {f : SchemaLang.Field} (hf : f ∈ fields) : f.ty.banAsync = true :=
  SchemaLang.banAsync_iff_noAsyncTy.mpr (cu.property.noAsync_of_record_field hit hf)

/-- THE IMPOSSIBILITY THEOREM: on a checked universe the emitter's
    "defensive skip" (the header's `future`/`stream` → `none` arms)
    cannot fire from the record table — a field type of a checked
    record is never `future`. The case is discharged BY the
    `WellFormed` evidence: `NoAsyncTy (.future a)` is an empty family
    (`nomatch` on the projected evidence). -/
theorem checked_field_ne_future (cu : SchemaLang.CheckedUniverse)
    {n : String} {fields : List SchemaLang.Field}
    (hit : SchemaLang.Item.record n fields ∈ cu.val)
    {f : SchemaLang.Field} (hf : f ∈ fields) {a : SchemaLang.Ty} :
    f.ty ≠ SchemaLang.Ty.future a := by
  intro heq
  have hna := cu.property.noAsync_of_record_field hit hf
  rw [heq] at hna
  nomatch hna

/-- The `stream` twin. -/
theorem checked_field_ne_stream (cu : SchemaLang.CheckedUniverse)
    {n : String} {fields : List SchemaLang.Field}
    (hit : SchemaLang.Item.record n fields ∈ cu.val)
    {f : SchemaLang.Field} (hf : f ∈ fields) {a : SchemaLang.Ty} :
    f.ty ≠ SchemaLang.Ty.stream a := by
  intro heq
  have hna := cu.property.noAsync_of_record_field hit hf
  rw [heq] at hna
  nomatch hna

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

/-- The Vortex emitter plugin: dtype constants + IntoVortex impls.

    W7.9 phase 2: the item universe is consumed through the CHECKED
    view (`GenCtx.checkedItems?` — the executable check discharged
    once into `WellFormed`, the evidence riding the type). The checked
    fold's async arms are unrepresentable
    (`checked_field_ne_future`/`_ne_stream`); the bytes are the
    unchecked path's own (`recordDTypesChecked_eq` + the byte-tie
    gate). The `none` arm is the pre-evidence fallback for callers
    that never ran the check (test fixtures) — the paths agree, so
    either way the output is identical.

    FOLLOW-UP (W7.9 phase 3): migrate the remaining `Emitter GenCtx`
    consumers — Emit/Wit.lean, Emit/Rust.lean, Emit/Invariant.lean,
    Emit/Update.lean, Emit/Machine.lean, Emit/Typestate.lean,
    Emit/Circuit.lean, Docs — onto `ctx.checkedItems?`; each defensive
    partiality (unresolved-ref skips, `filterMap` drops) gets the same
    treatment: the impossibility as a theorem, the bytes pinned by an
    `_eq` agreement theorem. ONE pattern proven here, not a sweep. -/
def vortexEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "vortex"
  style := .doubleSlash
  specSource := "Demo.lean"
  outputs := ["../../src/vortex_generated.rs"]
  run ctx :=
    let table := match ctx.checkedItems? with
      | some cu => recordDTypesChecked cu
      | none => recordDTypes ctx.items
    [ { path := "../../src/vortex_generated.rs"
        contents :=
          CodegenCore.Emit.Rust.renderModule
            (useItems ++ table.flatMap recordItems) }
    ]

end SchemaLang.Vortex.Emit

/-
# SchemaLang.Bridge — Ty → Substrait SType lowering

The bridge from the schema-lang component-boundary universe to the
Substrait typed query universe. This is where the "what maps to a
queryable column" decision lives — the query-side sibling of
`Vortex.Lower`.

Lowering decisions (target-neutral → Substrait):
- `.u8`..`.u64` → `.i8`..`.i64` — NARROWING: Substrait's core type
  catalogue has no unsigned ints, so unsigned schema types lose their
  unsignedness (and u64 values above i64.MAX are unrepresentable in a
  query plan; component-boundary code keeps the unsigned type).
- `.f32` → `.fp32`, `.f64` → `.fp64` (naming only)
- `.list a` → `.list` of the lowered element
- `.ty n` → `.userDefined "" n []` — schema-lang v1 has no URN, so the
  urn is empty and there are no parameters
- `.option` is NOT a value here: schema-lang `option` is a type
  CONSTRUCTOR (WIT-style) while Substrait carries nullability as a
  separate Bool — `SchemaCol.ofField` unwraps options into the nullable
  flag, and `toSType?` itself has no column context, so `.option`
  does not lower
- `.result`, `.future`, `.stream`, `.bytes` → `none` (not queryable:
  async/error channels live in function signatures, not column types)

Nullability composition rule (flatland `Substrait.Typed.Schema`
convention): both universes are nullability-FREE — schema-lang nests
nullability as `option<T>` constructors, Substrait carries it as
the third component of a `SchemaCol`. `ofField` is the junction: it
peels option constructors and emits the nullable flag.
-/

import SchemaLang.Item
import Substrait.Typed.Expr

namespace SchemaLang

open Substrait.Typed (SType SchemaCol Schema)

/-! ## Type lowering -/

/-- Partial lowering of the schema-lang universe to the Substrait query
    universe. `none` = not queryable (option/result/future/stream/bytes). -/
def Ty.toSType? : Ty → Option SType
  | .bool => some .bool
  -- unsigned narrowing: Substrait core types are signed only
  | .u8 => some .i8
  | .u16 => some .i16
  | .u32 => some .i32
  | .u64 => some .i64
  | .i8 => some .i8
  | .i16 => some .i16
  | .i32 => some .i32
  | .i64 => some .i64
  | .f32 => some .fp32
  | .f64 => some .fp64
  | .string => some .string
  | .list a => a.toSType?.map SType.list
  | .ty n => some (.userDefined "" n [])
  -- not queryable (option is unwrapped into the nullable flag by
  -- `SchemaCol.ofField`, which owns the column context)
  | .option _ => none
  | .result _ _ => none
  | .future _ => none
  | .stream _ => none
  | .bytes => none

/-- The lowering is a function of the type alone: equal types lower
    equally (used downstream to lift compat evidence through the
    bridge). Trivially `congrArg` — stated as its own lemma so callers
    don't reprove it. -/
theorem Ty.toSType?_congr {a b : Ty} (h : a = b) :
    a.toSType? = b.toSType? :=
  congrArg Ty.toSType? h

/-! ## Fields and schemas -/

/-- Peel option constructors off a field type, reporting whether any
    were peeled. Nested options (`option<option<T>>`) stay nullable —
    Substrait has no nullability to nest. -/
def Ty.peelOptions : Ty → Ty × Bool
  | .option a => let (t, _) := a.peelOptions; (t, true)
  | t => (t, false)

/-- Convert a schema-lang field to a Substrait schema column
    `(name, SType, nullable)`: the option constructor IS the
    nullability, so it is unwrapped into the flag; the inner type is
    lowered with `Ty.toSType?`. `none` when the field type is not
    queryable (result/future/stream/bytes — and nested options inside
    those). -/
def SchemaCol.ofField (f : Field) : Option SchemaCol :=
  let (t, nullable) := f.ty.peelOptions
  t.toSType?.map fun s => (f.name, s, nullable)

/-- Lower an item universe to Substrait schemas: one `(tableName,
    Schema)` pair per record item (non-records are skipped). Fields
    whose type does not lower are dropped from the schema (v1: the
    queryable projection of the record). -/
def Schema.ofItems : List Item → List (String × Schema) :=
  fun items =>
    items.filterMap fun it =>
      match it with
      | .record name fields =>
          some (name, fields.filterMap SchemaCol.ofField)
      | _ => none

end SchemaLang

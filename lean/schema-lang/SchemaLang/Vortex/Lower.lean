/-
# SchemaLang.Vortex.Lower — Ty → Vortex DType lowering

The target-specific lowering from the schema-lang universe to the
Vortex wire-faithful model. This is where nullability composition,
extension-dtype lookup, and the "what doesn't map" decisions live.

Lowering decisions (target-neutral → Vortex):
- `.option t` → lower `t` with the TOP-LEVEL nullability flipped to
  `.nullable` (Vortex nullability is per-dtype, not a wrapper — unlike
  WIT's `option<T>` which is a constructor). The flip lands on `t`'s
  outer dtype ONLY: everything inside keeps its own non-nullable flag
  (`option<list<u8>>` → a nullable list of NON-nullable u8).
- `.result ok err` → `none`: the tag+payload union this lowering
  promises has not landed — a refusal beats a wrong artifact that
  SUCCEEDS (callers handle `none` already: the return is `Option`).
- `.future t` / `.stream t` → banned in field position (banAsync);
  in func signatures they map to WASI 0.3 future/stream, not Vortex
- `.ty n` → registry lookup (`sem`), with the REQUESTED nullability
  stamped on the resolved dtype (`withNullability`) — a nullable ref
  emits a nullable dtype. `.ext n` → extension dtype lookup.

Nullability composition rule (flatland `Substrait.Typed.Schema`
convention): the schema universe is nullability-FREE (option handles
it); the lowering ADDS nullability based on context. A top-level
`.option t` becomes nullable; everything inside it stays as lowered.
-/

import SchemaLang.Ty
import SchemaLang.Vortex.DType

namespace SchemaLang.Vortex

open SchemaLang

/-- The named-type semantics for Vortex: resolves schema type names to
    their lowered Vortex dtypes. Provided by the caller (the driver). -/
abbrev VortexSem : Type := String → Option DType

/-- Lower a target-neutral `Ty` to a Vortex `DType`, given a semantics
    for named references. Returns `none` for unresolvable refs or
    non-tabular types (future/stream in field position). -/
def Ty.lower (sem : VortexSem) (null : Nullability) : Ty → Option DType
  | .bool => some (.bool null)
  | .u8 => some (.primitive .u8 null)
  | .u16 => some (.primitive .u16 null)
  | .u32 => some (.primitive .u32 null)
  | .u64 => some (.primitive .u64 null)
  | .i8 => some (.primitive .i8 null)
  | .i16 => some (.primitive .i16 null)
  | .i32 => some (.primitive .i32 null)
  | .i64 => some (.primitive .i64 null)
  | .f32 => some (.primitive .f32 null)
  | .f64 => some (.primitive .f64 null)
  | .string => some (.utf8 null)
  | .bytes => some (.binary null)
  | .option a => Ty.lower sem .nullable a
  | .result _ _ =>
      -- Vortex has no result dtype; the promised tag+payload union has
      -- not landed. Refuse (none) rather than silently drop the err
      -- side into a wrong artifact that succeeds.
      none
  | .list a => do
      -- the element's nullability is its own (non-nullable); `null`
      -- stamps the LIST's top-level flag only
      let inner ← Ty.lower sem .nonNullable a
      some (DType.list inner null)
  | .tensor _ a =>
      -- the flat form: a tensor column is a LIST of its elements (row
      -- major); the static dims are schema metadata, not Vortex dtype
      -- data. The element's nullability is its own (non-nullable), the
      -- `list` precedent.
      do
        let inner ← Ty.lower sem .nonNullable a
        some (DType.list inner null)
  | .future _ => none  -- not tabular
  | .stream _ => none  -- not tabular
  | .ty n => (sem n).map (·.withNullability null)

/-- Lower a list of named fields to a Vortex struct dtype. -/
def lowerFields (sem : VortexSem) (null : Nullability)
    (fields : List (String × Ty)) : Option StructFields :=
  fields.mapM fun (n, t) => do
    let dt ← Ty.lower sem null t
    return (n, dt)

end SchemaLang.Vortex

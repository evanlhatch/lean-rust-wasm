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

import SchemaLang.Item
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

/-! ## The checked twin (W7.9 phase 2)

`Ty.lowerChecked` is `Ty.lower` arm by arm with ONE difference: the
field-position ban's evidence (`t.banAsync = true` — projected from a
`CheckedUniverse`'s `WellFormed` through
`WellFormed.noAsync_of_record_field` + `banAsync_iff_noAsyncTy`) rides
the input, so the `.future`/`.stream` arms are not fallback `none`s
but ABSURDITY eliminations (`Bool.noConfusion` on `false = true`).
The defensive skip is unrepresentable on this path;
`Ty.lowerChecked_eq_lower` certifies the two lowerings — and hence
the emitted bytes — coincide. -/

/-- The checked lowering: every arm is `Ty.lower`'s own; the async
    arms are discharged BY the evidence. -/
def Ty.lowerChecked (sem : VortexSem) (null : Nullability) :
    (t : Ty) → t.banAsync = true → Option DType
  | .bool, _ => some (.bool null)
  | .u8, _ => some (.primitive .u8 null)
  | .u16, _ => some (.primitive .u16 null)
  | .u32, _ => some (.primitive .u32 null)
  | .u64, _ => some (.primitive .u64 null)
  | .i8, _ => some (.primitive .i8 null)
  | .i16, _ => some (.primitive .i16 null)
  | .i32, _ => some (.primitive .i32 null)
  | .i64, _ => some (.primitive .i64 null)
  | .f32, _ => some (.primitive .f32 null)
  | .f64, _ => some (.primitive .f64 null)
  | .string, _ => some (.utf8 null)
  | .bytes, _ => some (.binary null)
  | .option a, h => Ty.lowerChecked sem .nullable a h
  | .result _ _, _ => none
  | .list a, h => do
      let inner ← Ty.lowerChecked sem .nonNullable a h
      some (DType.list inner null)
  | .tensor _dims a, h => do
      let inner ← Ty.lowerChecked sem .nonNullable a h
      some (DType.list inner null)
  | .future _, h => Bool.noConfusion h
  | .stream _, h => Bool.noConfusion h
  | .ty n, _ => (sem n).map (·.withNullability null)

/-- The checked and unchecked lowerings coincide — the evidence
    changes nothing computational (the byte-tie's theorem form). -/
theorem Ty.lowerChecked_eq_lower (sem : VortexSem) (t : Ty)
    (h : t.banAsync = true) (null : Nullability) :
    Ty.lowerChecked sem null t h = Ty.lower sem null t := by
  induction t generalizing null with
  | bool => rfl
  | u8 => rfl
  | u16 => rfl
  | u32 => rfl
  | u64 => rfl
  | i8 => rfl
  | i16 => rfl
  | i32 => rfl
  | i64 => rfl
  | f32 => rfl
  | f64 => rfl
  | string => rfl
  | bytes => rfl
  | option _ ih => exact ih h .nullable
  | result _ _ _ _ => rfl
  | list _ ih =>
      simp only [Ty.lowerChecked, Ty.lower]
      rw [ih h .nonNullable]
  | tensor _ _ ih =>
      simp only [Ty.lowerChecked, Ty.lower]
      rw [ih h .nonNullable]
  | future _ => exact Bool.noConfusion h
  | stream _ => exact Bool.noConfusion h
  | ty _ => rfl

/-- The checked field-list fold: the per-field `banAsync` evidence
    (from the `CheckedUniverse`) rides the recursion. Computationally
    `lowerFields` — the agreement theorem below. -/
def lowerFieldsChecked (sem : VortexSem) (null : Nullability) :
    (fields : List (String × Ty)) →
    (∀ p, p ∈ fields → p.2.banAsync = true) → Option StructFields
  | [], _ => some []
  | (n, t) :: rest, h => do
      let dt ← Ty.lowerChecked sem null t (h (n, t) List.mem_cons_self)
      let fs ← lowerFieldsChecked sem null rest
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      return (n, dt) :: fs

/-- The checked and unchecked field folds coincide. -/
theorem lowerFieldsChecked_eq_lowerFields (sem : VortexSem) (null : Nullability)
    (fields : List (String × Ty))
    (h : ∀ p, p ∈ fields → p.2.banAsync = true) :
    lowerFieldsChecked sem null fields h = lowerFields sem null fields := by
  induction fields with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨n, t⟩ := p
      have e1 := Ty.lowerChecked_eq_lower sem t (h (n, t) List.mem_cons_self) null
      have e2 := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
      -- both folds unfold to the same bind chain (bind_assoc/pure_bind
      -- reconcile the mapM-cons shape with the checked cons shape)
      simp only [lowerFieldsChecked, lowerFields, List.mapM_cons, e1, e2,
        bind_assoc, pure_bind]

end SchemaLang.Vortex

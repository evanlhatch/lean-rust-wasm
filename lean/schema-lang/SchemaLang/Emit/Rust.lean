/-
# SchemaLang.Emit.Rust — the Rust target

Fold `Item`s to the rich Rust domain crate. Records → structs, variants
→ enums; func signatures are NOT emitted here (they are the WIT world's
exports — the component-host glue consumes the WIT in Phase 5).

Lowering (target-neutral universe → Rust):
- scalars 1:1 (`bool`, `u8`…`u64`, `i8`…`i64`, `f32`, `f64`)
- `string` → `String`, `bytes` → `Vec<u8>`
- `option`/`result`/`list` → `Option`/`Result`/`Vec` (1:1)
- `map`/`set` → `BTreeMap`/`BTreeSet` (deterministic — the runbook
  default; `KeyTy` scalars are all `Ord`)
- `future`/`stream` unreachable in field position (wellFormed bans —
  the flatland audit doctrine: the emitter may assume checked input)
- `.ty n` → `Pascal n`

Derives come from `derivesFor`: `baseDerives` + conditional `Eq`
(f32/f64 don't implement Eq, and named refs are RESOLVED against the
universe — a float behind a `.ty` ref still blocks `Eq`; fast-observe,
bon, serde land with the faults/tabular packages). Names pre-mangled via
`Emit.pascal`/`rustIdent` — the AST never case-converts.
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Wf
public import SchemaLang.Emit.GenCtx

@[expose] public section

namespace SchemaLang.Emit.Rust

open CodegenCore.Emit (pascal rustIdent)

/-- The base derives stamped on every generated type. Eq is added
    conditionally — f32/f64 don't implement Eq. -/
def baseDerives : List String := ["Clone", "Debug", "PartialEq"]

/-- Float check with a ref-semantics: structural on the Ty; refs
    consult `sem` (an already-resolved verdict per name). -/
def hasFloatWith (sem : String → Bool) : Ty → Bool
  | .f32 | .f64 => true
  | .option a => hasFloatWith sem a
  | .result ok err => hasFloatWith sem ok || hasFloatWith sem err
  | .list a => hasFloatWith sem a
  | .map _ v => hasFloatWith sem v  -- the key is a `KeyTy` scalar: float-free
  | .set _ => false                 -- a `KeyTy` scalar: float-free
  | .future a => hasFloatWith sem a
  | .stream a => hasFloatWith sem a
  | .ty n => sem n
  | _ => false

/-- The ref verdicts, fuel-bounded like `Vortex.Emit.refSem`: a name is
    float-CONTAINING unless resolvable-and-clean. The failure mode this
    conservatism prevents: a record deriving `Eq` while the type behind
    its named ref doesn't implement it (generated Rust that doesn't
    compile). Fuel exhaustion / unresolvable / non-type refs → `true`. -/
def floatRefs (items : List Item) : Nat → String → Bool
  | 0, _ => true
  | fuel + 1, n =>
      match items.find? (·.name == n) with
      | some (.record _ fields) =>
          fields.any fun f => hasFloatWith (floatRefs items fuel) f.ty
      | some (.variant _ cases) =>
          cases.any fun (_, payload) =>
            match payload with
            | some t => hasFloatWith (floatRefs items fuel) t
            | none => false
      | _ => true

/-- Check whether a Ty's Rust lowering contains a float type, resolving
    named refs against the universe (fuel-bounded; unresolvable or
    over-deep refs are conservatively float-CONTAINING). -/
def hasFloat (items : List Item) (t : Ty) (fuel : Nat := 8) : Bool :=
  hasFloatWith (floatRefs items fuel) t

/-- The derives for a type whose parts are `tys` (record fields or
    variant payloads): `Eq` joins the base derives iff NO part — refs
    resolved against the universe — contains a float. The ONE
    Eq-eligibility fold: the Rust emitter and the Delta change enums
    both consume it (single fix site for the `Eq`-behind-a-ref bug). -/
def derivesFor (items : List Item) (tys : List Ty) : List String :=
  if tys.any (hasFloat items) then baseDerives else baseDerives ++ ["Eq"]

/-- The map/set KEY rendering, DIRECT (the `KeyTy.toTy` indirection
    breaks `tyRust`'s structural recursion; the arms are exactly the
    scalar text `tyRust` gives the injected types). -/
def keyRust : KeyTy → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .string => "String"

/-- Lower a `Ty` to Rust type text. `future`/`stream` cannot reach this
    in field position (wellFormed bans them); if a func-signature
    emitter reuses this, the future unwraps at `async`. -/
def tyRust : Ty → String
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .f32 => "f32" | .f64 => "f64"
  | .string => "String"
  | .bytes => "Vec<u8>"
  -- the flat form: `Vec<elem>` (row-major; the dims are schema
  -- metadata — a shape-bearing newtype is v2 with the derives work)
  | .tensor _ a => s!"Vec<{tyRust a}>"
  -- BTreeMap/BTreeSet, NOT HashMap/HashSet: deterministic iteration
  -- order (the runbook default — generated artifacts and any
  -- order-observing downstream code are stable). `KeyTy` scalars are
  -- all `Ord`, so the tree types' bounds hold by construction
  | .map k v => s!"BTreeMap<{keyRust k}, {tyRust v}>"
  | .set k => s!"BTreeSet<{keyRust k}>"
  | .option a => s!"Option<{tyRust a}>"
  | .result ok err => s!"Result<{tyRust ok}, {tyRust err}>"
  | .list a => s!"Vec<{tyRust a}>"
  | .future a | .stream a => tyRust a
  | .ty n => pascal n

-- NOT a `DefaultVal` rendering (the consolidation's honest-gap note):
-- `fresh` is the delta lane's patch-value axis, not the semantic zero,
-- and the `none` arms are self-contained-literal exclusions (the
-- tensor's shape-checked ctor, map/set's `std::collections` import,
-- `.ty` refs) — a target-specific rendering table, kept as such.
/-- The self-contained Rust literal per `Ty`, parameterized over the
    ONE axis the two consumers differ on: a FRESH value (the delta
    lane's patch-roundtrip test value — `fresh = true`) vs the ZERO
    default (the invariant lane's default test row — `fresh = false`).
    `none` = no self-contained literal (the nested-record rule: a
    tensor's shape needs a shape-checked constructor; map/set need the
    `std::collections` import in the emitted test module — not
    pinned, so `none`, the tensor rule). -/
def rustLiteral? (fresh : Bool) : Ty → Option String
  | .bool => some (if fresh then "true" else "false")
  | .u8 => some (if fresh then "1" else "0u8")
  | .u16 => some (if fresh then "1" else "0u16")
  | .u32 => some (if fresh then "1" else "0u32")
  | .u64 => some (if fresh then "1" else "0u64")
  | .i8 => some (if fresh then "1" else "0i8")
  | .i16 => some (if fresh then "1" else "0i16")
  | .i32 => some (if fresh then "1" else "0i32")
  | .i64 => some (if fresh then "1" else "0i64")
  | .f32 => some (if fresh then "1.0" else "0.0f32")
  | .f64 => some (if fresh then "1.0" else "0.0f64")
  | .string => some (if fresh then "\"a\".into()" else "String::new()")
  | .bytes => some (if fresh then "vec![]" else "Vec::new()")
  | .option _ => some "None"
  | .result ok _ =>
      if fresh then ("Ok(" ++ · ++ ")") <$> rustLiteral? fresh ok else none
  | .list _ => some (if fresh then "vec![]" else "Vec::new()")
  | .tensor _ _ => none
  | .map _ _ | .set _ => none
  | .future a | .stream a => if fresh then rustLiteral? fresh a else none
  | .ty _ => none

/-- The registry lanes' module-assembly skeleton (the invariant and
    update emitters' shared shape): header comment lines + a blank, one
    `use crate::schema_generated::<Pascal rec>` per record + a blank,
    the flat per-item fns + a blank, the per-record fns, and the
    optional trailing `#[cfg(test)]` module (`use super::*;` supplied
    here). Deterministic: registry order throughout. -/
def recordGroupedModule (header : List String) (records : List String)
    (itemFns perRecordFns : List CodegenCore.Emit.Rust.Item)
    (testMod : Option (String × List CodegenCore.Emit.Rust.Item)) :
    List CodegenCore.Emit.Rust.Item :=
  header.map .comment ++ [.raw ""]
    ++ records.map (fun rec => .use_ s!"crate::schema_generated::{pascal rec}")
    ++ [.raw ""]
    ++ itemFns
    ++ [.raw ""]
    ++ perRecordFns
    ++ match testMod with
       | none => []
       | some (name, items) =>
           [.raw "#[cfg(test)]", .mod_ name ([.raw "use super::*;"] ++ items)]

/-- A record → `struct` item. Name + fields DIRECT — the caller's kind
    fold guarantees the constructor, so the old `Item → Item`-shape's
    fallback arm (`.comment "recordItem: not a record"` — a comment
    where the struct should be, the defensive dead arm) is DELETED:
    dead by construction is now dead by signature. -/
def recordItem (derives : List String) (n : String) (fields : List SchemaLang.Field) :
    CodegenCore.Emit.Rust.Item :=
  .struct (pascal n) derives
    (fields.map fun f => { name := rustIdent f.name, ty := tyRust f.ty })

/-- A variant → `enum` item (payload cases carry their type). Name +
    cases DIRECT — same signature argument as `recordItem`. -/
def variantItem (derives : List String) (n : String) (cases : List SchemaLang.VariantCase) :
    CodegenCore.Emit.Rust.Item :=
  .enum (pascal n) derives
    (cases.map fun (c, payload) =>
      match payload with
      | some t => s!"{pascal c}({tyRust t})"
      | none => pascal c)

/-- A full universe → the Rust module items (types only; funcs are the
    WIT world's exports, not Rust-side types). Derives come from
    `derivesFor` — `Eq` exactly when the fields/payloads (refs resolved
    against `items`) are float-free. -/
def schemaItems (items : List Item) :
    List CodegenCore.Emit.Rust.Item :=
  items.filterMap fun it =>
    match it with
    | .record n fields =>
        some (recordItem (derivesFor items (fields.map (·.ty))) n fields)
    | .variant n cases =>
        some (variantItem (derivesFor items (cases.filterMap (·.2))) n cases)
    | _ => none

/-! ## W7.9 phase 2 sweep — the checked universe view

The emitter consumes a `CheckedUniverse` (`{ items // WellFormed items
}`) through `GenCtx.checkedItems?` — the single checkpoint (one
`universeCheck` discharge per universe, in GenCtx.lean). On the checked
path the per-field lowering is `tyRustNA`: the async evidence
(`NoAsyncTy`, projected from the `WellFormed` bundle through
`WellFormed.noAsync_of_record_field` / the variant-arm projection
below) rides the recursion, so `tyRust`'s `future`/`stream`
silent-unwrap arms — the header's ill-formed-input fallback (asyncness
silently dropped) — are UNREPRESENTABLE on this path (`NoAsyncTy` has
no async constructors: `nomatch`, not a fallback rendering).
`schemaItemsChecked_eq` certifies the bytes are the raw path's own.
`schemaItems` stays the raw-input entry point (Tests over synthetic
universes — the honest seam; the registry driver path goes through the
checkpoint). -/

/-- The variant-arm projection of the `WellFormed` bundle (the record
    arm's sibling, `WellFormed.noAsync_of_record_field`, for payload
    types; stated here — the emit tree owns its projections, the
    vortex lane's `checked_field_*` precedent). -/
theorem WellFormed.noAsync_of_variant_case {items : List Item}
    (hwf : WellFormed items) {n : String} {cases : List VariantCase}
    (hit : Item.variant n cases ∈ items) {c : String} {t : Ty}
    (hct : (c, some t) ∈ cases) : NoAsyncTy t := by
  cases hwf with
  | mk hitems _ _ _ =>
      cases hitems _ hit with
      | variant hna _ _ _ => exact hna c t hct

/-- The sub-evidence projections: `NoAsyncTy`'s composite ctors carry
    the child evidence EXPLICITLY (the type args are implicit), so the
    dependent `match` cannot name it positionally — these defs are the
    named projections (definitional: iota on the ctor). -/
def NoAsyncTy.invOption {a : Ty} : NoAsyncTy (.option a) → NoAsyncTy a
  | .option ha => ha

def NoAsyncTy.invResult {ok err : Ty} :
    NoAsyncTy (.result ok err) → NoAsyncTy ok ∧ NoAsyncTy err
  | .result hok herr => ⟨hok, herr⟩

def NoAsyncTy.invList {a : Ty} : NoAsyncTy (.list a) → NoAsyncTy a
  | .list ha => ha

def NoAsyncTy.invMap {k : KeyTy} {v : Ty} : NoAsyncTy (.map k v) → NoAsyncTy v
  | .map hv => hv

def NoAsyncTy.invTensor {dims : List Nat} {a : Ty} :
    NoAsyncTy (.tensor dims a) → NoAsyncTy a
  | .tensor ha => ha

/-- The checked Ty lowering: every arm is `tyRust`'s own; the async
    arms are discharged BY the evidence (empty family — `nomatch`). -/
def tyRustNA : (t : Ty) → NoAsyncTy t → String
  | .bool, _ => "bool"
  | .u8, _ => "u8" | .u16, _ => "u16" | .u32, _ => "u32" | .u64, _ => "u64"
  | .i8, _ => "i8" | .i16, _ => "i16" | .i32, _ => "i32" | .i64, _ => "i64"
  | .f32, _ => "f32" | .f64, _ => "f64"
  | .string, _ => "String"
  | .bytes, _ => "Vec<u8>"
  | .tensor _ a, h => s!"Vec<{tyRustNA a (NoAsyncTy.invTensor h)}>"
  | .map k v, h => s!"BTreeMap<{keyRust k}, {tyRustNA v (NoAsyncTy.invMap h)}>"
  | .set k, _ => s!"BTreeSet<{keyRust k}>"
  | .option a, h => s!"Option<{tyRustNA a (NoAsyncTy.invOption h)}>"
  | .result ok err, h =>
      s!"Result<{tyRustNA ok (NoAsyncTy.invResult h).1}, {tyRustNA err (NoAsyncTy.invResult h).2}>"
  | .list a, h => s!"Vec<{tyRustNA a (NoAsyncTy.invList h)}>"
  | .future _, h => nomatch h
  | .stream _, h => nomatch h
  | .ty n, _ => pascal n

/-- The checked and unchecked lowerings coincide — the evidence
    changes nothing computational (the byte-tie's theorem form). -/
theorem tyRustNA_eq : ∀ (t : Ty) (h : NoAsyncTy t), tyRustNA t h = tyRust t := by
  intro t
  induction t with
  | bool => intro _; rfl
  | u8 => intro _; rfl
  | u16 => intro _; rfl
  | u32 => intro _; rfl
  | u64 => intro _; rfl
  | i8 => intro _; rfl
  | i16 => intro _; rfl
  | i32 => intro _; rfl
  | i64 => intro _; rfl
  | f32 => intro _; rfl
  | f64 => intro _; rfl
  | string => intro _; rfl
  | bytes => intro _; rfl
  | tensor _ a ih => intro h; cases h with | tensor ha =>
      simp only [tyRustNA, NoAsyncTy.invTensor, tyRust]; rw [ih ha]
  | map _ v ih => intro h; cases h with | map hv =>
      simp only [tyRustNA, NoAsyncTy.invMap, tyRust]; rw [ih hv]
  | set _ => intro _; rfl
  | option a ih => intro h; cases h with | option ha =>
      simp only [tyRustNA, NoAsyncTy.invOption, tyRust]; rw [ih ha]
  | result ok err ihok iherr => intro h; cases h with | result hok herr =>
      simp only [tyRustNA, NoAsyncTy.invResult, tyRust];
      rw [ihok hok, iherr herr]
  | list a ih => intro h; cases h with | list ha =>
      simp only [tyRustNA, NoAsyncTy.invList, tyRust]; rw [ih ha]
  | future _ ih => intro h; cases h
  | stream _ ih => intro h; cases h
  | ty _ => intro _; rfl

/-- The checked struct-field fold: the per-field async evidence rides
    the recursion (the membership wall: a `map` lambda carries no
    membership proof, so the fold is structural — the vortex lane's
    `lowerFieldsChecked` shape). -/
def recordFieldsChecked : (fields : List SchemaLang.Field) →
    (∀ f, f ∈ fields → NoAsyncTy f.ty) →
    List CodegenCore.Emit.Rust.Field
  | [], _ => []
  | f :: rest, h =>
      { name := rustIdent f.name, ty := tyRustNA f.ty (h f List.mem_cons_self) }
        :: recordFieldsChecked rest
          (fun g hg => h g (List.mem_cons_of_mem _ hg))

/-- The checked and unchecked field folds coincide. -/
theorem recordFieldsChecked_eq :
    ∀ (fields : List SchemaLang.Field) (h : ∀ f, f ∈ fields → NoAsyncTy f.ty),
      recordFieldsChecked fields h =
        fields.map fun f => ({ name := rustIdent f.name, ty := tyRust f.ty } :
          CodegenCore.Emit.Rust.Field) := by
  intro fields
  induction fields with
  | nil => intro _; rfl
  | cons g rest ih =>
      intro h
      simp only [recordFieldsChecked, List.map_cons]
      rw [tyRustNA_eq g.ty (h g List.mem_cons_self),
        ih (fun k hk => h k (List.mem_cons_of_mem _ hk))]

/-- The checked record item: `recordItem` with the evidence threading
    the field fold. -/
def recordItemChecked (derives : List String) (n : String)
    (fields : List SchemaLang.Field) (h : ∀ f, f ∈ fields → NoAsyncTy f.ty) :
    CodegenCore.Emit.Rust.Item :=
  .struct (pascal n) derives (recordFieldsChecked fields h)

theorem recordItemChecked_eq (derives : List String) (n : String)
    (fields : List SchemaLang.Field) (h : ∀ f, f ∈ fields → NoAsyncTy f.ty) :
    recordItemChecked derives n fields h = recordItem derives n fields := by
  simp only [recordItemChecked, recordItem, recordFieldsChecked_eq fields h]

/-- The checked enum-payload fold: the per-case async evidence (the
    `ItemWf.variant` arm's payload projection) rides the recursion. -/
def variantCasesChecked : (cases : List SchemaLang.VariantCase) →
    (∀ c t, (c, some t) ∈ cases → NoAsyncTy t) → List String
  | [], _ => []
  | (c, none) :: rest, h =>
      pascal c :: variantCasesChecked rest
        (fun c' t' hct => h c' t' (List.mem_cons_of_mem _ hct))
  | (c, some t) :: rest, h =>
      s!"{pascal c}({tyRustNA t (h c t List.mem_cons_self)})" :: variantCasesChecked rest
        (fun c' t' hct => h c' t' (List.mem_cons_of_mem _ hct))

/-- The checked and unchecked payload folds coincide. -/
theorem variantCasesChecked_eq :
    ∀ (cases : List SchemaLang.VariantCase)
      (h : ∀ c t, (c, some t) ∈ cases → NoAsyncTy t),
      variantCasesChecked cases h =
        cases.map fun (c, payload) =>
          match payload with
          | some t => s!"{pascal c}({tyRust t})"
          | none => pascal c := by
  intro cases
  induction cases with
  | nil => intro _; rfl
  | cons x rest ih =>
      intro h
      cases x with
      | mk c payload =>
          cases payload with
          | none =>
              simp only [variantCasesChecked, List.map_cons, ih]
          | some t =>
              simp only [variantCasesChecked, List.map_cons]
              rw [tyRustNA_eq t (h c t List.mem_cons_self),
                ih (fun c' t' hct => h c' t' (List.mem_cons_of_mem _ hct))]

/-- The checked variant item: `variantItem` with the evidence threading
    the payload fold. -/
def variantItemChecked (derives : List String) (n : String)
    (cases : List SchemaLang.VariantCase)
    (h : ∀ c t, (c, some t) ∈ cases → NoAsyncTy t) :
    CodegenCore.Emit.Rust.Item :=
  .enum (pascal n) derives (variantCasesChecked cases h)

theorem variantItemChecked_eq (derives : List String) (n : String)
    (cases : List SchemaLang.VariantCase)
    (h : ∀ c t, (c, some t) ∈ cases → NoAsyncTy t) :
    variantItemChecked derives n cases h = variantItem derives n cases := by
  simp only [variantItemChecked, variantItem, variantCasesChecked_eq cases h]

/-- The checked record-table worker: the evidence is projected ONCE
    from the `WellFormed` bundle at `schemaItemsChecked` and threaded
    through the recursion (the membership wall: a `filterMap` lambda
    carries no membership proof, so the fold is structural here — the
    vortex lane's `recordDTypesCheckedGo` shape). `full` is the WHOLE
    universe, threaded unchanged: `derivesFor`'s ref resolution is a
    full-universe fact, so the per-item evidence (quantified over the
    fold's own `items`) rides alongside it. -/
def schemaItemsCheckedGo (full : List Item) :
    (items : List Item) →
    (∀ n fields, Item.record n fields ∈ items →
      ∀ f, f ∈ fields → NoAsyncTy f.ty) →
    (∀ n cases, Item.variant n cases ∈ items →
      ∀ c t, (c, some t) ∈ cases → NoAsyncTy t) →
    List CodegenCore.Emit.Rust.Item
  | [], _, _ => []
  | it :: rest, hrec, hvar =>
      let go := schemaItemsCheckedGo full rest
        (fun n' fs hit => hrec n' fs (List.mem_cons_of_mem _ hit))
        (fun n' cs hit => hvar n' cs (List.mem_cons_of_mem _ hit))
      match it with
      | .record n fields =>
          recordItemChecked (derivesFor full (fields.map (·.ty))) n fields
            (hrec n fields List.mem_cons_self) :: go
      | .variant n cases =>
          variantItemChecked (derivesFor full (cases.filterMap (·.2))) n cases
            (hvar n cases List.mem_cons_self) :: go
      | .func _ => go
      | .resource _ => go

/-- The worker agrees with the shared spine, item list by item list
    (the spine's own filterMap lambda, with `derivesFor` resolved
    against the same full universe). -/
theorem schemaItemsCheckedGo_eq (full : List Item) :
    ∀ (items : List Item)
      (hrec : ∀ n fields, Item.record n fields ∈ items →
        ∀ f, f ∈ fields → NoAsyncTy f.ty)
      (hvar : ∀ n cases, Item.variant n cases ∈ items →
        ∀ c t, (c, some t) ∈ cases → NoAsyncTy t),
      schemaItemsCheckedGo full items hrec hvar =
        items.filterMap (fun it =>
          match it with
          | .record n fields =>
              some (recordItem (derivesFor full (fields.map (·.ty))) n fields)
          | .variant n cases =>
              some (variantItem (derivesFor full (cases.filterMap (·.2))) n cases)
          | _ => none) := by
  intro items
  induction items with
  | nil => intro _ _; rfl
  | cons it rest ih =>
      intro hrec hvar
      simp only [schemaItemsCheckedGo, List.filterMap_cons]
      cases it with
      | record n fields =>
          simp only [recordItemChecked_eq,
            ih (fun n' fs hit => hrec n' fs (List.mem_cons_of_mem _ hit))
              (fun n' cs hit => hvar n' cs (List.mem_cons_of_mem _ hit))]
      | variant n cases =>
          simp only [variantItemChecked_eq,
            ih (fun n' fs hit => hrec n' fs (List.mem_cons_of_mem _ hit))
              (fun n' cs hit => hvar n' cs (List.mem_cons_of_mem _ hit))]
      | func _ | resource _ =>
          simp only [ih (fun n' fs hit => hrec n' fs (List.mem_cons_of_mem _ hit))
            (fun n' cs hit => hvar n' cs (List.mem_cons_of_mem _ hit))]

/-- Every type item of a CHECKED universe, rendered — the emitter's
    input. The per-field / per-payload async evidence is projected ONCE
    from the `WellFormed` bundle and threaded through the fold. -/
def schemaItemsChecked (cu : CheckedUniverse) : List CodegenCore.Emit.Rust.Item :=
  schemaItemsCheckedGo cu.val cu.val
    (fun _n _fields hit _f hf => WellFormed.noAsync_of_record_field cu.property hit hf)
    (fun _n _cases hit _c _t hct => WellFormed.noAsync_of_variant_case cu.property hit hct)

/-- BYTES PRESERVED (the theorem half of the byte-tie): the checked
    item table IS the unchecked one — the evidence changes nothing
    computational. -/
theorem schemaItemsChecked_eq (cu : CheckedUniverse) :
    schemaItemsChecked cu = schemaItems cu.val := by
  simp only [schemaItemsChecked, schemaItemsCheckedGo_eq]
  rfl

/-! ## The emission law (the vortex lane's `vortexLaw` shape) -/

/-- The Rust emitter's law: whenever the ctx's checked view exists,
    every field of every record and every payload of every variant in
    the checked universe is async-free — the evidence the checked fold
    consumes, bundled as one `GenCtx → Prop` (the shape `Emitter.law`
    takes). -/
def rustLaw (ctx : GenCtx) : Prop :=
  ∀ cu : CheckedUniverse, ctx.checkedItems? = some cu →
    (∀ (n : String) (fields : List SchemaLang.Field),
        Item.record n fields ∈ cu.val →
        ∀ (f : SchemaLang.Field), f ∈ fields → NoAsyncTy f.ty)
    ∧ (∀ (n : String) (cases : List VariantCase),
        Item.variant n cases ∈ cu.val → ∀ (c : String) (t : Ty),
          (c, some t) ∈ cases → NoAsyncTy t)

/-- The discharge: one citation per clause (`noAsync_of_record_field`,
    `noAsync_of_variant_case`). Certified drivers hand
    `rustLaw_discharged ctx` to `Emitter.runCertified`. -/
theorem rustLaw_discharged (ctx : GenCtx) : rustLaw ctx := by
  intro cu _
  exact ⟨fun _n _fields hit _f hf =>
      WellFormed.noAsync_of_record_field cu.property hit hf,
    fun _n _cases hit _c _t hct =>
      WellFormed.noAsync_of_variant_case cu.property hit hct⟩

end SchemaLang.Emit.Rust

/-- The Rust emitter plugin: rich domain types.

    W7.9 phase 2 sweep: the item universe is consumed through the
    CHECKED view (`GenCtx.checkedItems?` — the single checkpoint, one
    `universeCheck` discharge per universe). The checked fold's
    `future`/`stream` arms are unrepresentable (`tyRustNA`'s `nomatch`
    — the raw `tyRust`'s silent unwrap cannot fire); the bytes are the
    raw path's own (`schemaItemsChecked_eq` + the byte-tie gate). The
    `none` arm is the pre-evidence fallback for callers that never ran
    the check (test fixtures over synthetic universes) — the paths
    agree, so either way the output is identical.

    W7.3 phase 2: `law` is POPULATED (`rustLaw` — the field/payload
    async-freedom as the emission contract), discharged by
    `rustLaw_discharged`; Tests execute the certified lane
    (`runCertified` = `run`, asserted over the demo ctx). -/
def rustEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "rust"
  style := .doubleSlash
  specSource := "Demo.lean"
  outputs := ["../../generated/rust/schema_generated.rs"]
  run ctx :=
    let items := match ctx.checkedItems? with
      | some cu => SchemaLang.Emit.Rust.schemaItemsChecked cu
      | none => SchemaLang.Emit.Rust.schemaItems ctx.items
    [
      { path := "../../generated/rust/schema_generated.rs"
        contents := CodegenCore.Emit.Rust.renderModule items }
    ]
  law := some SchemaLang.Emit.Rust.rustLaw

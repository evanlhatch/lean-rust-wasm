/-
# SchemaLang.Migration — the REMEDY half of the breaking gate (6.5.2)

`Diff` DETECTS breaking changes; this module carries the evidence that
one is REMEDIABLE (event-sourcing upcasting: the old log is replayable
through the migration). The shape, per the flatland SPEC-core §2
transfer:

- for each retyped field, a TOTAL function old-value → new-value AS
  LEAN DATA (`FieldMigration.apply` — its TYPE is the soundness shape:
  `oldTy` values in, `newTy` values out, no partiality expressible);
- the soundness obligation `applyMigration old = new`, discharged per
  instance (the exemplar: `widenU32U64_sound`);
- a three-way gate verdict (`CompatVerdict`) so a breaking change WITH
  remedy evidence reports differently from one without.

Deliberately minimal (the deliverable is the TYPE + one exemplar + its
theorem, not a framework): v1 remedies cover RETYPED fields over the
closed fragment only (named refs map to `Empty` under `emptySem`, so a
remedy over an unresolved shape is unconstructible — no hand-waved
"the host will fix it"). Removals, and `semChanged` (6.5.1) drift, are
honestly UNREMEDIED. The migration AUTHORING surface (an attribute
registering `Migration`s the `schema-breaking` exe would consume) is
the documented follow-up — the exe passes `[]` until the first real
breaking change needs one; the verdict machinery below is exercised in
`Tests/Main.lean` (`migrationChecks`).
-/

import SchemaLang.Diff

namespace SchemaLang

/-- The value sem for migration evidence: remedies are v1-closed to the
    NON-ref fragment — named refs map to `Empty`, so a remedy whose
    old/new type is an unresolved reference is unconstructible. -/
def emptySem : TySem := fun _ => Empty

/-- One field remedy: a retyped field plus its TOTAL value map, as Lean
    data, typed by the schema types themselves — the function's TYPE is
    the soundness shape (`oldTy` values in, `newTy` values out). The
    obligation `applyMigration old = new` is discharged per instance
    (see `widenU32U64_sound`). -/
structure FieldMigration where
  /-- the field on the CHANGED item this remedies -/
  field : String
  oldTy : Ty
  newTy : Ty
  apply : oldTy.toType emptySem → newTy.toType emptySem

/-- Remedy evidence for ONE breaking-changed item: per retyped field,
    the total old→new value map. -/
structure Migration where
  /-- the item name (matches `Change.changed n _`) -/
  item : String
  /-- per-field remedies, keyed by the CHANGED field's name -/
  fields : List FieldMigration

/-- Does this migration REMEDY a change? A `.changed` is remedied when
    every breaking field finding has a matching remedy (the retyped
    field, with exactly the found old/new types). Additions are safe
    (no old data exists to map); removals and `semChanged` drift are
    v1-unremedied (no value-map target — the honest verdict, not an
    oversight); a `.removed` item is unremedied outright. -/
def Migration.remedies (m : Migration) (c : Change) : Bool :=
  match c with
  | .added _ => true
  | .removed _ => false
  | .changed n fds =>
      n == m.item && fds.all fun
        | .fieldAdded _ => true
        | .fieldTypeChanged f oldTy newTy =>
            m.fields.any fun fm =>
              fm.field == f && fm.oldTy == oldTy && fm.newTy == newTy
        | .fieldRemoved _ | .semChanged _ _ => false

/-- The breaking gate's verdict: three-way, so a breaking change WITH
    remedy evidence reports differently from one without. -/
inductive CompatVerdict where
  | clean        -- no breaking changes (additions are safe)
  | remedied     -- breaking changes, EVERY one with matching remedy evidence
  | unremedied   -- ≥1 breaking change without remedy evidence
deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString CompatVerdict where
  toString
    | .clean => "clean"
    | .remedied => "remedied"
    | .unremedied => "unremedied"

/-- The breaking subset of a diff: anything but `.added`. One
    definition — `verdictOf` and BreakingMain used to each inline this
    filter; the gate's notion of "breaking" now has a single name. -/
def breakingOf (changes : List Change) : List Change :=
  changes.filter fun c => match c with | .added _ => false | _ => true

/-- The verdict over a diff plus the available remedy evidence.
    Breaking = anything but `.added`; remedied requires EVERY breaking
    change covered by some migration. -/
def verdictOf (changes : List Change) (migrations : List Migration) : CompatVerdict :=
  let breaking := breakingOf changes
  if breaking.isEmpty then .clean
  else if breaking.all fun c => migrations.any (·.remedies c) then .remedied
  else .unremedied

/-- The gate's exit semantics — the ONLY mapping (exes consume this,
    never hand-map at call sites):

    - `clean` → 0 (silent success)
    - `remedied` → 2 — deliberately distinct from both: the change is
      shippable (the remedy exists and its soundness theorem
      discharged) but ACTION is required — apply the migration to the
      event log, then re-baseline the snapshot. `just gates` fails on
      2: a remedy never applied is not a remedy, and a warning that CI
      ignores is not a warning.
    - `unremedied` → 1 (the change breaks consumers with no remedy). -/
def CompatVerdict.exitCode : CompatVerdict → UInt32
  | .clean => 0
  | .unremedied => 1
  | .remedied => 2

/-! ## The exemplar: integer widening (`u32 → u64`)

The type is inhabitable and the obligation discharges. Widening is
generic — any retyped integer field widens exactly — so the exemplar
ships WITH the type (the doctrine's instances-ship-with-the-spec rule),
parameterized by the field name. -/

/-- A u32→u64 widening remedy for `field`: every u32 value maps to the
    SAME number as a u64 (widening, not reinterpretation). -/
def widenU32U64 (field : String) : FieldMigration :=
  { field, oldTy := .u32, newTy := .u64
  , apply := fun old => old.toUInt64 }

/-- Soundness, in the `applyMigration old = new` shape: applying the
    remedy to an old value yields the new-typed value OF THE SAME
    NUMBER — the non-vacuous content is the `.toNat` equation (the
    bare `apply old = old.toUInt64` would be the definition restated).
    Discharged by core's `UInt32.toNat_toUInt64` (`rfl`). -/
theorem widenU32U64_sound (field : String) (old : UInt32) :
    ((widenU32U64 field).apply old).toNat = old.toNat := rfl

end SchemaLang

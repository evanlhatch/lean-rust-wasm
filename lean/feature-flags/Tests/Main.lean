/-
# FeatureFlags tests — the gate files' driver

The dogfood service's gate floor: positive + negative controls over the
impl, elaboration-checked (`#guard` fails the BUILD on drift, not just
the run). The TestKit discipline (PropSpec sweeps with the MANDATORY
negative control, DiffSpec for differential gates) grows in here as the
service does.
-/
import Lean
import TestKit
import FeatureFlags
import FeatureFlagsFn
import SchemaLang.Meta.Keys
import Templates
import Tests.Stress



-- Negative control first: the sentinel id → none.
#guard (FeatureFlagsImpl.flag_get 0).isNone

-- Positive control: a real id → some (the record round-trips).
#guard (FeatureFlagsImpl.flag_get 3).map (·.id) == some 3

-- The rollout gate: > 100 = invalidRollout (the domain error, on the
-- result channel's LEFT-ridden... the error half: `inr`).
#guard (match FeatureFlagsImpl.flag_set_rollout 3 150 with | .inr _ => true | _ => false)
#guard ((match FeatureFlagsImpl.flag_set_rollout 3 150 with | .inl _ => true | _ => false) == false)

-- The sentinel refuses the rollout set too.
#guard (match FeatureFlagsImpl.flag_set_rollout 0 50 with | .inr _ => true | _ => false)

-- The in-range set: locked-store v1 (the honest stub — the error says so).
#guard match FeatureFlagsImpl.flag_set_rollout 3 50 with
  | .inr (FlagError.locked _) => true
  | _ => false

-- The delete: the audit entry back (the action spelled).
#guard match FeatureFlagsImpl.flag_delete 7 with
  | .inl e => e.action == "delete" && e.id == 7
  | _ => false

-- The watch: the empty key = the empty stream.
#guard (FeatureFlagsImpl.flag_watch "").isEmpty
#guard (FeatureFlagsImpl.flag_watch "checkout").map (·.key) == ["checkout"]

/-! ## W8.10 — templates/slots (the feature-flags lesson) -/

-- The template: the keyed-record shape Flag and AuditEntry share,
-- declared ONCE. `key` is a SCALAR slot (the KeyTy sub-universe — it
-- holds a primary key's type); `label` is ANY boundary type.
open Templates in
schema_template keyedRecord where
  slot: key scalar
  slot: label any
  field: id key
  field: name label
  field: note string

-- Instantiation 1: the audit-entry shape (u64 key, string columns).
schema_from_template keyedRecord as auditEntry where
  fill: key := .u64
  fill: label := .string

-- Instantiation 2: a string-keyed record whose label column is a
-- COMPOSITE type through the `any` slot (slot substitution is real
-- substitution — the composite rides the Ty-term form).
schema_from_template keyedRecord as tagRecord where
  fill: key := .string
  fill: label := .list .string

-- The derived surface, per instance: the fresh `<inst>Fields` abbrev
-- (the `derive_schema_fields` item-1 surface), with the fillings
-- substituted in — and the `abbrev` rule holds: instance search sees
-- through it (`HasCol` on the derived list works directly).
#guard auditEntryFields == [⟨"id", SchemaLang.Ty.u64⟩, ⟨"name", SchemaLang.Ty.string⟩, ⟨"note", SchemaLang.Ty.string⟩]
#guard tagRecordFields == [⟨"id", SchemaLang.Ty.string⟩, ⟨"name", SchemaLang.Ty.list SchemaLang.Ty.string⟩, ⟨"note", SchemaLang.Ty.string⟩]

#check (SchemaLang.VExpr.colOf "id" : SchemaLang.VExpr auditEntryFields SchemaLang.Ty.u64)
#check (SchemaLang.VExpr.colOf "name" : SchemaLang.VExpr tagRecordFields (SchemaLang.Ty.list SchemaLang.Ty.string))

-- The registry sees each instance as a REAL item (the same
-- `schemaItemExt` write path `@[schema]` uses).
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let items := SchemaLang.Meta.registeredItems env
  for inst in [`auditEntry, `tagRecord] do
    unless items.any (fun (ln, it) => ln == inst && it.name == inst.toString) do
      throwError s!"W8.10: `{inst}` was not registered as a schema item"

-- The entourage composes: the instance IS a registered record, so the
-- downstream lanes work unchanged — the invariant lane (a LAW per
-- instance) and the key lane (the declared primary key).
schema_invariant "entry-id-positive" for auditEntry :=
  SchemaLang.VExpr.gt (SchemaLang.VExpr.colOf "id") (SchemaLang.VExpr.lit 0)

schema_keys for auditEntry := primary id

-- NEGATIVE CONTROL 1: the contract gate — a `scalar` slot refuses a
-- non-KeyTy filling AT ELABORATION.
/-- error: schema_from_template badFill: slot `key` is declared `scalar` — the filling `SchemaLang.Ty.list (SchemaLang.Ty.string)` does not inject from the KeyTy scalar sub-universe (bool, u8–u64, i8–i64, string) -/
#guard_msgs in
schema_from_template keyedRecord as badFill where
  fill: key := .list .string
  fill: label := .string

-- NEGATIVE CONTROL 2: unknown slot — did-you-mean over the template's
-- declared slot list.
/-- error: schema_from_template badSlot: no slot `kye` — the template declares: key, label — did you mean: key? -/
#guard_msgs in
schema_from_template keyedRecord as badSlot where
  fill: key := .u64
  fill: label := .string
  fill: kye := .u64

-- NEGATIVE CONTROL 3: the fresh-name rule — an instance name colliding
-- with an already-registered item is refused.
/-- error: schema_from_template auditEntry: `auditEntry` is already a registered schema item — instance names must be fresh — did you mean: auditEntry, AuditEntry? -/
#guard_msgs in
schema_from_template keyedRecord as auditEntry where
  fill: key := .u64
  fill: label := .string

def main : IO UInt32 := do
  IO.println "FeatureFlagsTests: guards green (elab-time)"
  match stressChecks with
  | .ok () =>
      IO.println "FeatureFlagsTests: stress sweep green (50-tick LCG + negative control)"
      return 0
  | .error e =>
      IO.eprintln s!"FeatureFlagsTests: stress FAIL: {e}"
      return 1

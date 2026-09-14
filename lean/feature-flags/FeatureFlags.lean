/-
# FeatureFlags spec — the authoring surface (THE source of truth)

DO-NOT-DELETE header: every attribute here has a role in the codegen
pipeline. This module is the SSOT — the WIT world, the Rust types, the
observe spans, and the fault surfaces are all generated from the
registrations BELOW (the `schema-gen` driver replays them from the
oleans). Delete an attribute and the artifact loses the surface
silently; the byte-tie gate catches it only after the fact.

The DOGFOOD SERVICE: a feature-flag store. Real shape, not the demo's
minimum: a keyed flag with a rollout percentage, an audit trail entry,
a domain-error variant carried on the `result` channel, an async watch
surface, and an opaque store resource.

Attribute roles:

- `@[schema]` on a structure/inductive → registers a record/variant in
  the schema registry. Fields must live in the CLOSED boundary universe
  (`Ty`): UInt64/String/List/Option/… — anything else fails at
  elaboration with the fragment enumerated. The generated Rust/WIT type
  is derived from the field list; renaming a field IS a breaking change
  (`just breaking` gates it).
- `@[schema_fn]` on a def → registers a func SIGNATURE. The body is a
  STUB — the signature is the spec (`_id` is the parameter's spec-name,
  underscore-silenced for the dead body). The real body lives in the
  impl module (FeatureFlagsFn.lean). Optional semantic args: `@[schema_fn
  strict]` / `volatile` / `stream` (the FuncSem axes).
- `@[schema_resource]` on an opaque def → an opaque handle type.

Registration order matters (v1 limitation): the referenced type must be
registered before the referencing declaration — keep the record above
the functions that mention it.
-/

import SchemaLang.Meta.Reflect

-- the schema_update registrations here emit their instances into
-- SchemaLang by the framework's construction (Reflect's command) — same
-- as Demo
set_option linter.guestlang.packageNamespace false -- because the framework's registration command emits the instances into SchemaLang by construction; no source-site attribute exists

/-! ## The async markers (WASI 0.3 at the boundary)

DOGFOOD FINDING (moved to the substrate): these lived as per-module
copies (Demo's precedent) because the reifier matches them BY NAME —
the markers now live HERE too, but the real fix is ONE copy in
`SchemaLang.Meta` (the reifier's name-match is the only obstacle).
Tracking as the flags lane's substrate follow-up.
 -/

namespace Async

def Future (a : Type) : Type := a

/-- Defined as `Future` itself: both are boundary markers whose bodies
    are the identity BY DESIGN (the dupDefBodies lesson — one anchor,
    aliases of it). -/
def Stream (a : Type) : Type := Future a

end Async

/-! ## Records -/

/-- A feature flag: the keyed state + the rollout percentage (0–100,
    gated by the `rolloutLe100` invariant) + the description tags. -/
@[schema]
structure Flag where
  id : UInt64
  key : String
  enabled : Bool
  rollout : UInt64
  tags : List String

/-- The audit trail entry: who did what to which flag, when. -/
@[schema]
structure AuditEntry where
  id : UInt64
  flagKey : String
  action : String
  ts : UInt64

/-! ## Variants -/

/-- The domain errors: the result channel's failure half. -/
@[schema]
inductive FlagError where
  | notFound
  | invalidRollout (pct : UInt64)
  | locked (by_ : String)

/-! ## Function signatures (the bodies are NOT part of the spec) -/

/-- u64 → option<flag>: the keyed lookup; id 0 = the absent sentinel. -/
@[schema_fn]
def flag_get (_id : UInt64) : Option Flag :=
  none

/-- Set the rollout: the domain error rides the RESULT channel (the
    invalid percentage > 100 = `invalidRollout`). -/
@[schema_fn]
def flag_set_rollout (_id : UInt64) (_pct : UInt64) :
    Sum Flag FlagError :=
  Sum.inr FlagError.notFound

/-- Delete (retire) a flag: the audit entry back. -/
@[schema_fn]
def flag_delete (_id : UInt64) : Sum AuditEntry FlagError :=
  Sum.inr FlagError.notFound

/-- The async watch surface: the flag stream (WASI 0.3 async). -/
@[schema_fn]
def flag_watch (_key : String) : Async.Future (List Flag) :=
  []

/-! ## Resources -/

/-- The opaque store handle: the schema records it as a resource. -/
@[schema_resource]
def FlagStore : Type := Empty

/-! ## The invariants (the enforcement ladder's rungs) -/

-- THE BOUNDARY RUNG: the key is nonempty (the executable VExpr —
-- emitted as the generated check fn; the elaboration gate = HasCol).
schema_invariant "key-nonempty" for Flag :=
  SchemaLang.VExpr.gt (SchemaLang.VExpr.strlen (SchemaLang.VExpr.colOf "key")) (SchemaLang.VExpr.lit 0)

-- THE BOUNDARY RUNG, ≤-shaped: the rollout never exceeds 100 (the
-- `.not` extension the dogfood demanded — the fragment's ≤-gap).
schema_invariant "rollout-le-100" for Flag :=
  SchemaLang.VExpr.not (SchemaLang.VExpr.gt (SchemaLang.VExpr.colOf "rollout") (SchemaLang.VExpr.lit 100))

-- THE PROVED RUNG: the sentinel contract (the impl module's
-- kernel-checked theorem — the host's defensive none-check is erased).
-- The citation RESOLVES at this command (`SchemaLang.checkCitation?`,
-- the `Dbsp.Certs.#check_cert` gate) — so the cited theorem lives HERE
-- (the impl's mirror, `FeatureFlagsImpl.flag_get_zero_none`, carries
-- the proved-erased tier on the impl side): the registered predicate
-- `0 == 0` is vacuously true on every row; the pinned row witnesses it
-- in the exact `validates … = true` shape the resolver demands.
def flagSentinelRow : SchemaLang.RowVals
    [⟨"id", SchemaLang.Ty.u64⟩, ⟨"key", SchemaLang.Ty.string⟩,
      ⟨"enabled", SchemaLang.Ty.bool⟩, ⟨"rollout", SchemaLang.Ty.u64⟩,
      ⟨"tags", SchemaLang.Ty.list SchemaLang.Ty.string⟩] :=
  .cons (.u64 0) (.cons (.string "") (.cons (.bool false)
    (.cons (.u64 0) (.cons (.list .nil) .nil))))

theorem flag_get_zero_none :
    SchemaLang.validates
      (SchemaLang.VExpr.eq (SchemaLang.VExpr.lit 0) (SchemaLang.VExpr.lit 0))
      flagSentinelRow = true := by
  unfold SchemaLang.validates
  simp only [SchemaLang.evalB, SchemaLang.evalU, SchemaLang.boolToU64]
  rfl

schema_invariant "get-sentinel-none" for Flag proved flag_get_zero_none :=
  SchemaLang.VExpr.eq (SchemaLang.VExpr.lit 0) (SchemaLang.VExpr.lit 0)

/-! ## The updates (the batch semantics — the tick's cascade input) -/

-- The rollout's CLAMP: any row over 100 lands at exactly 100 (the
-- reads-the-original-row discipline: the value expr reads the ORIGINAL
-- rollout; the guard refuses the in-range rows).
schema_update rolloutClamp for Flag rollout :=
  SchemaLang.VExpr.lit 100 where SchemaLang.VExpr.gt (SchemaLang.VExpr.colOf "rollout") (SchemaLang.VExpr.lit 100)

-- The key's self-echo (the SELF-READING update — the nonlinear row:
-- the journal carries S0 exactly here).
schema_update keyEcho for Flag key :=
  SchemaLang.VExpr.colOf "key" where SchemaLang.VExpr.gt (SchemaLang.VExpr.strlen (SchemaLang.VExpr.colOf "key")) (SchemaLang.VExpr.lit 0)

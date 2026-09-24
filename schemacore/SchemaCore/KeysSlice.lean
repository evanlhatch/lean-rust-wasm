/-
# SchemaCore.KeysSlice — the keys lane's registered fixture

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).

The keys lane's end-to-end fixture: the `@[key]` entries append to
`keysExt` at elaboration (the default builder — a `def` of the item
type, the value evaluated at elaboration); the replay/WF teeth are
`#eval` pins (a drift FAILS the build); the curated failures are the
`#guard_msgs` negative controls. A module's own initializers do not run
during ITS OWN elaboration, so the mount (SchemaCore.Keys) and the
entries (this module) are different modules — the KitTests LaneReg →
LaneDemo discipline.

The fixture: the slice's Example record keyed by `label` (a scalar —
the `keyOfTy` gate admits string). The FK positive case CANNOT live on
the registered universe (ExampleEx has no scalar field to host a key —
the slice's honest shape), so the cascade's foreign rungs are exercised
in SchemaTests over hand-built universes; the LIVE teeth here pin the
replay, the WF against the LIVE registry, and the determinacy content
(`uniqueOn` over the default-singleton table).

Provenance: fresh (the fixture IS the lane's first consumer; no legacy
content). The runtime suite's value-level tests ride these same defs
(SchemaTests' keysSpec) — registration is this file, the tests consume
the exported values.

The five questions: root = the keys lane's fixture content; carrier =
the KeyDecl rows over the Example item; spine reading = the event log's
entries; ladder rung = the teeth are `#eval`/`#guard_msgs`
(elaboration-time); gate row = SchemaTests' keysSpec + the axiom
report.

Core-only.
-/

import SchemaCore.CheckSlice
import SchemaCore.Keys

open SchemaCore

/-! ## The registered key declaration -/

/-- The Example record's declared primary key: `label` (the string
    scalar — the WIT-facing identity; the fields snapshot is the SAME
    list the check lane's fixtures carry, and the teeth below tie it to
    the LIVE registry). -/
@[key]
def exampleKey : KeyDecl :=
  { record := "Example"
    fields := exampleCheckFields
    key := "label"
    foreign := [] }

/-! ## The build-time teeth (the registration + the WF + the determinacy) -/

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  -- the replay: one entry, the record name as the registry key
  let decls := getKeys env
  unless decls.length == 1 && decls[0]!.record == "Example" do
    throwError s!"keys lane replay drifted: {decls.map (·.record)}"
  -- the fold hook: the registry materializes (nodup decided)
  match keyRegistry env with
  | .error e => throwError s!"keys lane fold drifted: {e}"
  | .ok reg =>
      unless reg.items.length == 1 do
        throwError "keys lane registry drifted: wrong item count"
  -- the WF teeth: the declaration checks against the LIVE universe
  -- (the record resolves; the fields snapshot is NOT stale; the key
  -- field is on the record and scalar)
  let items := schemaExt.getState env
  unless (keyDeclsCheck items decls).isEmpty do
    throwError s!"keys lane WF drifted: {keyDeclsCheck items decls}"
  -- the determinacy tooth: uniqueOn holds over the default-singleton
  -- table (the one table materializable from the declaration alone)
  match exampleKey.defaultTable? with
  | none => throwError "keys lane determinacy drifted: no default table"
  | some table =>
      unless exampleKey.uniqueOn table do
        throwError "keys lane determinacy drifted: uniqueOn failed"
  -- the obligation view: the tier computes decidableNow (the claim
  -- index needs no table for the tier's read — `[]` names the type)
  unless decls.all (fun d => (d.uniqueObligation []).tier == .decidableNow) do
    throwError "keys lane obligation tier drifted"

/- NEGATIVE CONTROL: a duplicate record declaration is the closed-world
    refusal (Kit.Diag — got + the taken names + the ONE engine's
    did-you-mean). -/
/-- error: [KL0001] error: @[key] dupKey: `Example` is already a registered item — names must be fresh (got: Example) — valid: Example — did you mean: Example? -/
#guard_msgs in
@[key] def dupKey : KeyDecl :=
  { record := "Example"
    fields := exampleCheckFields
    key := "count"
    foreign := [] }

/- NEGATIVE CONTROL: the entry must be a `def` of the lane's item
    type — the curated usage message (KL0003). -/
/-- error: [KL0003] error: @[key] wrongKey: the entry's type is not the lane's item type `SchemaCore.KeyDecl` — valid usage: `@[key] def wrongKey : SchemaCore.KeyDecl := <value>` -/
#guard_msgs in
@[key] def wrongKey : Nat := 5

/- # SchemaCore.Register — `@[schema]`: the registration

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/15-patterns.md #7 (the env extension as the
compile-time event log: registration = append, replay = the
materialization); notes/v3/12-construction.md §1 (the authoring surface
is PLAIN Lean declarations — the attribute reflects them, the author
never writes `Ty` or `Item` by hand).

The registration is MOUNTED on the lane substrate (Kit.Lane's
`register_lane` — 12 §2's steps 1–2 mechanized into one kit call):

- the extension: substrate-generated (`schemaExt`, append-only,
  addImportedFn-concatenates the imported arrays);
- the attribute: substrate-generated (`@[schema]`, the `attr` clause
  keeps the slice's authoring surface byte-stable); the custom
  `builder` clause CONSUMES the description layer (the CONVERGED
  reflection — SchemaCore.Describe's `reflectItemViaDescr`: describe
  → Descr → item, ONE reflection path, 05 §3); `reflectStruct` below
  is that route's `Except String` adapter over the lane substrate's
  builder contract. The substrate's DEFAULT builder (a `def` of the
  item type, the value evaluated at elaboration) is the lane shape
  KitTests.LaneReg exercises end-to-end; `naming` is the registry's
  lookup key (the item's Lean name);
- the replay/fold faces: `getSchemaItems` + `schemaRegistry` (the
  substrate's generated accessors; the fold hook materializes the
  replay into a `Kit.DataRegistry`).

The duplicate-name refusal is the substrate's closed-world Diag
(got + the taken names + the ONE engine's did-you-mean — was a bare
contains-check).

Provenance: mined from
`legacy/lean/schema-lang/SchemaLang/Meta/Register/Schema.lean` +
`Provenance.lean` (`checkStruct`/`tyOfExpr?`/`ctorArgTypes` — the
theorem-free reflection content, re-shaped) and
`legacy/lean/codegen-core/CodegenCore/Registry.lean` (`mkRegistryExt`'s
semantics — now living in Kit.Lane). Deliberately OUT: variants/funcs/
resources (one shape per the slice), key registration, named-type
references (the reifier's registry lookup — no second `@[schema]` decl
depends on it yet).

Core-only except the builder adapter (a `meta def` — it cites the
elaboration-time reflection route; the mount's generated
`unsafe initialize` is the substrate's).

The five questions (notes/v3/01-core.md):
- root: META — the authoring surface (elab-time reflection); the lane
  substrate (Kit.Lane) mechanizes steps 1–2.
- carrier grade: none of its own — the generated entries are
  first-order `Item`s; the duplicate refusal is closed-world Diag.
- spine reading: the REGISTRY stage's write side — registration =
  append; replay = the substrate's accessors.
- ladder rung: rung 1 — the discipline lives in the shapes
  (append-only ext, decided nodup, did-you-mean refusal).
- gate row: the axiom report (SchemaCore roots) + gen-check (the
  replayed registration is the byte-tie's writer side).
-/

import Lean
import SchemaCore.Ty
import SchemaCore.Item
import SchemaCore.Describe

namespace SchemaCore

/-! ## The builder — the description route's mount face -/

/-- The `@[schema]` builder: the CONVERGED reflection route
    (`Describe.reflectItemViaDescr` — describe → Descr → item, 05 §3),
    with its curated `Kit.Diag` flattened to the lane substrate's
    `Except String` contract (`Kit.Lane.wrapBuilder`) — the ONE
    toString at the ONE boundary; the refusals themselves stay Diag
    end-to-end (05 §4). The name is the pre-convergence direct
    walker's, which SchemaTests.Main's twin-path pin still cites;
    when that pin collapses to the single route, the builder cites
    `reflectItemViaDescr` directly and this is the adapter alone. -/
meta def reflectStruct (env : Lean.Environment) (declName : Lean.Name) :
    Except String Item :=
  (reflectItemViaDescr env declName).mapError (·.toString)

/-! ## The mount — `@[schema]`, by `Kit.Lane.register_lane` -/

/- The registry, mounted by `Kit.Lane.register_lane` (the lane
    recipe's steps 1–2 in one kit call). The custom `builder` clause is
    the structure-reflection route (12 §1: the authoring surface is
    the plain structure declaration — `reflectStruct` runs the
    description route (`Describe.reflectItemViaDescr`) through the
    substrate's `Except String` contract); the
    substrate's DEFAULT builder (a `def` of the item type, the value
    evaluated at elaboration) is the lane shape — KitTests.LaneReg
    exercises it end-to-end. `naming` is the registry's lookup key.
    Generates: `schemaExt` (the append-only compile-time event log),
    `@[schema]`, `getSchemaItems` (the replay accessor),
    `schemaRegistry` (the fold hook — the replay materialized into a
    `Kit.DataRegistry`), `schemaNameOf`, `schemaAttrReg` (the
    attribute's initializer). -/
register_lane Item where
  attr := schema
  naming := fun it => it.name
  builder := reflectStruct

end SchemaCore

/-! ## The description-layer interop (D19 — the convergence, EXECUTED)

The twin reflection path this file once carried — `reflectStruct`'s
direct ctor/arity walk over `tyOfExpr?`, with its bare-String
refusals — is DELETED. The ONE reflection path is
`SchemaCore.Describe` (the typed description universe — 05 §3's "ONE
deliberate meta-universe"), and the reifier family
(`natLitOf?` / `keyOfExpr?` / `tyOfExpr?` / `ctorArgTypes`) lives
there too: one module, one expr walk, the import running Register →
Describe. This mount CONSUMES that route (`builder := reflectStruct`
— the `Except String` adapter over `Describe.reflectItemViaDescr`).
The description's coherence laws (`tyOfDescr_denotes`,
`deriveRender_coherent`, factored as `tyOfDescr_some`) say the
description layer is not a parallel renderer; the paths' agreement on
the slice's fixture is pinned live in SchemaTests (build-time teeth).
-/

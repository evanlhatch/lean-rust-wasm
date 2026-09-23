/-
# SchemaLang.Meta.RegisterKit — `declare_registry_member`: the registry trinity as ONE command

OWNERSHIP: schema-lang owns this file. The S5 meta-toolkit — the
concept: command + registry + obligation is ONE shape. The 8
`schema_*`/`declare_*` commands each hand-roll the same reusable
skeleton:

  (1) the env-extension snapshot replay — `initialize <ext> :
      SimplePersistentEnvExtension (Name × <kind>) (List (Name × <kind>))
      ← CodegenCore.mkRegistryExt `…` PLUS the `registered*` reader,
      the exact `Meta.Register.Core` shape (append on add,
      concatenate on import — the `mkRegistryExt` semantics, replayed
      from oleans at import);
  (2) the registered-name space and its did-you-mean (GenKit's
      `freshNameCheck` is the ONE tree-wide rejection — enumerated
      space + suffix);
  (3) the attribute registration — the `register_check_attribute`
      shape (AttrKit's `registerBuiltinAttribute`
      `.afterCompilation` block);
  (4) the provenance hookup — `Register.ProvenanceDocs.
      registerSchemaItemDoc` (the declaring constant's doc string).

LAYERING (the Core cycle): the kit's lower cone is Core-free. The
doc-string registry lives in `Register.ProvenanceDocs` (Lean +
CodegenCore only) — NOT in `Register.Provenance` (which imports
`Register.Core`, and Core imports this kit — the import graph would
cycle). The emitted mount's hookup references the docs split's
`registerSchemaItemDoc`; consumers of the mount bring it into scope
via `SchemaLang.Meta.Reflect` (every consumer does).

`declare_registry_member` EMITS that skeleton at the point of use via
`GenKit.elabGenerated`'s route (source text → parse → elabCommand) —
the author never pastes the four pieces again. Generated names ARE
the explicit arguments — nothing is derived, nothing to guess (the
codebase's per-registry conventions — `registeredItems`,
`registeredTemplates`, `registeredKeys` — cannot be recovered from a
stem, so the author spells them). The extension is registered under
its identifier's own name (Register.Core's convention:
`schemaItemExt` → `` `schemaItemExt ``).

## Usage template (the three forms)

    declare_registry_member <ext> <reader> : <kind>
    declare_registry_member <ext> <reader> : <kind> plain!
    declare_registry_member <ext> <reader> : <kind>
      with <attr> := <builder> name: := <itemName>

- Form (i) — the registry only: the extension + the reader. This is
  the skeleton a real command hands to its own elaborator (the
  `schema_template` pattern). Consumer: `Templates.lean`'s
  `templateExt`/`registeredTemplates` (the migrated real command).
- Form (i) `plain!` — the PLAIN-ROWS mode: the kind IS the row, no
  declaring-name key in front of it. The default pair `(Name × <kind>)`
  carries the registering Lean name; registries whose ITEMS carry their
  own wire name are plain — `InvariantItem`/`SomeUpdate2` (the
  `schema_invariant`/`schema_update` lanes, the migrated real commands;
  their readers replay as `List InvariantItem`/`List SomeUpdate2`, and
  their elaborators register THE ITEM through `addEntry`, the item's
  OWN `name` field being the registry key).
  DELIBERATE EXCLUSION (v1): `plain!` cannot combine with the mount
  (`with …`) — the emitted mount's `name:` projection and `addEntry`
  argument are PAIR-shaped; no plain-row mount consumer exists, and
  pair-shaped emission over plain rows would be garbage, so the
  combination is REFUSED loudly (the negative control below pins the
  message). A later mount for a plain registry needs a mount
  parameterization (the name projection over the item, the item-only
  write) — the seam, not today's work.
- Form (ii) — the trinity: form (i) plus the emitted `@[<attr>]` mount
  whose handler runs the GenKit fresh-name obligation over the
  reader's registered item names, builds the item via `<builder>` (a
  `Name → CoreM <kind>` term — the KIND-SPECIFIC reflection, the one
  part of the skeleton that stays with the author), registers it into
  `<ext>`, and hooks up provenance. `<itemName>` is the name
  projection (`<kind> → String`): the obligation checks the ITEM's
  wire name, not the declaring constant's (two declarations can carry
  the same wire name — the `schema_from_template` collision class).
  The mount fits the self-contained attribute commands — the pair
  (`declaring name, item`) rows it emits cover authoring attrs
  (`@[schema]`-class). The richer command attrs whose registration
  needs the raw declaration syntax or a SECOND registry write are NOT
  expressible today — the `@[schema key.<field>]` seam (`Register
  .Schema`, documented there): their builders need the attribute
  syntax (a stx-threaded builder) and a post-registration hook for
  the secondary `keysExt` write.

Deliberate exclusions (v1, anti-museum): no writer def is emitted for
form (i) (the consumer's command IS the write path — `schema_template`
writes `templateExt` directly); `plain!` refuses the mount (the plain
lanes' elaborators ARE the write path); no load-bearing role for `Attr`
beyond the mount (the 8 commands' command-specific SYNTAX stays
command-specific — the toolkit does not generate grammar); no
syntax-category machinery.

## The same-module rule (why the self-test registers nothing in-file)

A `SimplePersistentEnvExtension` initialized with `initialize` is only
READABLE from a DIFFERENT module than its own (evaluating the `[init]`
handle in the same module is refused — the `schemaItemExt`/`templateExt`
precedent: the machinery registers in schema-lang/feature-flags, the
registrations arrive from Demo/Tests). So the kit's own member below
emits its registry IN THIS MODULE and proves the surface by
type-checks + the duplicate-member negative control; the REGISTRATION
round-trips are the consumer's job — proven end-to-end by the
`Templates.lean` migration (its registrations live in
`FeatureFlagsTests`, exactly like `templateExt` today) and by the
existing `@[schema]`/`schema_from_template` gates.

The self-test below (the first consumer): a registry-only member
(`footprintExt`/`registeredFootprints`) + the exact command-shaped
consumer code (`register_footprint`) + the duplicate-member negative
control, a trinity member (`tagExt`/`registeredTags` + the emitted
`@[tag]` mount) proving the full emission elaborates, and the
plain-rows member (`plainExt`/`registeredPlains` + `register_plain` —
the invariant/update lanes' shape) with ITS negative controls.
-/
module

public import Lean
public import CodegenCore
public meta import SchemaLang.Meta.Register.ProvenanceDocs

public meta section

namespace SchemaLang.Meta

open Lean Elab Command Term

/-! ## The command -/

/-- `declare_registry_member` — the registry-trinity emitter (see the
    module header for the three forms and the usage template). All
    forms emit the extension + the reader; `plain!` selects the
    plain-rows mode (the kind IS the row — the item's own name field
    is the registry key, the invariant/update lanes' shape); the
    `with <attr> := <builder> name: := <itemName>` form additionally
    emits the `@[<attr>]` registration mount (the GenKit fresh-name
    obligation, the registration, the provenance hookup) — and
    refuses `plain!` (the mount's name projection and write are
    pair-shaped; see the module header for the seam). The generated
    code is elaborated in the caller's namespace — all non-local
    names in it are fully qualified (the EntityMachine rule). -/
syntax (name := SchemaLang.Meta.declareRegistryMember)
  "declare_registry_member " ident ident " : " term
    (" plain!")?
    (" with " ident " := " term "name:" " := " term)? : command

/-- The elaborator. -/
@[command_elab SchemaLang.Meta.declareRegistryMember]
unsafe def elabDeclareRegistryMember : CommandElab := fun stx => do
  let rowGroup := stx[5]
  let optGroup := stx[6]
  let isPlain := !rowGroup.isNone
  let isMount := !optGroup.isNone
  let extStx := stx[1]!
  let readerStx := stx[2]!
  let kindStx := stx[4]!
  let extName := extStx.getId
  let kindSrc : String := kindStx.reprint.getD ""
  -- THE PLAIN-MOUNT REFUSAL (v1 anti-museum, before any emission — the
  -- negative control pins this message): the emitted mount's `name:`
  -- projection and `addEntry` argument are PAIR-shaped (`Name ×
  -- <kind>`); `plain!` lanes register through their OWN elaborators (the
  -- invariant/update pattern), so the combination would emit
  -- pair-shaped garbage over plain rows — refused loudly instead.
  if isPlain && isMount then
    throwError "declare_registry_member: `plain!` (plain rows — the kind IS the row) cannot combine with the mount (`with …`): the mount emits the `Name × <kind>` pair and its `name:` projection is pair-shaped (v1 — the plain lanes, invariants/updates, register through their own elaborators)"
  -- THE DUPLICATE-MEMBER GATE (before any emission): the generated
  -- `initialize` declares a constant named after the ext ident (in the
  -- invoking namespace) — a second registry member on the same name is
  -- refused HERE, so the failure is ONE clean error and no partially
  -- emitted reader pollutes the environment (elaboration would
  -- otherwise continue past the logged decl-name error).
  let ns ← getCurrNamespace
  if (← getEnv).contains (ns ++ extName) then
    throwError s!"`{ns ++ extName}` has already been declared"
  -- one generated-source emission (the `GenKit.elabGenerated` route:
  -- source text → parse → elabCommand)
  let emit (src : String) : CommandElabM Unit := do
    match Lean.Parser.runParserCategory (← getEnv) `command src with
    | .ok stx' => elabCommand stx'
    | .error e =>
        throwError s!"declare_registry_member: generated source failed to parse\n{e}"
  -- the row type: `plain!` → the kind VERBATIM (plain rows — the item IS
  -- the row, its own `name` field the registry key); default → the
  -- `Name × <kind>` pair (the registering Lean name + the item)
  let rowSrc : String := if isPlain then kindSrc else s!"(Lean.Name × {kindSrc})"
  -- (1) the env-extension snapshot replay (Register.Core's shape)
  emit s!"initialize {extName} : Lean.SimplePersistentEnvExtension {rowSrc} (List {rowSrc}) ←\n  CodegenCore.mkRegistryExt `{extName}"
  -- the reader (`registered*` per convention, the explicit argument)
  emit s!"def {readerStx.getId} (env : Lean.Environment) : List {rowSrc} :=\n  ({extName}).getState env"
  if isMount then
    let attrName := optGroup[1]!.getId
    let builderSrc := optGroup[3]!.reprint.getD ""
    let nameOfSrc := optGroup[6]!.reprint.getD ""
    let ctx := s!"@[{attrName}]"
    let descr := s!"register a {kindSrc} into `{extName}` — the declare_registry_member toolkit's emitted surface"
    -- (3)+(2)+(1)+(4): the mount — the `register_check_attribute`
    -- shape with the obligation, the registration, the provenance
    emit s!"register_check_attribute `{attrName} : \"{descr}\" := fun decl _stx _kind => do\n  let env ← Lean.getEnv\n  let item ← ({builderSrc}) decl\n  CodegenCore.freshNameCheck \"{ctx}\" ({nameOfSrc} item) \"{kindSrc}\"\n    (({readerStx.getId} env).map (fun (_, it) => {nameOfSrc} it))\n  Lean.modifyEnv fun env => ({extName}).addEntry env (decl, item)\n  SchemaLang.Meta.registerSchemaItemDoc decl"

/-! ## Self-test — the first consumer (registry-only form)

The member: a tiny named-metric item kind. The emitted ext + reader
land HERE (type-checked below); registration round-trips are
cross-module (the same-module rule in the module header) — the
consumer-shaped code (`register_footprint`) is compiled against the
emitted reader so the API contract (GenKit obligation + `addEntry`
write path) is build-checked. -/

/-- The demo item kind for the self-test: a named metric. -/
structure FootprintItem where
  name : String
  size : Nat
deriving Repr, BEq, Inhabited

declare_registry_member footprintExt registeredFootprints : FootprintItem

#check footprintExt
#check registeredFootprints

/-- THE consumer-shaped code: a command registering one footprint
    through the EMITTED reader + the GenKit obligation (the
    `schema_template` pattern — the write path is the command). -/
syntax (name := SchemaLang.Meta.registerFootprintCmd)
  "register_footprint " ident : command

@[command_elab SchemaLang.Meta.registerFootprintCmd]
unsafe def elabRegisterFootprint : CommandElab := fun stx => do
  let nm := stx[1]!.getId
  let ctx := s!"register_footprint {nm}"
  let env ← getEnv
  -- (2) the obligation (GenKit): duplicate names are refused
  CodegenCore.freshNameCheck ctx nm.toString "footprint"
    ((registeredFootprints env).map (fun (ln, _) => ln.toString))
  -- the registration: the append-on-add write path
  modifyEnv fun env => footprintExt.addEntry env
    (nm, { name := nm.toString, size := 1 })

/-! ## Self-test — the plain-rows mode (`plain!`, registry-only)

The member: the SAME named-metric item kind WITHOUT the declaring-name
key — the invariant/update lanes' shape (`InvariantItem`/`SomeUpdate2`
carry their own `name` field; the `Name × <kind>` pair would be
redundant). The emitted ext + reader land here (type-checked below);
the consumer-shaped code (`register_plain`) registers the ITEM
directly through the emitted ext — the `schema_invariant` write-path
pattern (the item's own name is the registry key). -/

declare_registry_member plainExt registeredPlains : FootprintItem plain!

#check plainExt
#check registeredPlains

/-- THE consumer-shaped code for a plain registry: the registration
    passes the ITEM — no `Name` pair — the item's own `name` field is
    the registry key (the `schema_invariant` write-path pattern). -/
syntax (name := SchemaLang.Meta.registerPlainCmd)
  "register_plain " ident : command

@[command_elab SchemaLang.Meta.registerPlainCmd]
unsafe def elabRegisterPlain : CommandElab := fun stx => do
  let nm := stx[1]!.getId
  let ctx := s!"register_plain {nm}"
  let env ← getEnv
  -- (2) the obligation (GenKit): duplicate names are refused (plain
  -- rows: the name projection is the ITEM's OWN name field)
  CodegenCore.freshNameCheck ctx nm.toString "footprint"
    ((registeredPlains env).map (·.name))
  -- the registration: the append-on-add write path, item-only
  modifyEnv fun env => plainExt.addEntry env
    { name := nm.toString, size := 1 }

/-! ## Self-test — the trinity form (attribute mount)

The member's full emission (ext + reader + the `@[tag]` mount) lands
here; the mount is usable by OTHER modules only (the same-module rule
— the `@[schema]` precedent: the Register modules register, the Demo
modules apply). -/

/-- The demo item kind for the trinity self-test. -/
structure TagItem where
  name : String
deriving Repr, BEq, Inhabited

declare_registry_member tagExt registeredTags
  : TagItem with tag := fun decl => pure { name := "wire" } name: := TagItem.name

#check tagExt
#check registeredTags

/-! ## Self-test — the negative controls -/

-- The duplicate-member refusal: a SECOND emission of the same
-- extension name fails at elaboration (`footprintExt` above) — the
-- toolkit's duplicate-member gate fires BEFORE any emission (one
-- clean error, no partially-emitted reader pollutes the
-- environment — the decl-name clash would otherwise be a LOGGED-only
-- error and elaboration would continue past it). The negative
-- control proves the toolkit's generated code is REAL: a duplicate
-- registry member is loudly refused, never silently shadowed.
/-- error: `SchemaLang.Meta.footprintExt` has already been declared -/
#guard_msgs in
declare_registry_member footprintExt registeredFootprintsDup : TagItem

-- The SAME gate fires on plain members (`plainExt` above) — the
-- plain-rows mode is the same emission path, not a separate command.
/-- error: `SchemaLang.Meta.plainExt` has already been declared -/
#guard_msgs in
declare_registry_member plainExt registeredPlainsDup : FootprintItem plain!

-- The plain-mount REFUSAL: `plain!` + `with …` is an elaboration error.
-- The toolkit refuses to emit pair-shaped mount code over plain rows
-- (v1 anti-museum — the seam in the module header): a plain registry's
-- mount would need the item-shaped name projection and the item-only
-- write, and no plain-lane mount consumer exists today (the invariant
-- and update lanes register through their own elaborators).
/-- error: declare_registry_member: `plain!` (plain rows — the kind IS the row) cannot combine with the mount (`with …`): the mount emits the `Name × <kind>` pair and its `name:` projection is pair-shaped (v1 — the plain lanes, invariants/updates, register through their own elaborators) -/
#guard_msgs in
declare_registry_member rowTagExt registeredRowTags : TagItem plain!
  with tag := fun decl => pure { name := "wire" } name: := TagItem.name

end SchemaLang.Meta

end -- public meta section

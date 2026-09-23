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
  (4) the provenance hookup — `Register.Provenance.
      registerSchemaItemDoc` (the declaring constant's doc string).

`declare_registry_member` EMITS that skeleton at the point of use via
`GenKit.elabGenerated`'s route (source text → parse → elabCommand) —
the author never pastes the four pieces again. Generated names ARE
the explicit arguments — nothing is derived, nothing to guess (the
codebase's per-registry conventions — `registeredItems`,
`registeredTemplates`, `registeredKeys` — cannot be recovered from a
stem, so the author spells them). The extension is registered under
its identifier's own name (Register.Core's convention:
`schemaItemExt` → `` `schemaItemExt ``).

## Usage template (the two forms)

    declare_registry_member <ext> <reader> : <kind>
    declare_registry_member <ext> <reader> : <kind>
      with <attr> := <builder> name: := <itemName>

- Form (i) — the registry only: the extension + the reader. This is
  the skeleton a real command hands to its own elaborator (the
  `schema_template` pattern). Consumer: `Templates.lean`'s
  `templateExt`/`registeredTemplates` (the migrated real command).
- Form (ii) — the trinity: form (i) plus the emitted `@[<attr>]`
  mount whose handler runs the GenKit fresh-name obligation over the
  reader's registered item names, builds the item via `<builder>` (a
  `Name → CoreM <kind>` term — the KIND-SPECIFIC reflection, the one
  part of the skeleton that stays with the author), registers it into
  `<ext>`, and hooks up provenance. `<itemName>` is the name
  projection (`<kind> → String`): the obligation checks the ITEM's
  wire name, not the declaring constant's (two declarations can carry
  the same wire name — the `schema_from_template` collision class).

Deliberate exclusions (v1, anti-museum): no writer def is emitted for
form (i) (the consumer's command IS the write path — `schema_template`
writes `templateExt` directly); no load-bearing role for `Attr` beyond
the mount (the 8 commands' command-specific SYNTAX stays
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
control, and a trinity member (`tagExt`/`registeredTags` + the emitted
`@[tag]` mount) proving the full emission elaborates.
-/
module

public import Lean
public import CodegenCore
public meta import SchemaLang.Meta.Register.Provenance

public meta section

namespace SchemaLang.Meta

open Lean Elab Command Term

/-! ## The command -/

/-- `declare_registry_member` — the registry-trinity emitter (see the
    module header for the two forms and the usage template). Both
    forms emit the extension + the reader; the `with <attr> :=
    <builder> name: := <itemName>` form additionally emits the
    `@[<attr>]` registration mount (the GenKit fresh-name obligation,
    the registration, the provenance hookup). The generated code is
    elaborated in the caller's namespace — all non-local names in it
    are fully qualified (the EntityMachine rule). -/
syntax (name := SchemaLang.Meta.declareRegistryMember)
  "declare_registry_member " ident ident " : " term
    (" with " ident " := " term "name:" " := " term)? : command

/-- The elaborator. -/
@[command_elab SchemaLang.Meta.declareRegistryMember]
unsafe def elabDeclareRegistryMember : CommandElab := fun stx => do
  let optGroup := stx[5]
  let isMount := !optGroup.isNone
  let extStx := stx[1]!
  let readerStx := stx[2]!
  let kindStx := stx[4]!
  let extName := extStx.getId
  let kindSrc : String := kindStx.reprint.getD ""
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
  -- (1) the env-extension snapshot replay (Register.Core's shape)
  emit s!"initialize {extName} : Lean.SimplePersistentEnvExtension (Lean.Name × {kindSrc}) (List (Lean.Name × {kindSrc})) ←\n  CodegenCore.mkRegistryExt `{extName}"
  -- the reader (`registered*` per convention, the explicit argument)
  emit s!"def {readerStx.getId} (env : Lean.Environment) : List (Lean.Name × {kindSrc}) :=\n  ({extName}).getState env"
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

/-! ## Self-test — the negative control -/

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

end SchemaLang.Meta

end -- public meta section

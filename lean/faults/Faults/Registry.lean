/-
# Faults.Registry — the failure-mode registry (the one code allocator)

Lifted from flatland's `Codegen.Registry.FailureModeItem` and COMPLETED:
flatland's registry had no emitter (the fast-observe integration was
designed in TOOLKIT §11.1, never built). This package is that emitter.
The ITEM SHAPE + its pure helpers + the kernel-checked obligation
theorems live in `Faults.Item` (the phase split — see that module's
header); this module is the META machinery: the env extensions, the
attribute registrations, the snapshot derive, and the fold.

Registration (W7.4): specs are per-item attribute registrations —
`@[fault]` (guest) / `@[host_fault]` (host) on a `FailureModeItem` def —
not hand list literals. Each attribute has its own env extension (the
`mkRegistryExt` semantics: append on add, concatenate on import); the
extension split IS the guest/host code-space split. `derive_fault_registry`
snapshots an extension into a `CodedRegistry` def at elaboration — the
hand list mirror is gone.

MODULE + the variant-projection fold (W10.1 — the one-fault
unification): this file is a `module` now — the fold's consumer
(`Demo.lean`, the schema authoring surface) is itself a module, and
the module system refuses `module ← non-module` imports. The plain-
file importers consumed the plain file's transitive visibility, so the
imports stay `public` (plus the `public meta import`s the phase rule
demands for the meta surface), and the data decls stay exposed.
-/

module

-- NOTE (W10.1): the import cone stops at the schema-lang SUBMODULES +
-- the Meta chain — never the `SchemaLang` root, whose cone reaches
-- back to `Demo` (`SchemaLang.Emit.Witness` reads the demo witness
-- registry); Demo imports this module (the fold's elaboration-order
-- constraint), and the cycle would be a build error.
public import Lean
public import CodegenCore
public import CodegenCore.CodedRegistry
public import SchemaLang.Item
public import SchemaLang.Meta.Derive
public import Faults.Category
public import Faults.Item
public meta import Faults.Category
public meta import Faults.Item

namespace Faults

open Lean Elab Command
open SchemaLang (Ty)

public meta section

/-! ## The elab-time machinery (meta — the phase check's boundary: the
schema registry's `Meta` walkers are meta, and the env extensions
follow the `declare_registry_member` pattern — meta-initialized, meta-
consumed). -/

/-! ## Attribute registration (W7.4)

One extension per spec source (`CodegenCore.Registry`'s one-extension-
per-item-kind rule): `@[fault]` registers into the GUEST extension,
`@[host_fault]` into the HOST extension. The handler evaluates the
COMPILED value (`applicationTime := .afterCompilation`, so the code
exists) and rejects a duplicate failure-mode name at elaboration —
cross-module duplicates fail when the second module elaborates, because
the extension replays imports. -/

/-- The guest failure-mode registry: Lean declaration name ↦ item,
    append-only. -/
initialize guestFaultExt :
    SimplePersistentEnvExtension (Name × FailureModeItem) (List (Name × FailureModeItem)) ←
  CodegenCore.mkRegistryExt `guestFaultExt

/-- The host failure-mode registry (steel-host capability/engine
    faults — the second spec source). -/
initialize hostFaultExt :
    SimplePersistentEnvExtension (Name × FailureModeItem) (List (Name × FailureModeItem)) ←
  CodegenCore.mkRegistryExt `hostFaultExt

/-- Register one compiled `FailureModeItem` def into `ext`. The value is
    evaluated from the compiled constant; a name already present is an
    elaboration error — the registry rejects, there is no overwrite
    path. -/
unsafe def registerFaultItem
    (ext : SimplePersistentEnvExtension (Name × FailureModeItem) (List (Name × FailureModeItem)))
    (attr : Name) (decl : Name) : CoreM Unit := do
  let item ← evalConst FailureModeItem decl
  -- The category-drift gate: `.unsupported` has no fast-observe rendering
  -- (fast-observe's `ErrorCategory` is Content/Invariant/Transient/Fatal and
  -- its `Policy` has no degrade action), so a spec carrying it would reach
  -- rustc as `ErrorCategory::Unsupported` and fail the CONSUMER'S build —
  -- rejected here, at registration, where the spec author is looking.
  -- Mapping it to an expressible category is a deliberate decision
  -- (see Faults.Category), not emitter sleight of hand.
  if item.category == Category.unsupported then
    throwError
      s!"`{attr}`: failure-mode `{item.name}` has category `.unsupported` — \
         fast-observe's `ErrorCategory` has no Unsupported variant (and no \
         degrade `Policy`), so this cannot be emitted; the spec would fail \
         rustc in the consumer. Pick an expressible category, or first map \
         `.unsupported` in `Category.rustName` (see Faults.Category's header)."
  if let some (other, _) :=
      (ext.getState (← getEnv)).find? (fun (_, it) => it.name == item.name) then
    throwError
      s!"`{attr}`: failure-mode name `{item.name}` already registered at `{other}` \
         — names must be unique"
  modifyEnv fun env => ext.addEntry env (decl, item)

unsafe initialize registerBuiltinAttribute {
    name := `fault
    descr := "register a `FailureModeItem` def into the guest failure-mode registry"
    applicationTime := .afterCompilation
    add := fun decl _stx _kind => registerFaultItem guestFaultExt `fault decl
  }

unsafe initialize registerBuiltinAttribute {
    name := `host_fault
    descr := "register a `FailureModeItem` def into the host failure-mode registry"
    applicationTime := .afterCompilation
    add := fun decl _stx _kind => registerFaultItem hostFaultExt `host_fault decl
  }

/-- The registered guest items from an environment (emitter entry). -/
def registeredGuestFaults (env : Environment) : List (Name × FailureModeItem) :=
  guestFaultExt.getState env

/-- The registered host items from an environment (emitter entry). -/
def registeredHostFaults (env : Environment) : List (Name × FailureModeItem) :=
  hostFaultExt.getState env

/-! ## The spec snapshot command

`derive_fault_registry name` / `derive_fault_registry name host` —
snapshot the attribute-populated extension into a
`CodegenCore.CodedRegistry FailureModeItem` def at elaboration (the
`derive_schema_type_names` discipline: not a hand mirror — editing the
per-item registrations re-derives the registry). Codes: prefix `"E"`;
start 100 for the guest registry, `100 + guest count` for the host
registry — DERIVED from the replayed guest extension, never a hand-set
fiat (the old hardcoded host start silently collided the moment guests
grew past it). Name uniqueness and code collision-freedom discharge by
`decide` over the concrete snapshot. -/

/-- A `FailureModeItem` value → its literal term (payload types via
    `SchemaLang.Meta.tyTerm` — the one `Ty` reifier). -/
def faultItemTerm (m : FailureModeItem) : CommandElabM Term := do
  let payloadTerms : Array Term ← m.payload.toArray.mapM fun (n, t) => do
    `(($(quote n), $(← SchemaLang.Meta.tyTerm t)))
  let catTerm : Term ← match m.category with
    | .fatal => `(Category.fatal)
    | .content => `(Category.content)
    | .transient => `(Category.transient)
    | .invariant => `(Category.invariant)
    | .unsupported => `(Category.unsupported)
  let body : Term ←
    `({ name := $(quote m.name), display := $(quote m.display)
      , category := $catTerm, advice := $(quote m.advice)
      , payload := [$payloadTerms,*] })
  `(($body : FailureModeItem))

syntax (name := deriveFaultRegistry)
  "derive_fault_registry " ident (&" host")? : command

@[command_elab deriveFaultRegistry]
def deriveFaultRegistryImpl : CommandElab := fun stx => do
  let target := stx[1].getId
  let isHost := !stx[2].isNone
  let env ← getEnv
  let ext := if isHost then hostFaultExt else guestFaultExt
  let items := (ext.getState env).map (·.2)
  let start := if isHost then 100 + (guestFaultExt.getState env).length else 100
  let itemTerms : Array Term ← items.toArray.mapM faultItemTerm
  elabCommand (← `(def $(mkIdent target) : CodegenCore.CodedRegistry FailureModeItem :=
    { items := [$itemTerms,*], nameOf := (·.name)
    , codePrefix := "E", start := $(quote start) }))

/-! ## The variant-projection fold (W10.1 — the one-fault unification)

The registry IS the wire variant's SSOT (the design doc's §2.2
decision): the guest registry's items fold into a schema
`Item.variant` — one wire case per row, the row's payload the case
payload — registered into the SAME universe the WIT world folds from,
under the carrier type's name. A fault is declared ONCE; the wire
type, the fast-observe enum, the codes, and the doctor entries are
projections of the one row. The hand-paired `@[schema] inductive
OrderError` registration DIES (the duplicate seam), and the
disagreement gate below is the unification's negative control: a
fault row and a registered schema variant disagreeing on a case (name
or payload) fails ELABORATION.

The fold lives HERE (the faults package owns the projection) but is
INVOKED in the schema module — the elaboration-order constraint: the
`@[schema_fn]` reifying the variant reference runs at the SCHEMA
module's elaboration, before this package's spec snapshot replays, so
the rows + the fold must precede it there (`Demo.lean`). The stored
case names are the rows' registry names verbatim — the emitters'
kebab mangling applies downstream, unchanged, so the folded item is
byte-identical to the registration it replaces (the wire variant is
unchanged byte-wise; the `universe.snapshot` baseline holds). -/

/-- One registry row → its wire case: the row's registry name + the
    payload type. WIT variant cases carry at most one payload (v1 —
    the schema lane's case shape); a multi-field payload row is the
    `multiPayload` diagnostic, AT THE FOLD (registration-time
    rejection, the `@[schema]` discipline — not a downstream
    emitter's surprise). -/
def faultCaseOf (m : FailureModeItem) :
    Except String SchemaLang.VariantCase :=
  match m.payload with
  | [] => .ok (m.name, none)
  | [(_, t)] => .ok (m.name, some t)
  | _ :: _ :: _ =>
      .error ((SchemaLang.SchemaDiag.multiPayload m.name).render ++
        s!" — fault row `{m.name}` (the fold's v1 case shape)")

/-- The fold's case list, rendered for the disagreement diagnostic. -/
def renderCases (cs : List SchemaLang.VariantCase) : String :=
  String.intercalate ", " (cs.map fun
    | (c, none) => c
    | (c, some t) => s!"{c}({repr t})")

/-- `derive_fault_variant <carrierName>` — fold the guest registry's
    rows into the schema `Item.variant` named `carrierName`,
    registering it when absent. The gate: a registration under the
    same name must AGREE with the fold (idempotent re-run) — a
    disagreement (a case the registry hasn't got, or a case payload
    the row doesn't carry) fails elaboration. A non-variant squatter
    is a named error too. -/
syntax (name := deriveFaultVariant) "derive_fault_variant " ident : command

@[command_elab deriveFaultVariant]
def deriveFaultVariantImpl : CommandElab := fun stx => do
  let target := stx[1].getId
  let env ← getEnv
  let items := (guestFaultExt.getState env).map (·.2)
  if items.isEmpty then
    throwError s!"derive_fault_variant `{target}`: no `@[fault]` rows \
      registered — the fold has nothing to project"
  match items.foldl (fun acc m => do
      let cs ← acc
      let c ← faultCaseOf m
      .ok (cs ++ [c])) (.ok []) with
  | .error msg => throwError s!"derive_fault_variant `{target}`: {msg}"
  | .ok folded =>
    match SchemaLang.Meta.registeredItem? env target with
    | some (.variant _ existing) =>
        if existing != folded then
          throwError s!"derive_fault_variant `{target}`: the fault registry's \
            fold disagrees with the registered schema variant — the registry is \
            the wire variant's SSOT (one fault concept per failure mode). \
            registry folds to: [{renderCases folded}] | schema has: \
            [{renderCases existing}] — fix the `@[fault]` rows or delete the \
            hand variant"
        -- agreement: the fold is idempotent — the registration stands
    | some it =>
        throwError s!"derive_fault_variant `{target}`: `{it.name}` is already \
          registered as `{repr it}` — not a variant; the fault fold owns \
          this name"
    | none =>
      -- the same registration-time identifier hygiene the `@[schema]`
      -- path applies (a reserved word would emit invalid WIT/Rust)
      for (c, _) in folded do
        for d in SchemaLang.checkSchemaIdent (s!"case of `{target}`") c do
          throwError s!"derive_fault_variant `{target}`: {d.render}"
      liftCoreM (SchemaLang.Meta.registerSchemaItem target
        (.variant target.toString folded))
      liftCoreM (SchemaLang.Meta.registerSchemaItemDoc target)

end -- public meta section
end Faults

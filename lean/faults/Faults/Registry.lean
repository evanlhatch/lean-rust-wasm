/-
# Faults.Registry — the failure-mode registry (the one code allocator)

Lifted from flatland's `Codegen.Registry.FailureModeItem` and COMPLETED:
flatland's registry had no emitter (the fast-observe integration was
designed in TOOLKIT §11.1, never built). This package is that emitter.

Item shape (flatland base + the fields the emission contract requires):
- `name`     — registry identifier, mangled to the Rust variant
- `display`  — the `#[error("…")]` message (may interpolate payload
               fields, fast-observe format syntax)
- `category` — policy axis (see `Faults.Category`)
- `advice`   — the `#[advice]` attribute; the fix, in domain vocabulary
- `payload`  — structured fields, typed by the SCHEMA language's `Ty`
               (schema-lang is the type authority; no second universe)

Codes are NEVER hand-set: they derive from registry position via
`CodegenCore.allocateCodes`, surfaced through `CodedRegistry.codes` —
name uniqueness AND code collision-freedom are proof fields with
`by decide` defaults (W7.4's CodedItem mixin), so an illegal registry
literal fails to ELABORATE; there is no runtime rejection path.

Registration (W7.4): specs are per-item attribute registrations —
`@[fault]` (guest) / `@[host_fault]` (host) on a `FailureModeItem` def —
not hand list literals. Each attribute has its own env extension (the
`mkRegistryExt` semantics: append on add, concatenate on import); the
extension split IS the guest/host code-space split. `derive_fault_registry`
snapshots an extension into a `CodedRegistry` def at elaboration — the
hand list mirror is gone.

wellFormed: payload types resolve against the schema universe's type
names. Name uniqueness is NOT a Bool check — it is in the type.
-/

import Lean
import CodegenCore
import CodegenCore.CodedRegistry
import SchemaLang
import SchemaLang.Meta.Derive
import Faults.Category

namespace Faults

open Lean Elab Command
open SchemaLang (Ty)

/-- A failure mode: spec data. -/
structure FailureModeItem where
  name : String
  display : String
  category : Category
  advice : String
  payload : List (String × Ty)
deriving Repr, BEq, Inhabited

/-- Payload type references resolve against `known` (the schema
    universe's type names; scalars need no universe). Uses the diagnostic
    authority (`Ty.check`) — one resolver, shared with SchemaLang. -/
def FailureModeItem.wellFormed (known : List String) (m : FailureModeItem) : Bool :=
  m.payload.all (fun (_, t) => (t.check known).isEmpty)

/-- The registry's diagnostic authority (wellFormed is the Bool
    projection; this NAMES the failure). Rides `Ty.check` — the ONE
    resolver shared with SchemaLang — whose `unknownRef` render carries
    the closed-world suggestion (`CodegenCore.didYouMean`, moved here-
    adjacent so every error path reaches it core-only). -/
def FailureModeItem.diagnose (known : List String) (m : FailureModeItem) :
    List String :=
  m.payload.flatMap fun (fname, t) =>
    (t.check known).map fun d => s!"`{m.name}` payload `{fname}`: {d}"

/-- The universe check: every mode well formed. Name uniqueness is the
    `DataRegistry.nodup` proof field — subsumed by the framework (W7.4),
    no longer a Bool check here. -/
def universeWellFormed (known : List String)
    (reg : CodegenCore.DataRegistry FailureModeItem) : Bool :=
  reg.items.all (fun m => m.wellFormed known)

/-- Code allocation preserves count — the kernel-checked obligation,
    now the framework's theorem (`CodedRegistry.codes_length`). Kept
    under the stable name: the axiom gate prints it. -/
theorem allocate_length (reg : CodegenCore.CodedRegistry FailureModeItem) :
    reg.codes.length = reg.items.length :=
  reg.codes_length

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

end Faults

/-
# SchemaLang.Meta.Register.ProvenanceDocs — the doc-string registry (Core-free)

The provenance DOC-STRING registry — split out of `Register.Provenance`
(pure code motion — every declaration keeps its exact statement and
name). WHY the split: `RegisterKit`'s lower cone must NOT reach
`Register.Core` (Core imports the toolkit — a cycle would error), and
the emitted mount's provenance hookup references `registerSchemaItemDoc`
— so the hook's home must be Core-free. These declarations touch only
`Lean` + `CodegenCore` (`schemaItemDocsExt`, its reader, the lookup,
and the write). The doc strings stay in a SEPARATE persistent
extension, NOT on `Item` — `Item` is the closed boundary universe, and
a provenance field would poison its BEq/specEq/snapshot surface
(`FuncSig.body`'s precedent, extended to all item kinds).
`Register.Provenance` (the naming helpers + the partial reifier —
Core-coupled — plus `provenanceOf`, which reads these via `itemDoc?`)
imports this module and re-exports it; consumers keep importing
`SchemaLang.Meta.Reflect` / `Register.Provenance` and see the same
names.
-/
module

public import Lean
public import CodegenCore

public meta section

namespace SchemaLang.Meta

open Lean

/-- Provenance extension: Lean declaration name ↦ doc string (the ONE
    doc string for the declaring constant). -/
initialize schemaItemDocsExt :
    SimplePersistentEnvExtension (Name × String) (List (Name × String)) ←
  CodegenCore.mkRegistryExt `schemaItemDocsExt

/-- All registered doc strings from an environment (the emitter entry
    point). -/
def registeredItemDocs (env : Environment) : List (Name × String) :=
  schemaItemDocsExt.getState env

/-- Look up the doc string for one declared schema item. Returns the
    empty string when no doc string was written (not all declarations
    carry one). -/
def itemDoc? (env : Environment) (leanName : Name) : String :=
  match (registeredItemDocs env).find? (fun (n, _) => n == leanName) with
  | some (_, doc) => doc
  | none => ""

/-- Register the doc string for one reflected item. Silent when the
    declaration carries no doc string. -/
def registerSchemaItemDoc (leanName : Name) : CoreM Unit := do
  let env ← getEnv
  let doc? ← liftM <| findDocString? env leanName
  if let some doc := doc? then
    modifyEnv fun env =>
      schemaItemDocsExt.addEntry env (leanName, doc)

end SchemaLang.Meta

end -- public meta section

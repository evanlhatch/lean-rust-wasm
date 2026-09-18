/-
# SchemaLang.Meta.Register.Core — the schema-item registry (shared core)

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name). `Meta/Reflect.lean`
remains the shared core + the public re-export hub; this module holds
the machinery every other `Register` module mounts: the `schemaItemExt`
extension + its read/write path.
-/
module

public import Lean
public import Qq
public import CodegenCore.AttrKit
public import CodegenCore
public meta import SchemaLang.Ty
public meta import SchemaLang.Item
public meta import SchemaLang.Invariant
public meta import SchemaLang.Update
public meta import SchemaLang.Keys
-- Update2 is mathlib-FREE by construction (the neutrality family moved
-- to Update.lean at W8.3 — TickCascade's `Dbsp.Effects` dependency
-- must NOT reach legacy `Meta.Reflect` consumers: the feature-flags
-- `Flag` collision lesson). Keep it that way: Update2 imports
-- Update/Keys/CodegenCore only.
public meta import SchemaLang.Update2
public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/-- The registry: Lean declaration name ↦ schema item, append-only
    (the `CodegenCore.mkRegistryExt` semantics: append on add,
    concatenate on import — not a hand copy of them). -/
initialize schemaItemExt :
    SimplePersistentEnvExtension (Name × Item) (List (Name × Item)) ←
  CodegenCore.mkRegistryExt `schemaItemExt

/-- Registered items from an environment (the emitter entry point). -/
def registeredItems (env : Environment) : List (Name × Item) :=
  schemaItemExt.getState env

/-- Register one reflected item (the attribute handler's write path). -/
def registerSchemaItem (leanName : Name) (item : Item) : CoreM Unit :=
  modifyEnv fun env =>
    schemaItemExt.addEntry env (leanName, item)

end SchemaLang.Meta

end -- public meta section

/-
# SchemaLang.Meta.Register.Core — the schema-item registry (shared core)

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name). `Meta/Reflect.lean`
remains the shared core + the public re-export hub; this module holds
the machinery every other `Register` module mounts: the `schemaItemExt`
extension + its read/write path.

S5 (the meta-toolkit): the extension + the reader below are the
EMITTED skeleton now (`declare_registry_member` — RegisterKit), the
default pair shape (`Name × Item`); every declaration keeps its name
and the module's behavior is unchanged (byte-tie pins it). The
write path (`registerSchemaItem`) stays HAND-WRITTEN — the toolkit
emits no writer for form (i), and the `@[schema]` attribute stays
hand-rolled too (the seam — `Register.Schema`, documented there).
LAYERING: this module imports the kit (the block below needs its
elaborator), so the kit's own cone must be Core-free by construction
— the emitted mount's provenance hookup references the doc-string
registry, which lives in the Core-free `Register.ProvenanceDocs`, not
in `Register.Provenance` (which imports this module — the cycle would
error).
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
-- The S5 meta-toolkit (`declare_registry_member` — RegisterKit): the
-- registry block below is its emitted skeleton. The kit sits ABOVE
-- this module (its cone is Core-free — `Register.ProvenanceDocs`, the
-- layering note in the module header).
public meta import SchemaLang.Meta.RegisterKit
public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/- The registry: Lean declaration name ↦ schema item, append-only
   (the `CodegenCore.mkRegistryExt` semantics: append on add,
   concatenate on import — replayed from oleans at import). The
   extension + the reader below are the EMITTED skeleton now
   (`declare_registry_member` — RegisterKit; the default pair
   shape; decls byte-identical to the hand-rolled block they
   replace; a plain block comment, not a doc comment — doc comments
   demand a declaration after them, and this is a command). The
   write path `registerSchemaItem` stays hand-written below — the
   toolkit emits no writer for form (i). -/
declare_registry_member schemaItemExt registeredItems : Item

/-- Register one reflected item (the attribute handler's write path). -/
def registerSchemaItem (leanName : Name) (item : Item) : CoreM Unit :=
  modifyEnv fun env =>
    schemaItemExt.addEntry env (leanName, item)

end SchemaLang.Meta

end -- public meta section

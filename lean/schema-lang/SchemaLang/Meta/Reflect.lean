/-
# SchemaLang.Meta.Reflect — `@[schema]`: native Lean types as the spec

The authoring surface is PLAIN Lean declarations. The attributes reflect
them at elaboration time into registry items — the author never writes
`Ty` or `Item` by hand. This is the buf model with the descriptor
produced by the compiler itself.

Reflection coverage (the four item kinds):
- `@[schema]` on a structure  → `Item.record`
- `@[schema]` on an inductive → `Item.variant` (payload-carrying ctors)
- `@[schema_fn]` on a def     → `Item.func` (the SIGNATURE is the spec;
                                 the body is irrelevant to emission).
                                 Optional ident arg sets the semantic
                                 fields (6.5.1): `@[schema_fn volatile]`,
                                 `@[schema_fn strict.volatile]`, …
- `@[schema_resource]` on a def/type → `Item.resource` (opaque handle)

Reifier scope (v1, honest limits): scalars Bool/UInt8..UInt64/
Int8..Int64/Float32/Float 1:1; `String`, `ByteArray`, `List T`,
`Option T`, `Sum T E` recursive; `Future T`/`Stream T` marker defs →
`.future`/`.stream` (WASI 0.3 async at the boundary); a head that is
another `@[schema]` declaration → `.ty` ref (forward references fail —
register the referenced type first); everything else → a domain-voiced
elaboration error enumerating the boundary fragment. Parameterized
inductives are rejected (v1): their ctors carry implicit binders the
naive arg-walk would misread.

Registration: a `SimplePersistentEnvExtension` replayed from oleans at
import — the driver (`forge gen`) imports the demo module, reads the
environment, and the emitters see exactly what was registered.
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
-- The registration surface, split per concern (pure code motion —
-- every declaration keeps its exact statement + name). This module is
-- the re-export hub: consumers import `SchemaLang.Meta.Reflect` and
-- see the same names as before the split.
public import SchemaLang.Meta.Register.Core
public import SchemaLang.Meta.Register.Provenance
public import SchemaLang.Meta.Register.Keys
public import SchemaLang.Meta.Register.Quotes
public import SchemaLang.Meta.Register.Schema
public import SchemaLang.Meta.Register.Funcs
public import SchemaLang.Meta.Register.Invariants
public import SchemaLang.Meta.Register.Updates

/- The async boundary markers (WASI 0.3): the ONE copy. The reifier
    (`tyOfExpr?`) matches these BY NAME - do not move into a namespace.
    NON-meta + exposed (W5.4): Demo's non-meta defs elaborate
    `[] : Async.Future (List User)` by unfolding `Future`. -/
@[expose] public section
namespace Async
def Future (a : Type) : Type := a
/- Same marker shape as `Future` (the boundary marker pair). -/
def Stream (a : Type) : Type := Future a
end Async

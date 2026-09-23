/-
# SchemaCore — the umbrella module

One import point for the library (root-module imports are NOT
re-exported — this module re-exports by importing):

- `SchemaCore.Ty` — the closed boundary universe (now with the `KeyTy`
  scalar sub-universe for map/set keys and the `bounded` cap-in-type
  lane base).
- `SchemaCore.Value` — the typed value universe + the evaluator (the
  total denotation).
- `SchemaCore.Item` — the item model + the registry + the obligation view.
- `SchemaCore.RowVals` — the positional row layer + the name↔index iso.
- `SchemaCore.Register` — `@[schema]` + the env extension.
- `SchemaCore.Describe` — the typed description universe (D19's ONE
  meta-universe) + the generic rendering derivation + the reflector.
- `SchemaCore.Emit` — the slice's emitter + the shared regen core.
- `SchemaCore.Snapshot` — the universe snapshot (the registry-state
  serialization: the canonical sorted one-line-per-item format, the
  total print/parse pair, the PROVED round trip `parse_print`, the
  emitter row + the gate's ONE reading).

The five questions (notes/v3/01-core.md): answered per submodule (the
list above); the umbrella itself answers none — it is the import
point. Gate row: SchemaCore IS a gated package — the axiom report +
docs-check + gen-check (the committed gen/schema-slice.wit byte-tie)
all sweep it.
-/

import SchemaCore.Ty
import SchemaCore.Value
import SchemaCore.Item
import SchemaCore.RowVals
import SchemaCore.Register
import SchemaCore.Emit
import SchemaCore.Snapshot
import SchemaCore.Describe
import SchemaCore.Codec

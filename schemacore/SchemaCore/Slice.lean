/-
# SchemaCore.Slice — the proof-of-life schema (the registered fixture)

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).

The slice's ONE registered item: a plain Lean structure — the authoring
surface is the declaration itself; `@[schema]` reflects it into a
`SchemaCore.Item` and appends it to `schemaItemExt` at elaboration.
The drivers (`lake exe schema`, `gates gen-check`) replay this module's
olean with `loadExts := true` — the registration IS this file.

Every `Ty` constructor is exercised by a registered field where the
closed universe has an AUTHORING spelling: `Example` carries the four
scalars + `option` + `list`; `ExampleEx` carries the sum shape (`Sum a
b` → `.result`), the map shape (`List (K × V)` → `.map`), and the
bounded lane's base type (`Fin cap` → `.bounded`). The `set` ctor has
NO authoring spelling today — `List K` reifies to `.list K` (the
honest reading; the shapes are ambiguous in plain Lean), so a set
field waits for a wrapper-typed authoring surface — its lowering is
pinned at the `renderTy`/tests level, its registration named the gap.

Provenance: fresh (the fixture IS the slice; no legacy content).

The five questions (notes/v3/01-core.md):
- root: Universe content — the `Example` item over the closed `Ty`.
- carrier grade: the registry's nodup-in-type at elaboration (a
duplicate field name fails the build).
- spine reading: registration = append (this file IS the event-log
row); the drivers replay + read it.
- ladder rung: the fields-nodup obligation discharges at decidableNow.
- gate row: gen-check — the replayed registration writes the tied
artifact.
-/

import SchemaCore

open SchemaCore

@[schema]
structure Example where
  ready : Bool
  count : UInt64
  delta : Int64
  label : String
  note : Option String
  tags : List String

/-- The grown-universe fixture: the sum shape (the item model is
    records-only today — the sum rides the `result` Ty FIELD TYPE;
    variant ITEMS are the named future consumer, Item.lean's honest
gap), the map shape (the association-list spelling; the WIT lowering
is the declared retraction-with-note), and the bounded base type (the
cap in the type; the WIT lowering drops it — the declared loss). The
VARIANT-ITEM NOTE: `@[schema]` registers records only; when the item
model grows variants, this fixture grows the variant row and the WIT
emitter grows the `variant` decl (the mined legacy mapping). -/
@[schema]
structure ExampleEx where
  status : Sum UInt64 String
  counts : List (String × UInt64)
  small : Fin 42

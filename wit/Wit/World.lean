/-
# Wit.World — the WIT world value (the component boundary's contract side)

Owner: the component lane (the mandate tree, `wit/` — the same Wit
agent's zone; the world lands with its first consumer,
`Guest.Component`).
Driving decisions: notes/v3/13-interfaces.md (the WIT worlds row: the
component boundary is the contract) + notes/v3/03 (the boundary
discipline: the world is the SSOT the component's emission is checked
against — the skew discipline at generation) + the legacy GenMain
mining (`worldExportsOf`/`typeItemWit`/`worldWitOf` — the world as
data over the typed AST, never a string template).

## The shape

The world rides the LANDED typed AST (`Wit.Field`/`Wit.Interface`/
`Wit.Ty` — no second type grammar):

- `Func` — a world func: named params + AT MOST ONE unnamed result
  (the canonical-ABI scalar fragment's shape; multi-result funcs are
  unrepresentable here — the honest gap, grown with the consumer) +
  the `async` flag (the WASI async lane's func-level row: an `async`
  func lifts via the async-lift protocol — `Machines.AsyncSession`'s
  handshake, whose WIT-side bridge is `Wit.Session`'s
  `exportTape`/`importTape` + the duality check — and its spelling is
  `name: async func(...)` per the WIT spec's current shape, confirmed
  against the mandate tree's own fixtures, e.g. legacy
  `splicer-mw.wit`'s `export watch-counts: async func(n: u64) ->
  stream<u64>;`).
- `Item` — one world item: a func (the inline form the component lane
  emits) or an interface (the by-name form over the landed carrier).
- `World` — the world's imports/exports as data, each side's item
  names distinct IN THE TYPE (the DataRegistry pattern: a
  duplicate-named literal fails to elaborate through the `by decide`
  default; the runtime route is the constructor's decided refusal).

## Named exclusions (the leftover rule, each with its consumer)

- **the world-block parse-back LANDED** (with the func-level async
  row): `Wit.Parse.parseWorld` reads `Render.world`'s image back into
  the WorldOk-gated carrier (the round-trip laws are the generic
  instances). The worldFile DOCUMENT's package line stays render-only
  — the id is the component driver's, not the contract's (`World`
  carries no id); the document's tie is the render-side byte-tie
  (the committed bytes vs the fresh render).
- **no resources / no `use` / no worlds-in-worlds** — none is
  reachable by the component lane's emission today.

Core-only (no imports — the cone root of the WIT lane, beside `Wit`).

The five questions (notes/v3/01-core.md):
- root: Crossing — the component boundary's contract read as data
  over the typed WIT AST.
- carrier grade: the nodup facts ride the TYPE (`imports_nodup`,
  `exports_nodup` — the DataRegistry pattern).
- spine reading: the Interpretation stage's contract side — the
  component's emission folds this carrier; `Render.worldFile` is its
  text face.
- ladder rung: rung 1 — closed data + decided nodup defaults.
- gate row: the axiom report (the `Wit` root's sweep).
-/
module


public import Wit


@[expose] public section
namespace Wit

/-- A world func: the wire name, the named params, at most one
    unnamed result. The params reuse the landed `Field` carrier (name
    + type); the closed `Ty` grammar is the only type vocabulary. -/
structure Func where
  name : String
  params : List Field
  result : Option Ty
  /-- The async-lift discipline: the func's WIT row is spelled
      `async func(...)` and its call rides the async-lift handshake
      (`Machines.AsyncSession`'s session — the WIT-side bridge is
      `Wit.Session`). The default is `false` — every pre-existing
      func literal is a sync row, the artifacts' bytes unchanged. -/
  async : Bool := false
deriving Repr, Inhabited

/-- One world item: the inline-func form (the component lane's
    exports) or the by-name interface form (over the landed
    carrier). -/
inductive Item where
  /-- An inline func item (`export add: func(...) -> ...;`). -/
  | func (f : Func)
  /-- An interface item (`export types;` — the landed `Interface`). -/
  | iface (i : Interface)
deriving Repr, Inhabited

/-- The item's wire name (the nodup discipline's key). -/
def Item.name : Item → String
  | .func f => f.name
  | .iface i => i.name

/-- A WIT world: the two item lists (imports/exports) with each
    side's names distinct IN THE TYPE (the `DataRegistry` pattern —
    WIT rejects a world that exports or imports one name twice). -/
structure World where
  name : String
  imports : List Item
  exports : List Item
  imports_nodup : (imports.map Item.name).Nodup := by decide
  exports_nodup : (exports.map Item.name).Nodup := by decide
deriving Repr, Inhabited

end Wit

end -- public section


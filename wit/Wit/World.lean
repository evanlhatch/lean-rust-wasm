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
  unrepresentable here — the honest gap, grown with the consumer).
- `Item` — one world item: a func (the inline form the component lane
  emits) or an interface (the by-name form over the landed carrier).
- `World` — the world's imports/exports as data, each side's item
  names distinct IN THE TYPE (the DataRegistry pattern: a
  duplicate-named literal fails to elaborate through the `by decide`
  default; the runtime route is the constructor's decided refusal).

## Named exclusions (the leftover rule, each with its consumer)

- **no parse-back** — `Wit.Render.worldFile` is render-only; the
  world text's parser direction is a NAMED follow-up (the landed
  parser's accepted language is unchanged — the round-trip law's
  scope does not grow silently). The world artifact's tie is the
  render-side byte-tie (the committed bytes vs the fresh render).
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

import Wit

namespace Wit

/-- A world func: the wire name, the named params, at most one
    unnamed result. The params reuse the landed `Field` carrier (name
    + type); the closed `Ty` grammar is the only type vocabulary. -/
structure Func where
  name : String
  params : List Field
  result : Option Ty
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

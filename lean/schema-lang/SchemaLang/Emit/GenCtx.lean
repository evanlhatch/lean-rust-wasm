/-
# SchemaLang.Emit.GenCtx — the emitter contract's environment (v2)

The v1 emitter contract was `Emitter (List Item)`: `run` saw the schema
item universe ONLY. The dogfood finding: the invariant/update lanes'
`run` ignored the registry entirely — they folded COMMITTED demo rows
(`demoInvariants`/`demoUpdates`), so a SECOND project's registered
invariants/updates never emitted (the registry was replayed, then
silently dropped at the emitter boundary).

The contract upgrade: the emitters' state type is `GenCtx` — the
project's FULL registry state, all three lanes in one value:

- `items` — the boundary universe (`schemaItemExt`), replayed from the
  spec module's oleans by the driver,
- `invariants` — the `schema_invariant` registry (`invariantItemExt`),
- `updates` — the `schema_update` registry (`updateItemExt`).

Emitters that consume only the item universe read `ctx.items` (or are
built with `GenCtx.itemsOnly`); the invariant/update emitters read
`ctx.invariants`/`ctx.updates`. Adding a lane = one field here + the
emitters that consume it — the registry (`Emitter GenCtx`) and the
driver need no further shaping.

This module holds ONLY the ctx (no emitter): `Emit.Invariant` and
`Emit.Update` import it, and neither may import the other — the
dependency stays a tree.

The v3 provenance lane: `roots` — the root-namespace partition of the
item universe. The dogfood's multi-world lane needs per-project WIT
worlds, and the partition is DERIVED (never hand-listed): the driver
resolves each item's DECLARING name to its declaring module (the
environment's own map) and groups by it — see `rootPartitionOf`.
Emitters consume `ctx.rootItems`.
-/

import Lean
import CodegenCore
import SchemaLang.Item
import SchemaLang.Invariant
import SchemaLang.Update
import SchemaLang.Wf

namespace SchemaLang.Emit

open Lean


/-- The project's full registry state — the emitters' `run` input
    (the emitter contract v2). -/
structure GenCtx where
  /-- The boundary universe (the `@[schema]` registry). -/
  items : List Item
  /-- The registered invariants (the `schema_invariant` registry). -/
  invariants : List InvariantItem
  /-- The registered updates (the `schema_update` registry). -/
  updates : List SomeUpdate
  /-- The root-namespace partition of `items`: one (root, its items)
      entry per declaring module, roots in first-occurrence order, items
      in registration order. Empty = a provenance-free ctx (the v2
      shape; the item-universe emitters never read it). -/
  roots : List (Name × List Item) := []

/-- The items-only ctx: emitters/checks that consume the item universe
    and ignore the invariant/update lanes. -/
def GenCtx.itemsOnly (items : List Item) : GenCtx :=
  { items := items, invariants := [], updates := [] }

/-- The CHECKED view of the item universe (W7.9 phase 2). DESIGN
    CHOICE (the order offered the alternative of the DRIVER computing
    the checked universe once and the ctx carrying it): the view is a
    pure projection on the ctx instead. Reason: every existing
    `Emitter GenCtx` literal keeps compiling — no structure-field
    change (the `roots` lane, `itemsOnly`, and the seven emitter
    literals are untouched), and "discharge once" is a `let` at the
    consumer (`match ctx.checkedItems? with ...`), not a driver
    reshaping. The discharge itself is the bridge: the executable
    authority (`universeCheck`, the `SchemaDiag` source tooling reads)
    transports into the reasoning authority (`WellFormed`) via
    `universeCheck_sound`. `none` = the registry is ill-formed —
    emitters on this view keep their pre-evidence fallback; DIAGNOSES
    stay `universeCheck`'s job, not this view's. -/
def GenCtx.checkedItems? (ctx : GenCtx) : Option CheckedUniverse :=
  if h : universeCheck ctx.items = [] then
    some ⟨ctx.items, universeCheck_sound h⟩
  else none

/-- Group named items by the name's ROOT namespace (`Name.getRoot`):
    order-preserving both ways — roots by first occurrence, items in
    registration order (the fold cannot drift from the registry).
    Callers whose declaring names are not the provenance (both the demo
    and the flags packages declare at Lean's TRUE root) pre-map the
    names first — see `rootPartitionOf`. -/
def groupByRoot (named : List (Name × Item)) :
    List (Name × List Item) :=
  named.foldl
    (fun acc (n, it) =>
      let root := n.getRoot
      if acc.any fun (r, _) => r == root then
        acc.map fun (r, its) => if r == root then (r, its ++ [it]) else (r, its)
      else acc ++ [(root, [it])])
    []

/-- The provenance MAP (the partition's input): each declaring name →
    its DECLARING MODULE (`Environment.getModuleIdxFor?` + the module-name
    array — the environment's own map, never a hand list). The module
    names (`Demo`, `FeatureFlags`) ARE the root namespaces the
    wire-worlds partition by. A name the map misses (a same-env
    registration) maps to itself. -/
def namedByModule (env : Lean.Environment) (named : List (Lean.Name × Item)) :
    List (Lean.Name × Item) :=
  named.map fun (n, it) =>
    (((Lean.Environment.getModuleIdxFor? env n).map
      fun idx => env.allImportedModuleNames[idx.toNat]!).getD n, it)

/-- The provenance partition of ONE environment: `groupByRoot` over
    `namedByModule`. Multi-env drivers concat `namedByModule` lists
    first (the registry's append order), then group once. -/
def rootPartitionOf (env : Lean.Environment) (named : List (Lean.Name × Item)) :
    List (Lean.Name × List Item) :=
  groupByRoot (namedByModule env named)

/-- One root's partition of the ctx: the items whose declaring module
    is `root` (empty when the ctx carries no provenance lane or the
    partition doesn't name the root). The world emitters' lookup. -/
def GenCtx.rootItems (ctx : GenCtx) (root : Name) : List Item :=
  match ctx.roots.find? fun (r, _) => r == root with
  | some (_, its) => its
  | none => []

end SchemaLang.Emit

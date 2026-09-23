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
- `updates2` — the v2 `schema_update` registry (`update2ItemExt`; the
  v1→v2 migration — the emitter and the trace batches ride the v2
  wrapper now).

Emitters that consume only the item universe read `ctx.items` (or are
built with `GenCtx.itemsOnly`); the invariant/update emitters read
`ctx.invariants`/`ctx.updates2`. Adding a lane = one field here + the
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

module

public import Lean
public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Invariant
public import SchemaLang.Update
public import SchemaLang.Update2
public import SchemaLang.Wf

@[expose] public section

namespace SchemaLang.Emit

open Lean


/-- The project's full registry state — the emitters' `run` input
    (the emitter contract v2). -/
structure GenCtx where
  /-- The boundary universe (the `@[schema]` registry). -/
  items : List Item
  /-- The registered invariants (the `schema_invariant` registry). -/
  invariants : List InvariantItem
  /-- The registered updates (the v2 `schema_update` registry —
      `update2ItemExt`; the v1→v2 migration). -/
  updates2 : List SomeUpdate2
  /-- The root-namespace partition of `items`: one (root, its items)
      entry per declaring module, roots in first-occurrence order, items
      in registration order. Empty = a provenance-free ctx (the v2
      shape; the item-universe emitters never read it). -/
  roots : List (Name × List Item) := []

/-- The items-only ctx: emitters/checks that consume the item universe
    and ignore the invariant/update lanes. -/
def GenCtx.itemsOnly (items : List Item) : GenCtx :=
  { items := items, invariants := [], updates2 := [] }

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

/-- The checkpoint's TRANSPORT (the law-bearing emitters' citation):
    a checked view IS the ctx's item universe — the check discharges
    well-formedness evidence, it never selects or transforms content.
    (The checked-view consumers' laws state their contracts over the
    bundle; this lemma moves them to the ctx the driver replayed.) -/
theorem GenCtx.checkedItems?_val (ctx : GenCtx) (cu : CheckedUniverse)
    (h : ctx.checkedItems? = some cu) : cu.val = ctx.items := by
  unfold checkedItems? at h
  split at h
  · exact congrArg Subtype.val (Option.some.inj h).symm
  · exact absurd h (by simp)

/- THE SINGLE CHECKPOINT (W7.9 phase 2 sweep): `checkedItems?` is the
    ONLY `universeCheck` discharge on the emission path — every
    item-universe emitter's `run` consumes the bundle through it
    (`match ctx.checkedItems? with …`), no emitter re-checks. The
    registry (`Emit.Registry.coreEmitters`) documents the routing
    contract; the driver-restructure (a `checked` field computed once
    in `GenCtxIO.loadGenCtx`, handed to every emitter) is the named
    follow-up — the projection is a pure function of `ctx.items`, so
    the two are definitionally interchangeable and the bytes are
    unaffected either way. -/

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

/-! ## The one-pass kind partition

The emitters repeatedly re-walk the item universe with a
`filterMap`-by-kind (records here, funcs there, resources somewhere
else) — one fold per lane, ~10 walks over the same list across the
Emit modules. `Item.partition` walks ONCE and hands out the four kind
lanes; each lane keeps registration order, so any single-lane
conversion is emission-order-neutral (a site that needs the
INTERLEAVED kind order — e.g. Rust `schemaItems`' record/variant
interleave, `Wit.worldOf`'s type list — stays on `filterMap`:
`records ++ variants` would reorder a mixed universe, and the byte-tie
law forbids even a caught reordering).

(NOT in Item.lean — that module is another lane's file right now; the
home is the emit tree's shared dependency root, which every converting
site already imports. OUTSIDE the `SchemaLang.Emit` namespace: a nested
`def Item.partition` inside it would land as
`SchemaLang.Emit.Item.partition` — an impostor the inner sites would
silently resolve to while `SchemaLang.Item.partition` stayed missing.) -/

namespace SchemaLang.Item

/-- The four kind lanes of an item universe. -/
structure Partition where
  /-- The `.record` items, registration order. -/
  records : List (String × List Field)
  /-- The `.variant` items, registration order. -/
  variants : List (String × List VariantCase)
  /-- The `.func` signatures, registration order. -/
  funcs : List FuncSig
  /-- The `.resource` names, registration order. -/
  resources : List String

/-- One pass over the universe, four lanes out (a `foldr`, so each lane
    is registration-ordered; never a `termination_by` def — the
    kernel-opaque trap). -/
def partition (items : List Item) : Partition :=
  items.foldr (fun it acc =>
    match it with
    | .record n f => { acc with records := (n, f) :: acc.records }
    | .variant n c => { acc with variants := (n, c) :: acc.variants }
    | .func s => { acc with funcs := s :: acc.funcs }
    | .resource n => { acc with resources := n :: acc.resources })
    { records := [], variants := [], funcs := [], resources := [] }

end SchemaLang.Item

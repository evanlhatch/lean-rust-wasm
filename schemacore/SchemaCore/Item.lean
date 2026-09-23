/-
# SchemaCore.Item — the item model: a record of named `Ty` fields

Owner: the SchemaCore agent (the macht tree, `schemacore/`).
Driving decisions: notes/v3/01-core.md §1 (Universe root), §5 (the
spine: the registry is the accumulated event log, the emitter reads
it); notes/v3/15-patterns.md #4 (the obligation as data — the slice's
one checkable fact mounts HERE, not in a lane).

`Item` is the ONE shape the slice needs: a record-of-fields. The
universe is a `Kit.DataRegistry Item` — name uniqueness IN THE TYPE
(a duplicate-named registry fails to elaborate; the runtime side,
`registryOfItems`, decides the same fact and refuses loudly).

Deliberately absent (honest gaps, named): no variants, no keys, no
codecs — the slice proves the spine end-to-end with one shape; the
rest ports when its consumer lands (14's leftover rule). The
row-bridge Iso and the value universe now EXIST (see `SchemaCore.RowVals`
+ `SchemaCore.Value`); the per-record bridge is demonstrated on the
slice fixture in SchemaTests until GenKit generates it.

The five questions: root = Universe; carrier = the registry's
nodup-in-type + the emitter's law (the closed-world naming
precondition); spine reading = Registry → Interpretation → artifact;
ladder rung = `decidableNow` (the fields-nodup obligation); gate row =
byte-tie + axioms.

Core-only.
-/

import Kit
import SchemaCore.Ty

open Kit

namespace SchemaCore

/-! ## The item model -/

/-- One field: a name + its boundary type. -/
structure Field where
  name : String
  ty : Ty
  deriving Repr, BEq, Inhabited

/-- A schema item: a record of named fields. `name` is the Lean
    declaration's name (the provenance-faithful registration key). -/
structure Item where
  name : String
  fields : List Field
  deriving Repr, BEq, Inhabited

/-- `kebabName`: the wire spelling of a Lean name's last component —
    camelCase split at every uppercase (`"OrderItem"` → `"order-item"`).
    The WIT record names come from here (never hand-set). -/
def kebabName (s : String) : String :=
  let folded := s.toList.foldl (fun acc c =>
    if c.isUpper then acc ++ ['-', c.toLower] else acc ++ [c]) []
  match folded with
  | '-' :: rest => String.ofList rest
  | _ => String.ofList folded

/-- The item's wire name: the last component of its Lean name,
    kebab-cased (`"SchemaCore.Slice.Example"` → `"example"`). -/
def Item.wireName (item : Item) : String :=
  kebabName ((item.name.splitOn ".").getLast!)

/-! ## The universe as a DataRegistry -/

/-- The universe: the registered items, as a `Kit.DataRegistry` — name
    uniqueness in the type. The runtime constructor from the replayed
    extension state: the nodup fact is DECIDED (not assumed) and a
    duplicate name is the loud `.error` (the closed-world rejection —
    there is no silent acceptance path). -/
def registryOfItems (items : List Item) :
    Except String (DataRegistry Item) :=
  if h : (items.map (·.name)).Nodup then
    .ok { items := items, nameOf := fun it => it.name, nodup := h }
  else
    .error s!"duplicate item names: {items.map (·.name)} — \
      every registered item needs a unique name"

/-! ## The obligation view — the slice's one checkable fact -/

/-- The obligation: an item's field names are distinct. The tier is
    `decidableNow` — over concrete field lists the fact is a `decide`.
    Registration COMPUTES the tier; backends READ it (Kit.Obligation). -/
def fieldNodupObligation (item : Item) : Obligation (List String) :=
  { label := s!"schema/{item.name}/fields-nodup"
    tier := .decidableNow
    payload := item.fields.map (·.name)
    provenance := `SchemaCore }

/-- The claim the obligation carries. -/
def fieldNodupClaim (o : Obligation (List String)) : Prop := o.payload.Nodup

/-- The claim's decision procedure (the runtime `decide` instance). -/
instance fieldNodupClaimDec :
    ∀ o : Obligation (List String), Decidable (fieldNodupClaim o) :=
  fun o => List.nodupDecidable o.payload

/-- The discharge via the kit's decidableNow backend — `none` is the
    LOUD refusal (a false claim or a mis-wired tier; the backend never
    fabricates evidence). Soundness/completeness are Kit's theorems,
    cited, never re-proved. -/
def dischargeFieldNodup (item : Item) : Option Evidence :=
  (fieldNodupObligation item).decideDischarge fieldNodupClaim

end SchemaCore

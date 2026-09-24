/-
# SchemaCore.Item — the item model: a record of named `Ty` fields

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
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
    The WIT record names come from here (never hand-set).
    THE ONE MANGLER: the body delegates to `Kit.kebab` (Kit.Mangle) (the WIT
    lane's convention lives THERE, with the post-mangle uniqueness
    discipline — a parallel kebab here would be a second escaping
    decision). Byte-identical to the pre-delegation hand fold on the
    lane's input class (Lean name components — pure camelCase, no
    separators): `gates gen-check`'s byte-tie over `gen/schema-slice.wit`
    is the proof. -/
def kebabName (s : String) : String :=
  Kit.kebab s

/-- The last `.`-component of a name, as a structural char fold —
    the KERNEL-REDUCIBLE face of `(s.splitOn ".").getLast!` (core's
    splitOn rides the String iterator — wf recursion, 06 §2's
    kernel-opacity trap — so anything that must reduce in the kernel
    — the golden theorems' `decide`/`rfl` — routes through HERE;
    the two spellings agree on every input: both return the run of
    characters after the last `.`). -/
def lastName (s : String) : String :=
  String.ofList
    (s.toList.foldl (fun cur c => if c == '.' then [] else cur ++ [c]) [])

/-- The item's wire name: the last component of its Lean name,
    kebab-cased (`"SchemaCore.Slice.Example"` → `"example"`). -/
def Item.wireName (item : Item) : String :=
  kebabName (lastName item.name)

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

/-- The obligation: an item's field names are distinct — THE CLAIM IS
    THE TYPE INDEX (the row is `Obligation (List String)
    ((item.fields.map (·.name))).Nodup`), so the tier/evidence/
    discharge can never drift from the claim. The tier is
    `decidableNow` — over concrete field lists the fact is a `decide`.
    Registration COMPUTES the tier; backends READ it (Kit.Obligation). -/
def fieldNodupObligation (item : Item) :
    Obligation (List String) ((item.fields.map (·.name))).Nodup :=
  { label := s!"schema/{item.name}/fields-nodup"
    tier := .decidableNow
    payload := item.fields.map (·.name)
    provenance := `SchemaCore }

/-- The discharge via the kit's decidableNow backend — the claim
    discharged is the obligation's OWN index (there is no claim
    parameter to mis-wire); `none` is the LOUD refusal (a false claim
    or a mis-wired tier; the backend never fabricates evidence).
    Soundness/completeness are Kit's theorems, cited, never re-proved. -/
def dischargeFieldNodup (item : Item) : Option Evidence :=
  (fieldNodupObligation item).decideDischarge

end SchemaCore

/-
# Kit.Registry — the value-level registries

`DataRegistry`: name uniqueness IN THE TYPE (a duplicate-named literal
fails to elaborate — there is no runtime rejection path because there
is no illegal state). (The death-check retired `CodedRegistry` — the
position-derived dense codes — with no consumer beyond its own test
fixture; the persisted-code-space discipline lives in `Kit.CodeRegistry`
+ `Kit.CheckedProp`.)

Provenance: mined from
`legacy/lean/codegen-core/CodegenCore/DataRegistry.lean` +
DidYouMean.lean's engine — theorem content ported, files FRESH
(the env-extension layer of legacy Registry.lean deliberately does NOT
port here: this is the value-level registry; the compile-time event
log is a separate consumer's mount). The `insert` restoration + its
laws + `nodupNamesIso` mine `DataRegistry.lean` and
`CodegenCore.Kit.lean` (`nodupNamesIso`); `DisjointCommute` mines
`CodegenCore.Kit.lean`.

Core-only (no mathlib/Batteries). `Lean.EditDistance` is the compiler's
own DP — core.

The five questions (notes/v3/01-core.md):
- root: Universe — finite, name-keyed data.
- carrier grade: nodup-in-type (a duplicate-named literal fails to
  elaborate — the unrepresentable grade); didYouMean is plain
  first-order data.
- spine reading: the REGISTRY half of Registry → Interpretation (the
  value-level integral; the env-log mount is Kit.Lane's).
- ladder rung: rung 1 — invariants decided/in-the-type; no proof
  family.
- gate row: Kit's row in Gates.Packages' gated set (the per-library
  axiom sweep covers it); KitTests pins the allocation + suggestion
  behavior.
-/


module

public import Lean
public import Kit.Correspondence
public import TextKit.Suggest

@[expose] public section


namespace Kit

/-! ## didYouMean — the closed-world error discipline -/

/-- The closest dictionary entries to `got`, nearest first. The closed
    world means the dictionary is always complete — the candidates ARE
    the valid space, not a heuristic. DELEGATION: the ONE engine lives
    at `TextKit.Suggest` (the cone/build call — the module-system C0
    substrate both diagnostic sides import); this is the `Kit`-namespaced
    route over it, kept so every Kit-side consumer and pin is
    interface-preserved. -/
def didYouMean (got : String) (dict : List String) (maxDist : Nat := 3) :
    List String :=
  TextKit.didYouMean got dict maxDist

/-! ## DataRegistry — name uniqueness in the type -/

/-- A registry of named items with uniqueness IN THE TYPE: `nodup` is a
    proof field whose default discharges by `decide` over the concrete
    items — a duplicate name makes the literal fail to elaborate. -/
structure DataRegistry (α : Type) where
  /-- The items, in registration order. -/
  items : List α
  /-- The naming function (names are the lookup keys). -/
  nameOf : α → String
  /-- Names are unique. Default: discharged by `decide`; override with
      an explicit proof for non-concrete item lists. -/
  nodup : (items.map nameOf).Nodup := by decide

namespace DataRegistry

/-- All items, in registration order. -/
def all (reg : DataRegistry α) : List α := reg.items

/-- A lookup miss: the requested name plus the nearest registered names
    (the closed-world rule — the suggestions ARE the valid space). -/
structure LookupMiss where
  /-- The name that was requested. -/
  got : String
  /-- The nearest registered names (`Kit.didYouMean`). -/
  didYouMean : List String

/-- Name lookup: the unique item with that name, or a structured miss
    with did-you-mean suggestions over the registered names. -/
def lookup? (reg : DataRegistry α) (name : String) : Except LookupMiss α :=
  match reg.items.find? (fun it => reg.nameOf it == name) with
  | some it => .ok it
  | none => .error { got := name
                     didYouMean := Kit.didYouMean name (reg.items.map reg.nameOf) }

/-! ## The laws (proved once, here) -/

/-- Uniqueness consequence, generic: a nodup name-map makes the naming
    function injective on the list. -/
theorem nodup_map_unique (f : α → String) {l : List α}
    (hnd : (l.map f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (heq : f a = f b) : a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hxnot, hxs⟩ := hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact absurd (heq ▸ List.mem_map_of_mem hb) hxnot
    · rcases hb with rfl | hb
      · exact absurd (heq.symm ▸ List.mem_map_of_mem ha) hxnot
      · exact ih hxs ha hb

/-- Uniqueness transported to the registry: two items with the same
    name are the same item. -/
theorem nameOf_injective (reg : DataRegistry α) {a b : α}
    (ha : a ∈ reg.items) (hb : b ∈ reg.items)
    (heq : reg.nameOf a = reg.nameOf b) : a = b :=
  nodup_map_unique reg.nameOf reg.nodup ha hb heq

/-- A successful lookup returns an item of the registry with the
    requested name. -/
theorem lookup?_ok_mem (reg : DataRegistry α) {name : String} {a : α}
    (h : reg.lookup? name = .ok a) : a ∈ reg.items ∧ reg.nameOf a = name := by
  unfold lookup? at h
  split at h
  · next it hfind =>
    injection h with hit
    subst hit
    have hp : (reg.nameOf it == name) = true :=
      List.find?_some (p := fun it => reg.nameOf it == name) hfind
    exact ⟨List.mem_of_find?_eq_some hfind, beq_iff_eq.mp hp⟩
  · next hnone =>
    cases h

/-- Determinism under nodup: the looked-up item is THE unique item with
    that name — no other item can claim it. -/
theorem lookup?_ok_unique (reg : DataRegistry α) {name : String} {a : α}
    (h : reg.lookup? name = .ok a) :
    ∀ b ∈ reg.items, reg.nameOf b = name → b = a := by
  intro b hb hbn
  obtain ⟨ha, hna⟩ := reg.lookup?_ok_mem h
  exact reg.nameOf_injective hb ha (hbn.trans hna.symm)

/-- A failed lookup is exactly the no-such-name case, and the miss
    carries the requested name plus suggestions over the registered
    names. -/
theorem lookup?_miss (reg : DataRegistry α) {name : String}
    (h : ∀ a ∈ reg.items, reg.nameOf a ≠ name) :
    reg.lookup? name
      = .error (LookupMiss.mk name
          (Kit.didYouMean name (reg.items.map reg.nameOf))) := by
  have hnone : reg.items.find? (fun it => reg.nameOf it == name) = none :=
    List.find?_eq_none.mpr fun x hx => by
      simp only [beq_iff_eq]
      exact h x hx
  unfold lookup?
  rw [hnone]

/-- Insert a fresh-named item (at the head), preserving uniqueness. The
    freshness obligation is an ARGUMENT: a duplicate name makes `insert`
    uncallable — there is no rejection path because there is no illegal
    state to reject (the mined shape; the runtime-rejection lane lives
    in `Kit.Lane.materialize`, a different carrier). -/
def insert (reg : DataRegistry α) (item : α)
    (hfresh : reg.nameOf item ∉ reg.items.map reg.nameOf) : DataRegistry α where
  items := item :: reg.items
  nameOf := reg.nameOf
  nodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨hfresh, reg.nodup⟩

/-- The inserted item is findable by its own name. -/
theorem lookup?_insert_self (reg : DataRegistry α) (item : α)
    (hfresh : reg.nameOf item ∉ reg.items.map reg.nameOf) :
    (reg.insert item hfresh).lookup? (reg.nameOf item) = .ok item := by
  simp [lookup?, insert]

/-- Insertion grows the registry by exactly one. -/
theorem all_insert (reg : DataRegistry α) (item : α)
    (hfresh : reg.nameOf item ∉ reg.items.map reg.nameOf) :
    (reg.insert item hfresh).all = item :: reg.all := rfl

end DataRegistry

/-! ## nodupNamesIso — the indexed-name space (the RowVals-projection
correspondence) -/

/-- A nodup name list IS an indexed space: position `i` ↦ the name at
    `i`, name ↦ its unique position. (`Fin n`/name-subtype reading of
    the field-name lists the RowVals lane projects by — the data-plane
    wave's name-keyed walk DOES this.) -/
def nodupNamesIso {names : List String} (hnd : names.Nodup) :
    Iso (Fin names.length) {n : String // n ∈ names} where
  to i := ⟨names[i.1]'i.2, List.getElem_mem i.2⟩
  inv n := ⟨names.idxOf n.1, List.idxOf_lt_length_of_mem n.2⟩
  to_inv n := Subtype.ext (List.getElem_idxOf (List.idxOf_lt_length_of_mem n.2))
  inv_to i := Fin.ext (by
    have hj := List.getElem_idxOf (List.idxOf_lt_length_of_mem (List.getElem_mem i.2))
    exact (List.getElem_inj hnd).mp hj)

/-! ## DisjointCommute — the shared write-disjointness law (one shape,
many granularities) -/

/-- THE shared law: `apply (apply s m₁) m₂ = apply (apply s m₂) m₁`
    whenever the mutations' locations are disjoint. A mutation acts on
    state through `apply`, has ONE location, locations carry a
    disjointness relation, and write-disjoint mutations commute. Each
    granularity instantiates the class by CITING its existing theorem
    (the proofs live where the semantics live; this class adds no
    proof). Mined from legacy `CodegenCore.Kit.lean`'s class of the same
    name (the dbsp delta system + the lens path were its two
    consumers). -/
class DisjointCommute (S L Mut : Type) where
  /-- The mutation application. -/
  apply : S → Mut → S
  /-- The (single) location a mutation writes. -/
  loc : Mut → L
  /-- Location disjointness (the side condition). -/
  Disjoint : L → L → Prop
  /-- THE contract: write-disjoint mutations commute. -/
  disjoint_commutes :
    ∀ (m₁ m₂ : Mut), Disjoint (loc m₁) (loc m₂) →
      ∀ (s : S), apply (apply s m₁) m₂ = apply (apply s m₂) m₁

end Kit

end -- @[expose] public section
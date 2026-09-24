/-
# Kit.Registry — the value-level registries

`DataRegistry`: name uniqueness IN THE TYPE (a duplicate-named literal
fails to elaborate — there is no runtime rejection path because there
is no illegal state). `CodedRegistry`: position-derived dense codes
(codes are NEVER hand-set — collision-free by construction, denseness
by construction; the executable `denseCheck` survives any hand-set-code
regression).

Provenance: mined from
`legacy/lean/codegen-core/CodegenCore/DataRegistry.lean` +
`CodedRegistry.lean` + Registry.lean's `allocateCodes` +
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
- root: Universe — finite, name-keyed data; position-derived dense
  codes.
- carrier grade: nodup-in-type (a duplicate-named literal fails to
  elaborate — the unrepresentable grade); didYouMean is plain
  first-order data.
- spine reading: the REGISTRY half of Registry → Interpretation (the
  value-level integral; the env-log mount is Kit.Lane's).
- ladder rung: rung 1 — invariants decided/in-the-type; no proof
  family.
- gate row: none yet — Kit is outside Gates.Packages' gated set;
  KitTests pins the allocation + suggestion behavior.
-/

import Lean
import Kit.Correspondence
import TextKit.Suggest

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

/-! ## Code allocation — position-derived, never hand-set -/

/-- Allocate `"{pre}{start+i}"`-style identifiers from list position. -/
def allocateCodes {α : Type} (pre : String) (start : Nat) (items : List α) :
    List (α × String) :=
  items.zipIdx.map (fun (item, i) => (item, s!"{pre}{start + i}"))

/-- Code allocation preserves count — one code per item, always. -/
theorem allocateCodes_length {α : Type} (pre : String) (start : Nat)
    (items : List α) :
    (allocateCodes pre start items).length = items.length := by
  simp [allocateCodes]

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

/-! ## CodedRegistry — the dense code space -/

/-- A named registry with allocated codes: name uniqueness from
    `DataRegistry.nodup`, code collision-freedom from `codesNodup` —
    both proof fields defaulted to `by decide`, so a concrete literal
    carries both invariants BY CONSTRUCTION.

    Deliberately NO `insert`: codes are position-derived, so a mid-list
    insertion would reallocate every later code. Coded registries grow
    by append at the authoring layer. -/
structure CodedRegistry (α : Type) extends DataRegistry α where
  /-- The code prefix (`"E"` for failure modes). -/
  codePrefix : String
  /-- The first code's number; code of item `i` is `s!"{codePrefix}{start + i}"`. -/
  start : Nat
  /-- The allocated codes are distinct. Default discharged by `decide`
      over the concrete items; override with an explicit proof for
      non-concrete item lists. -/
  codesNodup : ((allocateCodes codePrefix start items).map (·.2)).Nodup := by decide

namespace CodedRegistry

/-- The allocated (item, code) pairs, in registration order. -/
def codes (reg : CodedRegistry α) : List (α × String) :=
  allocateCodes reg.codePrefix reg.start reg.items

/-- Code allocation preserves count — one code per item, always. -/
theorem codes_length (reg : CodedRegistry α) :
    reg.codes.length = reg.items.length :=
  allocateCodes_length reg.codePrefix reg.start reg.items

/-- Collision-freedom transported to `codes` (definitionally the raw
    allocation the proof field quantifies over). -/
theorem codes_nodup (reg : CodedRegistry α) :
    (reg.codes.map (·.2)).Nodup :=
  reg.codesNodup

/-- Position injectivity: the position of `items[i]` IS `i` — the
    name-map is nodup (`reg.nodup`), so two positions naming the same
    item are one position. -/
theorem idxOf_getElem_inj [BEq α] [LawfulBEq α] (reg : CodedRegistry α)
    (i : Fin reg.items.length) : reg.items.idxOf reg.items[i.1] = i.1 := by
  have hmem : reg.items[i.1] ∈ reg.items := List.getElem_mem i.2
  have hj := List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)
  have hlen₁ : reg.items.idxOf reg.items[i.1]
      < (reg.items.map reg.nameOf).length := by
    rw [List.length_map]
    exact List.idxOf_lt_length_of_mem hmem
  have hlen₂ : i.1 < (reg.items.map reg.nameOf).length := by
    rw [List.length_map]
    exact i.2
  have hmap? : (reg.items.map reg.nameOf)[reg.items.idxOf reg.items[i.1]]?
      = (reg.items.map reg.nameOf)[i.1]? := by
    rw [List.getElem?_map, List.getElem?_map,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem),
      List.getElem?_eq_getElem i.2, hj]
  exact (List.getElem?_inj hlen₁ reg.nodup).mp hmap?

/-- The executable denseness check: every allocated code, stripped of
    the prefix, parses to exactly `start + position`. -/
def denseCheck (reg : CodedRegistry α) : Bool :=
  reg.codes.zipIdx.all fun c =>
    (c.1.2.drop reg.codePrefix.length).toNat? == some (reg.start + c.2)

/-- Positions ↔ members: name uniqueness makes the position map
    injective, membership total. The `[BEq α]` is for `idxOf` (the
    inverse's lookup). -/
def membersIso [BEq α] [LawfulBEq α] (reg : CodedRegistry α) :
    Iso (Fin reg.items.length) {a // a ∈ reg.items} where
  to i := ⟨reg.items[i.1]'i.2, List.getElem_mem i.2⟩
  inv a := ⟨reg.items.idxOf a.1, List.idxOf_lt_length_of_mem a.2⟩
  to_inv a := Subtype.ext (List.getElem_idxOf (List.idxOf_lt_length_of_mem a.2))
  inv_to i := Fin.ext (idxOf_getElem_inj reg i)

/-- The dense/exhaustive upgrade: when EVERY `a : α` is registered (the
    enum case), the position correspondence is total on α — an honest
    `Iso (Fin n) α`. Fires only when `α` is exhausted by the registry;
    for a non-enum α the honest form is `membersIso`. -/
def finIso [BEq α] [LawfulBEq α] (reg : CodedRegistry α)
    (hex : ∀ a : α, a ∈ reg.items) : Iso (Fin reg.items.length) α where
  to i := reg.items[i.1]'i.2
  inv a := ⟨reg.items.idxOf a, List.idxOf_lt_length_of_mem (hex a)⟩
  to_inv a := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hex a))
  inv_to i := Fin.ext (idxOf_getElem_inj reg i)

end CodedRegistry

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

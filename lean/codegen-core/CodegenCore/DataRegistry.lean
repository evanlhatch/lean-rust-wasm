/-
# CodegenCore.DataRegistry — data-level registry with unique names (W7.16)

Owns: the pure list-of-items registry for driver/runtime code (the
env-extension layer stays in `CodegenCore.Registry`). Deliberately excluded:
no environment, no IO, no attribute layer. Driving decision: name uniqueness
is IN THE TYPE — the `nodup` proof field defaults to `by decide`, so a
duplicate-named literal fails to elaborate; insertion takes freshness as an
argument. Lookup misses carry `didYouMean` suggestions (closed world: errors
enumerate the valid space). Core-only (no mathlib).
-/

module

public import CodegenCore.DidYouMean

@[expose] public section

namespace CodegenCore

/-- A registry of named items with uniqueness IN THE TYPE: `nodup` is a
    proof field whose default discharges by `decide` over the concrete
    items — a duplicate name makes the literal fail to elaborate, which is
    the dup-rejection discipline (there is no runtime path to reject). -/
structure DataRegistry (α : Type) where
  /-- The items, in registration order. -/
  items : List α
  /-- The naming function (names are the lookup keys). -/
  nameOf : α → String
  /-- Names are unique. Default: discharged by `decide`; override with an
    explicit proof for non-concrete item lists (see `insert`). -/
  nodup : (items.map nameOf).Nodup := by decide

namespace DataRegistry

/-- All items, in registration order. -/
def all (reg : DataRegistry α) : List α := reg.items

theorem mem_all {reg : DataRegistry α} {a : α} : a ∈ reg.all ↔ a ∈ reg.items :=
  Iff.rfl

/-- A lookup miss: the requested name plus the nearest registered names
    (the closed-world rule — the suggestions ARE the valid space). -/
structure LookupMiss where
  /-- The name that was requested. -/
  got : String
  /-- The nearest registered names (`CodegenCore.didYouMean`). -/
  didYouMean : List String

/-- Name lookup: the unique item with that name, or a structured miss with
    did-you-mean suggestions over the registered names. -/
def lookup? (reg : DataRegistry α) (name : String) : Except LookupMiss α :=
  match reg.items.find? (fun it => reg.nameOf it == name) with
  | some it => .ok it
  | none => .error { got := name
                     didYouMean := CodegenCore.didYouMean name (reg.items.map reg.nameOf) }

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

/-- Uniqueness transported to the registry: two items with the same name
    are the same item. -/
theorem nameOf_injective (reg : DataRegistry α) {a b : α}
    (ha : a ∈ reg.items) (hb : b ∈ reg.items)
    (heq : reg.nameOf a = reg.nameOf b) : a = b :=
  nodup_map_unique reg.nameOf reg.nodup ha hb heq

/-- A successful lookup returns an item of the registry with the requested
    name. -/
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

/-- A failed lookup is exactly the no-such-name case, and the miss carries
    the requested name plus suggestions over the registered names. -/
theorem lookup?_miss (reg : DataRegistry α) {name : String}
    (h : ∀ a ∈ reg.items, reg.nameOf a ≠ name) :
    reg.lookup? name
      = .error (LookupMiss.mk name
          (CodegenCore.didYouMean name (reg.items.map reg.nameOf))) := by
  have hnone : reg.items.find? (fun it => reg.nameOf it == name) = none :=
    List.find?_eq_none.mpr fun x hx => by
      simp only [beq_iff_eq]
      exact h x hx
  unfold lookup?
  rw [hnone]

/-- Insert a fresh-named item (at the head), preserving uniqueness. The
    freshness obligation is the point: a duplicate name makes `insert`
    uncallable — there is no rejection path because there is no illegal
    state to reject. -/
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

end CodegenCore

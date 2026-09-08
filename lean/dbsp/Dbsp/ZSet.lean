/-
# Dbsp.ZSet — Z-sets (theory side)

A Z-set is a finitely-supported integer multiplicity (`A →₀ ℤ`, mathlib
Finsupp). The group structure is what licenses the delta architecture:
negation is rollback, union is composition, and incremental≡batch is the
theorem family over it.

The EXEC side is flatland's Change (lean/Flatland/Flatland/Change.lean —
proved merge/revert laws); the bridge between them is an Abstraction
(Machines.Foundations). Per lean-v3 Part 3: theory on Finsupp (the port
stays faithful), execution on our sorted-canonical representation.

The lower half (`/-! ## Supporting API -/`) ports the parts of
`src/zset.lean` that the relational operators (Dbsp/Relational.lean) need:
membership, multiplicity lemmas, `ZSet.fromSet`/`ZSet.toSet`, single-element sets,
`ZSet.funPositive`/`ZSet.funPositive2`, and the `ZSet.map` machinery with its positivity
and support lemmas. The source's `flatmap` is not ported: in mathlib
`zset.map f = Finsupp.mapDomain f` is exactly `flatmap (λ a, {f a})`, so we
go straight to `mapDomain` (its sum-over-support expansion is `ZSet.map_apply`).
-/

import Dbsp.Tactics
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.NormNum

namespace Dbsp

/-- Z-sets over `A`: finitely-supported ℤ multiplicities. The AddCommGroup
    instance comes from mathlib. -/
abbrev ZSet (A : Type) : Type := A →₀ ℤ

/-- A set-like Z-set: every present element has multiplicity 1. -/
def ZSet.isSet (m : ZSet A) : Prop := ∀ a ∈ m.support, m a = 1

/-- A bag: no negative multiplicities. -/
def ZSet.isBag (m : ZSet A) : Prop := ∀ a, 0 ≤ m a

/-- Threshold to a set: keep present elements at multiplicity 1.
    Non-linear — its incremental form needs old state
    (`distinct_incremental_ok`; the old_values requirement is a theorem,
    not an optimization — SPEC-core §7.3). -/
-- noncomputable: mathlib's Finsupp.mapRange quotients with classical choice.
-- Fine here — this is the THEORY layer; execution lives in Flatland.Change.
noncomputable def ZSet.distinct (m : ZSet A) : ZSet A :=
  m.mapRange (fun w => if 0 < w then 1 else 0) (by simp)

/-! ## Supporting API (ported from `src/zset.lean`) -/

noncomputable section
open Classical
open scoped BigOperators

variable {A B : Type}

/-- Membership: `a ∈ m` means `a` is in the support, i.e. the multiplicity of
    `a` in `m` is nonzero (the source's `zset_mem`). -/
instance instMem : Membership A (ZSet A) := ⟨fun (m : ZSet A) (a : A) => a ∈ m.support⟩

/-- mp stands for multiplicity; the result of applying a zset to an element. -/
theorem ZSet.elem_mp {m : ZSet A} {a : A} : a ∈ m ↔ m a ≠ 0 := by
  change a ∈ m.support ↔ m a ≠ 0
  exact Finsupp.mem_support_iff

theorem ZSet.notElem_mp {m : ZSet A} {a : A} : a ∉ m ↔ m a = 0 := by
  change ¬a ∈ m.support ↔ m a = 0
  rw [Finsupp.mem_support_iff]
  constructor <;> intro h <;> simpa using h

/-- A zset is a set exactly when every multiplicity is 0 or 1 (source
    `is_set_or`). -/
theorem ZSet.isSetOr (s : ZSet A) : ZSet.isSet s ↔ ∀ a, s a = 0 ∨ s a = 1 := by
  unfold ZSet.isSet
  constructor
  · intro h a
    by_cases hamem : a ∈ s
    · right
      exact h a (by change a ∈ s.support at hamem; exact hamem)
    · left
      exact (ZSet.notElem_mp.mp hamem)
  · intro h a hamem
    rcases h a with h0 | h1
    · exfalso
      exact ((Finsupp.mem_support_iff).mp (by change a ∈ s.support at hamem; exact hamem)) h0
    · exact h1

/-- Sets are bags (source `set_is_bag`). -/
theorem ZSet.setIsBag (s : ZSet A) : ZSet.isSet s → ZSet.isBag s := by
  intro hset a
  rcases (ZSet.isSetOr s).mp hset a with h0 | h1
  · rw [h0]
  · rw [h1]
    exact zero_le_one

/-- The value of `distinct` at an element (multiplicity 1 iff present). -/
@[simp, zset] theorem ZSet.distinct_apply (m : ZSet A) (a : A) :
    (ZSet.distinct m) a = if 0 < m a then 1 else 0 := by
  simp [ZSet.distinct]

/-- A singleton Z-set (the source's `zset.single`). -/
instance instSingleton : Singleton A (ZSet A) := ⟨fun a => Finsupp.single a 1⟩

@[simp, zset] theorem ZSet.single_apply (a a' : A) : ({a} : ZSet A) a' = if a = a' then 1 else 0 := by
  exact Finsupp.single_apply

@[simp] theorem ZSet.elem_single (a x : A) : x ∈ ({a} : ZSet A) ↔ a = x := by
  rw [ZSet.elem_mp, ZSet.single_apply]
  by_cases h : a = x <;> simp [h]

@[simp] theorem ZSet.support_single (a : A) : ({a} : ZSet A).support = ({a} : Finset A) := by
  ext x
  rw [Finsupp.mem_support_iff, ZSet.single_apply]
  by_cases h : a = x
  · subst h; simp
  · rw [if_neg h]; simp [Ne.symm h]

/-- A finset as a Z-set: every element has multiplicity 1 (the source's
    `zset.from_set`, via the `dfinsupp.mk`-analog `Finsupp.indicator`). -/
noncomputable def ZSet.fromSet (s : Finset A) : ZSet A := Finsupp.indicator s (fun _ _ => (1 : ℤ))

@[simp] theorem ZSet.fromSet_apply (s : Finset A) (a : A) :
    (ZSet.fromSet s) a = if a ∈ s then 1 else 0 := by
  rw [ZSet.fromSet]
  rw [Finsupp.indicator_apply]
  by_cases h : a ∈ s <;> simp [h]

@[simp] theorem ZSet.fromSet_support (s : Finset A) : (ZSet.fromSet s).support = s := by
  ext a
  rw [Finsupp.mem_support_iff, ZSet.fromSet_apply]
  by_cases h : a ∈ s <;> simp [h]

@[simp] theorem ZSet.elem_fromSet (a : A) (s : Finset A) : a ∈ ZSet.fromSet s ↔ a ∈ s := by
  rw [ZSet.elem_mp, ZSet.fromSet_apply]
  by_cases h : a ∈ s <;> simp [h]

/-- The finset of present elements of a Z-set (the source's `zset.to_set`). -/
def ZSet.toSet (m : ZSet A) : Finset A := m.support

@[simp] theorem ZSet.elem_toSet (a : A) (m : ZSet A) : a ∈ ZSet.toSet m ↔ a ∈ m := by
  rw [ZSet.elem_mp]
  change a ∈ m.support ↔ m a ≠ 0
  exact Finsupp.mem_support_iff

/-- Positive-input-to-positive-output predicate on functions (source
    `fun_positive`). -/
def ZSet.funPositive (f : ZSet A → ZSet B) : Prop := ∀ m, ZSet.isBag m → ZSet.isBag (f m)

/-- The two-input version (source `fun_positive2`), used for joins. -/
def ZSet.funPositive2 (f : ZSet A → ZSet B → ZSet C) : Prop :=
  ∀ m1 m2, ZSet.isBag m1 → ZSet.isBag m2 → ZSet.isBag (f m1 m2)

/-- Lifting a function on the domain, summing multiplicities — the source's
    `zset.map`, implemented as `Finsupp.mapDomain` (which equals
    `flatmap (λ a, {f a})`). -/
def ZSet.map (f : A → B) (m : ZSet A) : ZSet B := Finsupp.mapDomain f m

/-- The value of `ZSet.map f m` at `b` is the sum of the multiplicities of the
    preimages of `b` (the source's `flatmap_at`/`ZSet.map_apply` for the ZSet.map). -/
theorem ZSet.map_apply (f : A → B) (m : ZSet A) (b : B) :
    ZSet.map f m b = m.support.sum (fun a => if f a = b then m a else 0) := by
  rw [ZSet.map, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp [Finsupp.single_apply]

/-- `ZSet.map` is linear (mathlib's `mapDomain_add`). -/
theorem ZSet.map_linear (f : A → B) (m1 m2 : ZSet A) :
    ZSet.map f (m1 + m2) = ZSet.map f m1 + ZSet.map f m2 := by
  unfold ZSet.map
  exact (Finsupp.mapDomain_add (f := f) (v₁ := m1) (v₂ := m2))

/-- Pointwise nonnegativity of `ZSet.map` on bags (used by `map_pos`). -/
theorem ZSet.map_at_nonneg (f : A → B) (m : ZSet A) (b : B) :
    ZSet.isBag m → 0 ≤ ZSet.map f m b := by
  intro hpos
  rw [ZSet.map_apply]
  exact Finset.sum_nonneg (by
    intro a ha
    by_cases h : f a = b <;> simp [h, hpos a])

/-- `ZSet.map f m b > 0` iff some element of `m` maps to `b` (the source's
    `ZSet.map_at_pos`, rephrased over `mapDomain`). -/
theorem ZSet.map_at_pos (f : A → B) (m : ZSet A) (b : B) :
    ZSet.isBag m → (0 < ZSet.map f m b ↔ ∃ a, a ∈ m ∧ f a = b) := by
  intro hpos
  constructor
  · intro h
    by_contra hn
    have hnz : ZSet.map f m b = 0 := by
      rw [ZSet.map_apply]
      exact Finset.sum_eq_zero (by
        intro a ha
        by_cases hfab : f a = b
        · have hamem_not : a ∉ m := by
            intro hamem
            exact hn ⟨a, hamem, hfab⟩
          have hmz : m a = 0 := ZSet.notElem_mp.mp hamem_not
          simp [hfab, hmz]
        · simp [hfab])
    rw [hnz] at h
    exact (not_lt_of_ge (le_refl (0 : ℤ))) h
  · intro hex
    rcases hex with ⟨a, hamem, hfab⟩
    rw [ZSet.map_apply]
    apply Finset.sum_pos'
    · intro x hx
      by_cases hxb : f x = b <;> simp [hxb, hpos x]
    · refine ⟨a, Finsupp.mem_support_iff.mpr (ZSet.elem_mp.mp hamem), ?_⟩
      have hia : 0 < m a := lt_of_le_of_ne (hpos a) (Ne.symm (ZSet.elem_mp.mp hamem))
      simp [hfab, hia]

/-- When `f` kills every preimage of `b` in `i` (a bag), `ZSet.map f (distinct i) b`
    vanishes (the source's private `ZSet.map_at_distinct_none`). -/
theorem ZSet.map_at_distinct_none (f : A → B) (i : ZSet A) (b : B) :
    ZSet.isBag i →
    (∀ a, a ∈ i → f a ≠ b) →
    ZSet.map f (ZSet.distinct i) b = 0 := by
  intro hpos h
  rw [ZSet.map_apply]
  exact Finset.sum_eq_zero (by
    intro x hx
    -- x ∈ (distinct i).support, so i x > 0 and hence x ∈ i
    have hxi : 0 < i x := by
      have hx0 : (ZSet.distinct i) x ≠ 0 := (Finsupp.mem_support_iff.mp hx)
      rw [ZSet.distinct_apply] at hx0
      by_contra hni
      simp [hni] at hx0
    have hxmem : x ∈ i := (ZSet.elem_mp.mpr (Ne.symm hxi.ne))
    have hfx : f x ≠ b := h x hxmem
    by_cases hxb : f x = b
    · exfalso
      exact hfx hxb
    · simp [hxb])

end

end Dbsp

attribute [zset] Finsupp.add_apply Finsupp.sub_apply Finsupp.neg_apply Finsupp.zero_apply

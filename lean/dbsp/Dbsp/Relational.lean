/-
# Dbsp.Relational — the relational operators over Z-sets

Ports tchajed/database-stream-processing-theory `src/relational.lean`
(Lean 3) to Lean 4 (notes/lean/lean-v3.md Part 3), over the mathlib
`Finsupp` Z-sets of `Dbsp.ZSet`.

The operators: `union`, `map`, `filter`, `product`, `equiJoin`
(equi-join), `intersect`, `difference`, `groupBy`, plus `Query` (a stream
operator over Z-sets). The `_ok` theorems relate the operators to plain
finset semantics via `fromSet`/`toSet`; the `_pos` theorems say bags stay
bags; the `_linear`/`_bilinear` theorems license incrementalization; and
the `distinct_*` family are the deduplication rewrite licenses the
incremental distinct-of-operator computations need.

Deviations from the source (all likewise true in Lean 3's `dfinsupp`):

- The source's `def query A B := operator Z[A] Z[B]` becomes
  `abbrev Query A B := Operator (ZSet A) (ZSet B)`.
- The source's `filter` is built on `Finsupp.filter` (postfix `m.filter p`);
  its support/apply/linearity lemmas are the mathlib ones.
- `group_by`'s coding target `Π₀ (_: K), Z[A]` is `K →₀ ZSet A`; the outer
  support/apply theorems are proved by construction.
- The source's `distinct_set_simp`/`distinct_bag_simp` (`↔ true` simp
  lemmas) are not ported — they are rendering sugar, not used anywhere.
- The `fun_positive`/`fun_positive2`/`elem_mp`/`isSet_or`/`set_is_bag`
  machinery lives in `Dbsp.ZSet` (the `src/zset.lean` port).
- The source's `zset.map`/flatmap machinery is `Finsupp.mapDomain`, in
  `Dbsp.ZSet`; `map_at_pos`/`map_at_distinct_none` are spelled over it.

All `_ok` theorems need `[DecidableEq]` on the sorts involved, exactly as
in the source; `fromSet`/`toSet` are the finset↔zset bridge.
-/

import Dbsp.ZSet
import Dbsp.Linear
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace Dbsp

noncomputable section
open Classical
open scoped BigOperators

variable {A B C : Type}
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-! ## Queries -/

/-- A stream operator over Z-sets (the source's `query`). -/
abbrev Query (A B : Type) := Operator (ZSet A) (ZSet B)

namespace ZSet

/-! ## Distinct -/

theorem distinct_isSet (m : ZSet A) : ZSet.isSet (ZSet.distinct m) := by
  intro a ha
  rw [ZSet.distinct_apply]
  rw [Finsupp.mem_support_iff, ZSet.distinct_apply] at ha
  by_cases hm : 0 < m a
  · simp [hm]
  · exfalso
    exact ha (by simp [hm])

theorem distinct_isBag (m : ZSet A) : ZSet.isBag (ZSet.distinct m) :=
  ZSet.setIsBag _ (ZSet.distinct_isSet m)

/-- Distinct of a set is the set itself. -/
theorem distinct_set_id (m : ZSet A) : ZSet.isSet m → ZSet.distinct m = m := by
  intro h
  ext a
  rcases (ZSet.isSetOr m).mp h a with hma0 | hma1
  · simp [ZSet.distinct_apply, hma0]
  · simp [ZSet.distinct_apply, hma1]

/-- For a bag, distinct preserves membership. -/
theorem distinct_elem {m : ZSet A} {a : A} :
    ZSet.isBag m → (a ∈ ZSet.distinct m ↔ a ∈ m) := by
  intro hpos
  rw [ZSet.elem_mp, ZSet.elem_mp]
  rw [ZSet.distinct_apply]
  by_cases hm : m a = 0
  · rw [hm]
    simp
  · have hgt : 0 < m a := lt_of_le_of_ne (hpos a) (Ne.symm hm)
    simp [hgt, hm]

/-- Distinct is positive (bags to bags). -/
theorem distinct_pos : ZSet.funPositive (fun m : ZSet A => ZSet.distinct m) := by
  intro m hm a
  by_cases h : 0 < m a <;> simp [ZSet.distinct_apply, h]

@[simp]
theorem distinct_0 : ZSet.distinct (0 : ZSet A) = 0 := by
  ext a
  simp [ZSet.distinct_apply]

/-- Distinct is idempotent. -/
theorem distinct_idem (i : ZSet A) : ZSet.distinct (ZSet.distinct i) = ZSet.distinct i := by
  ext a
  by_cases h : 0 < i a <;> simp [ZSet.distinct_apply, h] <;> norm_num

/-! ## Union -/

/-- Union is distinct of the sum (so duplicates collapse). -/
def union (m1 m2 : ZSet A) : ZSet A := ZSet.distinct (m1 + m2)

instance instUnion : Union (ZSet A) := ⟨ZSet.union⟩

theorem union_eq (m1 m2 : ZSet A) : m1 ∪ m2 = ZSet.union m1 m2 := rfl

@[simp]
theorem union_apply (m1 m2 : ZSet A) (a : A) :
    ZSet.union m1 m2 a = if 0 < m1 a + m2 a then 1 else 0 := by
  show ZSet.distinct (m1 + m2) a = _
  rw [ZSet.distinct_apply, Finsupp.add_apply]

/-- Union reflects finset union through `fromSet`. -/
theorem union_ok (s1 s2 : Finset A) :
    ZSet.toSet (ZSet.union (ZSet.fromSet s1) (ZSet.fromSet s2)) = s1 ∪ s2 := by
  ext a
  rw [ZSet.elem_toSet, ZSet.elem_mp, Finset.mem_union, union_apply]
  by_cases h1 : a ∈ s1 <;> by_cases h2 : a ∈ s2 <;>
    simp [ZSet.fromSet_apply, h1, h2]

theorem union_pos : ZSet.funPositive2 (fun m1 m2 : ZSet A => ZSet.union m1 m2) := by
  intro m1 m2 h1 h2 a
  rw [ZSet.union_apply]
  split_ifs <;> simp

/-! ## Map -/

/-- The value of `map f (fromSet s)` at `b` is the size of the preimage. -/
theorem map_is_card (f : A → B) (s : Finset A) (b : B) :
    ZSet.map f (ZSet.fromSet s) b = (s.filter (fun a => f a = b)).card := by
  rw [ZSet.map_apply, ZSet.fromSet_support]
  trans (∑ a ∈ s, if f a = b then (1 : ℤ) else 0)
  · refine Finset.sum_congr rfl ?_
    intro a ha
    simp [ZSet.fromSet_apply, ha]
  · rw [Finset.card_filter]
    simp

/-- Map reflects finset image through `fromSet`. -/
theorem map_ok (f : A → B) (s : Finset A) :
    (ZSet.map f (ZSet.fromSet s)).support = s.image f := by
  ext b
  rw [Finsupp.mem_support_iff, map_is_card f s b]
  constructor
  · intro h
    rw [Nat.cast_ne_zero (R := ℤ), ← Nat.pos_iff_ne_zero, Finset.card_pos] at h
    obtain ⟨a, ha, rfl⟩ := Finset.filter_nonempty_iff.mp h
    exact Finset.mem_image_of_mem f ha
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    rw [Nat.cast_ne_zero (R := ℤ), ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact Finset.filter_nonempty_iff.mpr ⟨a, ha, rfl⟩

theorem map_pos (f : A → B) : ZSet.funPositive (ZSet.map f) := by
  intro m hm b
  exact ZSet.map_at_nonneg f m b hm

/-! ## Filter -/

section filter
variable (p : A → Prop) [DecidablePred p]

/-- Keep the elements satisfying `p`, multiplicities unchanged. -/
def filter (p : A → Prop) [DecidablePred p] (m : ZSet A) : ZSet A := Finsupp.filter p m

@[simp]
lemma filter_apply (m : ZSet A) (a : A) : ZSet.filter p m a = if p a then m a else 0 := rfl

@[simp]
lemma filter_support (m : ZSet A) : (ZSet.filter p m).support = m.support.filter p := rfl

theorem filter_ok (s : Finset A) :
    ZSet.toSet (ZSet.filter p (ZSet.fromSet s)) = s.filter p := by
  ext a
  rw [ZSet.elem_toSet]
  show a ∈ (ZSet.filter p (ZSet.fromSet s)).support ↔ a ∈ s.filter p
  rw [Finsupp.mem_support_iff, Finset.mem_filter]
  by_cases hpa : p a <;> by_cases has : a ∈ s <;>
    simp [ZSet.filter_apply, ZSet.fromSet_apply, hpa, has]

theorem filter_linear (m1 m2 : ZSet A) :
    ZSet.filter p (m1 + m2) = ZSet.filter p m1 + ZSet.filter p m2 := by
  unfold ZSet.filter
  exact Finsupp.filter_add

theorem filter_pos : ZSet.funPositive (ZSet.filter p) := by
  intro m hm a
  by_cases hpa : p a <;> simp [ZSet.filter_apply, hpa, hm a]

theorem filter_0 : ZSet.filter p 0 = 0 := by
  ext a
  simp [ZSet.filter_apply]

end filter

/-! ## Product -/

section product

/-- The cartesian product: multiplicities multiply (source `product`). -/
def product (m1 : ZSet A) (m2 : ZSet B) : ZSet (A × B) :=
  { support := m1.support.product m2.support,
    toFun := fun ab => m1 ab.1 * m2 ab.2,
    mem_support_toFun := by
      intro ab
      change ab ∈ m1.support ×ˢ m2.support ↔ m1 ab.1 * m2 ab.2 ≠ 0
      rw [Finset.mem_product]
      rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      exact Iff.symm (mul_ne_zero_iff (M₀ := ℤ)) }

@[simp]
theorem product_apply (m1 : ZSet A) (m2 : ZSet B) (ab : A × B) :
    product m1 m2 ab = m1 ab.1 * m2 ab.2 := rfl

theorem product_ok (s1 : Finset A) (s2 : Finset B) :
    ZSet.toSet (product (ZSet.fromSet s1) (ZSet.fromSet s2)) = s1.product s2 := by
  ext ab
  cases ab with
  | mk a b =>
    rw [ZSet.elem_toSet]
    show (a, b) ∈ (product (ZSet.fromSet s1) (ZSet.fromSet s2)).support ↔ _
    rw [Finsupp.mem_support_iff]
    have hmem : ((a, b) ∈ s1.product s2) = (a ∈ s1 ∧ b ∈ s2) := propext Finset.mem_product
    rw [hmem, product_apply, ZSet.fromSet_apply, ZSet.fromSet_apply]
    by_cases has1 : a ∈ s1 <;> by_cases has2 : b ∈ s2 <;>
      simp [has1, has2]

theorem product_bilinear : Bilinear (@ZSet.product A B) := by
  constructor
  · intro x1 x2 y
    ext ab <;> cases ab with
    | mk a b => simp; ring
  · intro x y1 y2
    ext ab <;> cases ab with
    | mk a b => simp; ring

theorem product_pos : ZSet.funPositive2 (@ZSet.product A B) := by
  intro m1 m2 hpos1 hpos2 ab
  cases ab with
  | mk a b =>
    rw [ZSet.product_apply]
    exact mul_nonneg (hpos1 a) (hpos2 b)

@[simp]
theorem product_0 : ZSet.product (0 : ZSet A) (0 : ZSet B) = 0 := by
  ext ab
  simp

section equi_join

variable (π1 : A → C) (π2 : B → C)

/-- The equi-join on projections `π1`, `π2`: the filtered product. -/
def equiJoin (m1 : ZSet A) (m2 : ZSet B) : ZSet (A × B) :=
  ZSet.filter (fun t : A × B => π1 t.1 = π2 t.2) (ZSet.product m1 m2)

@[simp]
theorem equiJoin_apply (m1 : ZSet A) (m2 : ZSet B) (t : A × B) :
    equiJoin π1 π2 m1 m2 t = if π1 t.1 = π2 t.2 then m1 t.1 * m2 t.2 else 0 := by
  simp [ZSet.equiJoin, ZSet.filter_apply]

theorem equiJoin_bilinear : Bilinear (ZSet.equiJoin π1 π2) := by
  constructor
  · intro x1 x2 y
    unfold ZSet.equiJoin
    rw [product_bilinear.1, filter_linear]
  · intro x y1 y2
    unfold ZSet.equiJoin
    rw [product_bilinear.2, filter_linear]

theorem equiJoin_pos : ZSet.funPositive2 (ZSet.equiJoin π1 π2) := by
  intro m1 m2 hpos1 hpos2
  show ZSet.isBag (ZSet.filter (fun t : A × B => π1 t.1 = π2 t.2) (ZSet.product m1 m2))
  exact ZSet.filter_pos _ _ (ZSet.product_pos _ _ hpos1 hpos2)

@[simp]
theorem equiJoin_0_l (b : ZSet B) : equiJoin π1 π2 0 b = 0 := by
  ext ab
  simp

@[simp]
theorem equiJoin_0_r (a : ZSet A) : equiJoin π1 π2 a 0 = 0 := by
  ext ab
  simp

end equi_join

end product

/-! ## Intersection -/

-- TODO: the paper says intersection can be defined as a special case of an
-- equijoin, but that construction requires projecting A × A → A (where both
-- are equal due to the filter), and it's not obvious that projection preserves
-- bilinearity. The direct definition is straightforward.

/-- Intersection: pointwise product of multiplicities (source `intersect`). -/
def intersect (m1 m2 : ZSet A) : ZSet A :=
  { support := m1.support ∩ m2.support,
    toFun := fun a => m1 a * m2 a,
    mem_support_toFun := by
      intro a
      rw [Finset.mem_inter]
      rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      exact Iff.symm (mul_ne_zero_iff (M₀ := ℤ)) }

instance instInter : Inter (ZSet A) := ⟨ZSet.intersect⟩

@[simp]
theorem intersect_apply (m1 m2 : ZSet A) (a : A) : (m1 ∩ m2) a = m1 a * m2 a := rfl

@[simp]
theorem intersect_0 : (0 : ZSet A) ∩ 0 = 0 := by
  ext a
  simp

@[simp]
theorem intersect_support (m1 m2 : ZSet A) : (m1 ∩ m2).support = m1.support ∩ m2.support := rfl

theorem intersect_ok (s1 s2 : Finset A) :
    ZSet.toSet (ZSet.fromSet s1 ∩ ZSet.fromSet s2) = s1 ∩ s2 := by
  ext a
  rw [ZSet.elem_toSet]
  show a ∈ (ZSet.fromSet s1 ∩ ZSet.fromSet s2).support ↔ _
  rw [Finsupp.mem_support_iff, Finset.mem_inter]
  show (ZSet.fromSet s1 ∩ ZSet.fromSet s2) a ≠ 0 ↔ _
  rw [ZSet.intersect_apply, ZSet.fromSet_apply, ZSet.fromSet_apply]
  by_cases has1 : a ∈ s1 <;> by_cases has2 : a ∈ s2 <;> simp [has1, has2]

theorem intersect_pos : ZSet.funPositive2 (fun m1 m2 : ZSet A => m1 ∩ m2) := by
  intro m1 m2 hpos1 hpos2 a
  rw [ZSet.intersect_apply]
  exact mul_nonneg (hpos1 a) (hpos2 a)

theorem intersect_bilinear : Bilinear (fun m1 m2 : ZSet A => m1 ∩ m2) := by
  constructor
  · intro x1 x2 y
    ext a
    simp [ZSet.intersect_apply]
    ring
  · intro x y1 y2
    ext a
    simp [ZSet.intersect_apply]
    ring

/-! ## Difference -/

/-- Difference: distinct of the subtraction (source `difference`). -/
def difference (m1 m2 : ZSet A) : ZSet A := ZSet.distinct (m1 - m2)

theorem difference_ok (s1 s2 : Finset A) :
    ZSet.toSet (ZSet.difference (ZSet.fromSet s1) (ZSet.fromSet s2)) = s1 \ s2 := by
  ext a
  rw [ZSet.elem_toSet]
  show a ∈ (ZSet.difference (ZSet.fromSet s1) (ZSet.fromSet s2)).support ↔ _
  rw [Finsupp.mem_support_iff, Finset.mem_sdiff]
  show ZSet.distinct (ZSet.fromSet s1 - ZSet.fromSet s2) a ≠ 0 ↔ _
  rw [ZSet.distinct_apply, Finsupp.sub_apply, ZSet.fromSet_apply, ZSet.fromSet_apply]
  by_cases has1 : a ∈ s1 <;> by_cases has2 : a ∈ s2 <;>
    simp [has1, has2]

/-! ## Group by -/

section group_by

variable {K : Type} [DecidableEq K] (p : A → K)

/-- Group by key: `groupBy p m k` is the fiber of `m` over the key `k`
    (source `group_by`; the coding target `Π₀ (_: K), Z[A]` is
    `K →₀ ZSet A`). -/
def groupBy (m : ZSet A) : K →₀ ZSet A :=
  { support := m.support.image p,
    toFun := fun k => ZSet.filter (fun a => p a = k) m,
    mem_support_toFun := by
      intro k
      constructor
      · intro hk
        rcases Finset.mem_image.mp hk with ⟨a, ha, hpa⟩
        rw [Finsupp.ne_iff]
        exact ⟨a, by
          rw [ZSet.filter_apply, if_pos hpa]
          exact (Finsupp.mem_support_iff.mp ha)⟩
      · intro hf
        rw [Finsupp.ne_iff] at hf
        rcases hf with ⟨a, ha⟩
        rw [ZSet.filter_apply] at ha
        by_cases hpa : p a = k
        · exact Finset.mem_image.mpr ⟨a, (Finsupp.mem_support_iff.mpr (by simpa [hpa] using ha)), hpa⟩
        · exact False.elim (by simpa [hpa] using ha) }

@[simp]
theorem groupBy_apply (m : ZSet A) (k : K) (a : A) :
    groupBy p m k a = if p a = k then m a else 0 := by
  simp [ZSet.groupBy, ZSet.filter_apply]

theorem groupBy_support (m : ZSet A) (k : K) :
    (groupBy p m k).support = m.support.filter (fun a => p a = k) := by
  rfl

theorem elem_groupBy (m : ZSet A) (k : K) (a : A) :
    a ∈ groupBy p m k ↔ p a = k ∧ a ∈ m := by
  rw [ZSet.elem_mp, ZSet.elem_mp]
  by_cases hpa : p a = k <;> simp [ZSet.groupBy_apply, hpa]

theorem groupBy_linear (m1 m2 : ZSet A) :
    groupBy p (m1 + m2) = groupBy p m1 + groupBy p m2 := by
  ext k a
  simp [ZSet.groupBy_apply]
  by_cases hpa : p a = k <;> simp [hpa]

end group_by

/-! ## A few properties about `distinct` -/

@[simp]
theorem ite_ite {c1 : Prop} [Decidable c1] {c2 : Prop} [Decidable c2] (x z : A) :
    (if c1 then (if c2 then x else z) else z) = if c1 ∧ c2 then x else z := by
  by_cases hc1 : c1 <;> by_cases hc2 : c2 <;> simp [hc1, hc2]

/-- Filtering commutes with distinct (no `is_bag` hypothesis needed). -/
theorem filter_distinct_comm (p : A → Prop) [DecidablePred p] (i : ZSet A) :
    ZSet.filter p (ZSet.distinct i) = ZSet.distinct (ZSet.filter p i) := by
  ext a
  by_cases hpa : p a <;> simp [ZSet.filter_apply, ZSet.distinct_apply, hpa]

theorem product_distinct_comm (i1 : ZSet A) (i2 : ZSet B) :
    ZSet.isBag i1 → ZSet.isBag i2 →
    ZSet.product (ZSet.distinct i1) (ZSet.distinct i2) = ZSet.distinct (ZSet.product i1 i2) := by
  intro hpos1 hpos2
  ext ab <;> cases ab with
  | mk a b =>
    simp only [product_apply, distinct_apply, mul_ite, mul_one, mul_zero, ite_ite]
    have h1 : 0 ≤ i1 a := hpos1 a
    have h2 : 0 ≤ i2 b := hpos2 b
    by_cases h1p : 0 < i1 a <;> by_cases h2p : 0 < i2 b
    · have hmul : 0 < i1 a * i2 b := mul_pos h1p h2p
      simp [h1p, h2p, hmul] <;> norm_num
    · have h2z : i2 b = 0 := le_antisymm (le_of_not_gt h2p) h2
      simp [h1p, h2z]
    · have h1z : i1 a = 0 := le_antisymm (le_of_not_gt h1p) h1
      simp [h2p, h1z]
    · have h1z : i1 a = 0 := le_antisymm (le_of_not_gt h1p) h1
      have h2z : i2 b = 0 := le_antisymm (le_of_not_gt h2p) h2
      simp [h1z, h2z]

theorem join_distinct_comm (π1 : A → C) (π2 : B → C) (i1 : ZSet A) (i2 : ZSet B) :
    ZSet.isBag i1 → ZSet.isBag i2 →
    ZSet.equiJoin π1 π2 (ZSet.distinct i1) (ZSet.distinct i2) = ZSet.distinct (ZSet.equiJoin π1 π2 i1 i2) := by
  intro hpos1 hpos2
  unfold ZSet.equiJoin
  rw [ZSet.product_distinct_comm _ _ hpos1 hpos2]
  rw [ZSet.filter_distinct_comm (p := fun t : A × B => π1 t.1 = π2 t.2)]

theorem intersect_distinct_comm (i1 i2 : ZSet A) :
    ZSet.isBag i1 → ZSet.isBag i2 →
    ZSet.distinct i1 ∩ ZSet.distinct i2 = ZSet.distinct (i1 ∩ i2) := by
  intro hpos1 hpos2
  ext a
  simp only [intersect_apply, distinct_apply, mul_ite, mul_one, mul_zero, ite_ite]
  have h1 : 0 ≤ i1 a := hpos1 a
  have h2 : 0 ≤ i2 a := hpos2 a
  by_cases h1p : 0 < i1 a <;> by_cases h2p : 0 < i2 a
  · have hmul : 0 < i1 a * i2 a := mul_pos h1p h2p
    simp [h1p, h2p, hmul] <;> norm_num
  · have h2z : i2 a = 0 := le_antisymm (le_of_not_gt h2p) h2
    simp [h1p, h2z]
  · have h1z : i1 a = 0 := le_antisymm (le_of_not_gt h1p) h1
    simp [h2p, h1z]
  · have h1z : i1 a = 0 := le_antisymm (le_of_not_gt h1p) h1
    have h2z : i2 a = 0 := le_antisymm (le_of_not_gt h2p) h2
    simp [h1z, h2z]

/-- Distinct commutes with `map` when the function is injective (source
    `map_inj_distinct_comm`). -/
theorem map_inj_distinct_comm (f : A → B) (hf : Function.Injective f) (i : ZSet A) :
    ZSet.isBag i →
    ZSet.distinct (ZSet.map f i) = ZSet.map f (ZSet.distinct i) := by
  intro hpos
  ext b
  by_cases hgt : 0 < ZSet.map f i b
  · have hex := (ZSet.map_at_pos f i b hpos).mp hgt
    rcases hex with ⟨a, hai, hfab⟩
    have hia : 0 < i a := lt_of_le_of_ne (hpos a) (Ne.symm (ZSet.elem_mp.mp hai))
    have hda : (ZSet.distinct i) a = 1 := by
      rw [ZSet.distinct_apply, if_pos hia]
    have haS : a ∈ (ZSet.distinct i).support := by
      rw [Finsupp.mem_support_iff, hda]
      simp
    rw [ZSet.distinct_apply, if_pos hgt]
    rw [ZSet.map_apply]
    rw [Finset.sum_eq_single a]
    · rw [if_pos hfab, hda]
    · intro x hx hxa
      have hxmem : x ∈ i := by
        have hx0 : (ZSet.distinct i) x ≠ 0 := (Finsupp.mem_support_iff.mp hx)
        have hxi : 0 < i x := by
          rw [ZSet.distinct_apply] at hx0
          by_contra hni
          simp [hni] at hx0
        exact (ZSet.elem_mp.mpr hxi.ne')
      have hfx : f x ≠ b := by
        intro hxb
        exact hxa (hf (by rw [hxb, hfab]))
      by_cases hxb : f x = b
      · exfalso
        exact hfx hxb
      · simp [hxb]
    · intro hna
      exfalso
      exact hna haS
  · rw [ZSet.distinct_apply, if_neg hgt]
    symm
    apply ZSet.map_at_distinct_none f i b hpos
    intro a hai hfa
    exact hgt ((ZSet.map_at_pos f i b hpos).mpr ⟨a, hai, hfa⟩)

theorem filter_distinct_dedup (p : A → Prop) [DecidablePred p] (i : ZSet A) :
    ZSet.distinct (ZSet.filter p (ZSet.distinct i)) = ZSet.distinct (ZSet.filter p i) := by
  rw [ZSet.filter_distinct_comm, ZSet.distinct_idem]

theorem map_distinct_dedup (f : A → B) (i : ZSet A) :
    ZSet.isBag i →
    ZSet.distinct (ZSet.map f (ZSet.distinct i)) = ZSet.distinct (ZSet.map f i) := by
  intro hpos
  ext b
  apply if_congr
  · rw [ZSet.map_at_pos f (ZSet.distinct i) b (ZSet.distinct_pos i hpos)]
    rw [ZSet.map_at_pos f i b hpos]
    exact exists_congr (fun a => by rw [ZSet.distinct_elem hpos])
  · simp
  · simp

theorem add_distinct_dedup (i1 i2 : ZSet A) :
    ZSet.isBag i1 → ZSet.isBag i2 →
    ZSet.distinct (ZSet.distinct i1 + ZSet.distinct i2) = ZSet.distinct (i1 + i2) := by
  intro hpos1 hpos2
  ext a
  simp [ZSet.distinct_apply]
  have h1 : 0 ≤ i1 a := hpos1 a
  have h2 : 0 ≤ i2 a := hpos2 a
  by_cases h1p : 0 < i1 a <;> by_cases h2p : 0 < i2 a
  · have hsum : 0 < i1 a + i2 a := add_pos h1p h2p
    simp [h1p, h2p, hsum] <;> norm_num
  · have h2z : i2 a = 0 := le_antisymm (le_of_not_gt h2p) h2
    simp [h1p, h2z]
  · have h1z : i1 a = 0 := le_antisymm (le_of_not_gt h1p) h1
    simp [h2p, h1z]
  · have h1z : i1 a = 0 := le_antisymm (le_of_not_gt h1p) h1
    have h2z : i2 a = 0 := le_antisymm (le_of_not_gt h2p) h2
    simp [h1z, h2z]

theorem product_distinct_dedup (i1 : ZSet A) (i2 : ZSet B) :
    ZSet.isBag i1 → ZSet.isBag i2 →
    ZSet.distinct (ZSet.product (ZSet.distinct i1) (ZSet.distinct i2)) = ZSet.distinct (ZSet.product i1 i2) := by
  intro hpos1 hpos2
  rw [ZSet.product_distinct_comm _ _ hpos1 hpos2]
  exact ZSet.distinct_idem (ZSet.product i1 i2)

theorem join_distinct_dedup (π1 : A → C) (π2 : B → C) (i1 : ZSet A) (i2 : ZSet B) :
    ZSet.isBag i1 → ZSet.isBag i2 →
    ZSet.distinct (ZSet.equiJoin π1 π2 (ZSet.distinct i1) (ZSet.distinct i2)) = ZSet.distinct (ZSet.equiJoin π1 π2 i1 i2) := by
  intro hpos1 hpos2
  rw [ZSet.join_distinct_comm π1 π2 i1 i2 hpos1 hpos2]
  exact ZSet.distinct_idem (ZSet.equiJoin π1 π2 i1 i2)

theorem intersect_distinct_dedup (i1 i2 : ZSet A) :
    ZSet.isBag i1 → ZSet.isBag i2 →
    ZSet.distinct (ZSet.distinct i1 ∩ ZSet.distinct i2) = ZSet.distinct (i1 ∩ i2) := by
  intro hpos1 hpos2
  rw [ZSet.intersect_distinct_comm i1 i2 hpos1 hpos2]
  exact ZSet.distinct_idem (i1 ∩ i2)


end ZSet

end

end Dbsp

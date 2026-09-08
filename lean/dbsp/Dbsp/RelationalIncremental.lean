/-
# Dbsp.RelationalIncremental — incremental forms of the relational ops

Ports tchajed/database-stream-processing-theory
`src/relational_incremental.lean` (Lean 3) to Lean 4 (notes/lean/lean-v3.md
Part 3).

The theorems:

- `map_incremental` / `filter_incremental` / `lifting_map_incremental` —
  the linear operators are their own incremental forms (via
  `lti_incremental`). No old state needed.
- `equiJoin_incremental` — **the incremental join**: the join's delta form
  is the three-term bilinear expansion (`bilinear_incremental`).
- `distinct_incremental_ok` — the incremental form of `distinct` is
  `distinctH`, which READS THE OLD (INTEGRATED) STATE. This is the
  old_values theorem made concrete: non-linear operators need history, and
  exactly this much history (the prior integrated state).

Deferred: the source's `flatmap_incremental` — the flatmap/map distinction
collapses over mathlib's `Finsupp.mapDomain` (see `Dbsp.ZSet`'s header), so
`map_incremental` covers both.
-/

import Dbsp.Relational
import Dbsp.Incremental

namespace Dbsp

variable {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-! ## The incremental form of distinct needs history -/

/-- The per-element distinct-delta from old state `i` and new delta `d`:
    -1 when the element leaves the set (was present, now gone), +1 when it
    enters, 0 otherwise. -/
noncomputable def ZSet.distinctHAt (i d : ZSet A) (x : A) : ℤ :=
  if 0 < i x ∧ (i + d) x ≤ 0 then -1
  else if i x ≤ 0 ∧ 0 < (i + d) x then 1
  else 0

/-- The incremental distinct operator's body, as a Z-set over the union of
    the supports. -/
noncomputable def ZSet.distinctH (i d : ZSet A) : ZSet A :=
  Finsupp.onFinset (i.support ∪ d.support) (fun x => distinctHAt i d x) (by
    intro x hx
    unfold distinctHAt at hx
    split_ifs at hx with h1 h2
    · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr (ne_of_gt h1.1))
    · have hne : (i + d) x ≠ 0 := ne_of_gt h2.2
      rw [Finsupp.add_apply] at hne
      by_contra hmem
      rw [Finset.mem_union] at hmem
      push_neg at hmem
      rw [Finsupp.notMem_support_iff.mp hmem.1, Finsupp.notMem_support_iff.mp hmem.2,
        add_zero] at hne
      exact hne rfl
    · exact absurd hx (by simp))

@[simp] theorem ZSet.distinctH_apply (i d : ZSet A) (x : A) :
    ZSet.distinctH i d x = ZSet.distinctHAt i d x := by
  rw [ZSet.distinctH, Finsupp.onFinset_apply]

/-- The incremental distinct: the distinct-delta from the previous
    integrated state and the current delta. -/
noncomputable def distinctIncremental : Stream (ZSet A) → Stream (ZSet A) :=
  fun d => lifting2 ZSet.distinctH (delay (I d)) d

/-- **distinct incrementalizes into old-state + delta.** The proof is the
    pointwise sign analysis of set membership across a step. -/
theorem distinct_incremental_ok :
    incremental (lifting (ZSet.distinct (A := A))) = distinctIncremental (A := A) := by
  funext d
  funext t
  show D (lifting ZSet.distinct (I d)) t = lifting2 ZSet.distinctH (delay (I d)) d t
  cases t with
  | zero =>
    show ZSet.distinct (I d 0) - ZSet.distinct (delay (I d) 0)
       = ZSet.distinctH (delay (I d) 0) (d 0)
    rw [integral_0]
    show ZSet.distinct (d 0) - ZSet.distinct 0 = ZSet.distinctH 0 (d 0)
    rw [ZSet.distinct_0, sub_zero]
    ext x
    rw [ZSet.distinctH_apply, ZSet.distinct_apply]
    simp [ZSet.distinctHAt, Finsupp.zero_apply]
  | succ n =>
    show ZSet.distinct (I d (n + 1)) - ZSet.distinct (delay (I d) (n + 1))
       = ZSet.distinctH (delay (I d) (n + 1)) (d (n + 1))
    rw [delay_succ]
    have hI : I d (n + 1) = d (n + 1) + I d n := by
      have h := congr_fun (integral_unfold d) (n + 1)
      rw [h]
      show d (n + 1) + delay (I d) (n + 1) = d (n + 1) + I d n
      rw [delay_succ]
    rw [hI]
    ext x
    rw [Finsupp.sub_apply, ZSet.distinctH_apply, ZSet.distinct_apply, ZSet.distinct_apply]
    unfold ZSet.distinctHAt
    split_ifs <;> simp_all [Finsupp.add_apply] <;> omega

/-! ## Linear operators incrementalize for free -/

/-- Map is LTI, hence its own incremental form. -/
@[simp] theorem map_incremental (f : A → B) :
    incremental (lifting (ZSet.map f)) = lifting (ZSet.map f) :=
  lti_incremental _ (lifting_lti _ (fun _ _ => ZSet.map_linear f _ _))

/-- The twice-lifted form (map as a stream-of-streams operator). -/
@[simp] theorem lifting_map_incremental (f : A → B) :
    incremental (lifting (lifting (ZSet.map f))) = lifting (lifting (ZSet.map f)) := by
  apply lti_incremental
  apply lifting_lti
  intro x y
  funext t
  exact ZSet.map_linear f (x t) (y t)

/-- The unfolded content: differentiating mapped states is mapping deltas. -/
theorem map_incremental_unfolded (f : A → B) (s : Stream (ZSet A)) :
    D (lifting (ZSet.map f) (I s)) = lifting (ZSet.map f) s :=
  congr_fun (map_incremental f) s

/-- Filter is LTI, hence its own incremental form. -/
@[simp] theorem filter_incremental (p : A → Prop) [DecidablePred p] :
    incremental (lifting (ZSet.filter p)) = lifting (ZSet.filter p) :=
  lti_incremental _ (lifting_lti _ (fun _ _ => ZSet.filter_linear p _ _))

/-! ## The incremental join -/

/-- **The incremental join**: for the equi-join (a time-invariant bilinear
    operator), the delta form is the three-term expansion
    `ΔA ⋈ B + A(prev) ⋈ ΔB + ΔA ⋈ ΔB`-via-`timesIncremental`
    (`a⋆b + I(z⁻¹a)⋆b + a⋆I(z⁻¹b)`). This is the join kernel's license:
    new-left against right-state, new-right against left-state, and
    delta-against-delta. -/
theorem equiJoin_incremental (π1 : A → C) (π2 : B → C) :
    incremental2 (lifting2 (ZSet.equiJoin π1 π2))
      = timesIncremental (lifting2 (ZSet.equiJoin π1 π2)) := by
  apply bilinear_incremental
  · rw [uncurryOp_lifting2]
    exact lifting_time_invariant _ (ZSet.equiJoin_0_l π1 π2 0)
  · exact lifting_bilinear _ (ZSet.equiJoin_bilinear π1 π2)

end Dbsp

/-
# Query.Eval — the weighted evaluation + the bridge + the weight-polymorphism

Owned by: the Query agent (the mandate tree, `query/`).

notes/v3/02-data-plane.md §4 (one relation semantics, a family of
weights: union adds, join multiplies, projection sums over preimages,
filter restricts) + 15-patterns #1 (the spec never lies to fit the
checker — the bridge runs BOTH ways) + #6 (the dual-reading tie).

What lands here:

- `tableW` — a base table as a `K`-weighted relation (the membership
  weight is the CALLER's — Bool = membership, Nat/ℤ = multiplicity;
  `WKind` has no unit, and inventing one would be a second weight
  algebra).
- `joinPairsW` — the equijoin's weighted core over the two sides'
  supports: the pairs satisfying the ON predicate, weights
  MULTIPLIED. Its weight formula (`joinPairsW_ok`) needs the
  right-zero law the abstract `WKind` does not carry (the left-zero
  `mul zero a` IS a `WKind` field); the law rides the explicit
  `WKindMulZero` bundle — Bool/Nat/Int instance it, nothing smuggled.
- `evalQ` — THE EXECUTABLE SEMANTICS: `K`-polymorphic (sets, bags,
  deltas share the one evaluation — 02 §4), structural over the typed
  fragment `Query.Q`.
- `evalQ_wmap` — **THE ONE THEOREM's instance** (02 §4): a weight-map
  on the input commutes with the evaluation,
  `wmap h (evalQ q m) = evalQ q (wmap h m)` — by structural induction
  over the fragment, one `WeightMap` bundle, every instance free.
- THE BRIDGE (pattern #1): `evalQ_true_iff` — over Bool weights (set
  semantics), the executable result's membership IS the spec
  (`Query.QSat`): both directions, one structural induction. The ℤ
  reading is the weight formulas themselves (pinned in QueryTests);
  the collapse to membership over bags is
  `ZSet.evaluate_supportCollapse`'s pattern, not restated here.
- `evalQ_join_key_det` — the 02 §3 payoff THROUGH the bridge: when the
  join's left column is the declared key and the left table's
  `uniqueOn` is checked, the joined left row is DETERMINED per right
  row — the Keys lane's determinacy theorem consumed via the spec.

The honest boundary (02 §4, named): deduplication is non-linear;
negation needs more than the weight-map bundle; ordered operations
need an explicit order — none of the three is in the fragment.

The five questions (notes/v3/01-core.md):
- **Root**: Universe × Change crossing — the fragment evaluates over
  ANY weight kind (the ONE relation semantics, 02 §4).
- **Carrier grade**: `ZSet.Weighted K Row` consumed, never re-carried.
- **Spine reading**: none — the executable face of the fragment.
- **Ladder rung**: hand theorems of the small kind — the bridge and
  the wmap instance are structural inductions written ONCE.
- **Gate rows**: the axiom report + QueryTests' pins (the weight-poly
  pins, the bridge both ways, the determinacy typing, the mandatory
  negative controls).

Core-only (imports Query.Expr + ZSet.Relation — the cone rule).
-/

import Query.Expr
import ZSet.Relation

namespace Query

open SchemaCore ZSet

/-! ## The right-zero bundle (the join's weight formula's premise) -/

/-- The right-zero law: `mul a zero = zero`. The abstract `WKind`
    carries the LEFT zero only; Bool/Nat/Int have both, and the join's
    weight formula consumes the right one — carried as an explicit
    class, never assumed silently. -/
class WKindMulZero (K : Type) [WKind K] where
  mul_zero_r : ∀ a : K, WKind.mul a WKind.zero = WKind.zero

instance wkindMulZeroInt : WKindMulZero Int where
  mul_zero_r := fun a => by rw [wkindInt_mul]; exact Int.mul_zero a

instance wkindMulZeroNat : WKindMulZero Nat where
  mul_zero_r := fun a => by rw [wkindNat_mul]; exact Nat.mul_zero a

instance wkindMulZeroBool : WKindMulZero Bool where
  mul_zero_r := fun a => by rw [wkindBool_mul]; exact Bool.and_false a

/-! ## The base table -/

/-- The base table as a `K`-weighted relation: each row at the
    caller's membership weight (duplicates accumulate — the bag
    reading; over Bool the add is OR, the set reading). -/
def tableW [WKind K] [CanonKey (RowVals fs)] [DecidableEq (RowVals fs)]
    (rows : List (RowVals fs)) (w : K) : Weighted K (RowVals fs) :=
  fromListW (rows.map fun r => (r, w))

/-- Over Bool, the base table's weight IS membership. -/
theorem tableW_bool_ok (rows : List (RowVals fs)) (r : RowVals fs) :
    weightW (tableW (K := Bool) rows true) r = decide (r ∈ rows) := by
  induction rows with
  | nil => rfl
  | cons r0 rest ih =>
      simp only [tableW, fromListW, weightW, canonW_weight] at ih ⊢
      simp only [List.map_cons, weightOfW, wkindBool_add] at ih ⊢
      by_cases h : r0 = r
      · rw [if_pos h, ih, Bool.true_or,
          decide_eq_true_iff.mpr (List.mem_cons.mpr (Or.inl h.symm))]
      · rw [if_neg h, ih]
        refine decide_eq_decide.mpr ⟨List.mem_cons_of_mem _, fun hmem => ?_⟩
        rcases List.mem_cons.mp hmem with he | hmem'
        · exact absurd he.symm h
        · exact hmem'

/-! ## The equijoin's weighted core -/

/-- The join's weighted core over two supports: every pair satisfying
    the ON predicate, at the MULTIPLIED weight (02 §4: join
    multiplies). The result carrier is the product; the fragment's
    join collapses it onto the appended schema by projection. -/
def joinPairsW [WKind K] (m : Weighted K (RowVals ga))
    (n : Weighted K (RowVals gb)) (p : RowVals ga → RowVals gb → Bool) :
    Weighted K (RowVals ga × RowVals gb) :=
  fromListW (m.rep.flatMap fun pa =>
    n.rep.filterMap fun pb =>
      if p pa.1 pb.1 then some ((pa.1, pb.1), WKind.mul pa.2 pb.2) else none)

/-- Off-support zero: no matching key, no weight. -/
theorem weightOfW_zero_forall_ne [WKind K] [DecidableEq α] (x : α) :
    ∀ {l : List (α × K)}, (∀ e ∈ l, e.1 ≠ x) → weightOfW l x = WKind.zero := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p r ih =>
      intro h
      have hne : ¬ (p.1 = x) := h p (by simp)
      simp only [weightOfW, if_neg hne]
      exact ih (fun e he => h e (by simp [he]))

/-- The per-left-row segment: the right support's matching pairs at the
    multiplied weight (the right rep's single-entry discipline makes
    the fold the pointwise product). -/
theorem weightOfW_joinInner [WKind K] [WKindMulZero K]
    [_cka : CanonKey α] [DecidableEq α] [ckb : CanonKey β] [DecidableEq β]
    {n : List (β × K)} (hsn : KeySortedW n)
    (p : α → β → Bool) (a : α) (wa : K) (b : β) :
    weightOfW (n.filterMap (fun pb => if p a pb.1 then some ((a, pb.1), WKind.mul wa pb.2) else none)) (a, b)
      = if p a b then WKind.mul wa (weightOfW n b) else WKind.zero := by
  induction hsn with
  | nil =>
      simp only [weightOfW]
      split
      · exact (WKindMulZero.mul_zero_r _).symm
      · rfl
  | cons k w r hlt hs ih =>
      by_cases hp0 : p a k
      · simp only [if_pos hp0, List.filterMap_cons, weightOfW]
        by_cases hkb : k = b
        · rw [if_pos (by rw [hkb])]
          have hp0b : p a b = true := hkb ▸ hp0
          have hr : weightOfW (r.filterMap (fun pb => if p a pb.1 then some ((a, pb.1), WKind.mul wa pb.2) else none)) (a, b)
              = WKind.zero := by
            refine weightOfW_zero_forall_ne _ (fun e he => ?_)
            obtain ⟨pb, hpb, he⟩ := List.mem_filterMap.mp he
            by_cases hpp : p a pb.1
            · rw [if_pos hpp] at he
              have hinj := Option.some.inj he
              have hne1 : pb.1 ≠ b := by
                intro hh
                have h1 := hlt pb hpb
                rw [hh, hkb] at h1
                exact ckb.irrefl b h1
              refine fun hcon => hne1 (by
                have hfst : (a, pb.1) = e.1 := congrArg Prod.fst hinj
                have hpair : (a, pb.1) = (a, b) := hfst.trans hcon
                exact congrArg Prod.snd hpair)
            · rw [if_neg hpp] at he
              exact absurd he (by simp)
          rw [hr, WKind.add_zero, if_pos hp0b]
          have hz : weightOfW r b = WKind.zero := by
            refine weightOfW_gt b r (fun q hq => ?_)
            have h1 := hlt q hq
            rw [hkb] at h1
            exact h1
          rw [if_pos hkb, hz, WKind.add_zero]
        · rw [if_neg (by intro hc; exact hkb (congrArg Prod.snd hc)), ih,
            if_neg hkb]
      · simp only [if_neg hp0, List.filterMap_cons, weightOfW]
        rw [ih]
        by_cases hkb : k = b
        · have hp0b : p a b = false := by rw [← hkb]; simpa using hp0
          rw [if_neg (by simp [hp0b]), if_neg (by simp [hp0b])]
        · simp only [if_neg hkb]

/-- THE JOIN'S WEIGHT FORMULA: the pair's weight is the multiplied
    weights of the sides when the ON predicate holds, zero otherwise.
    Each side's support carries each key at most once (the canonical
    rep's single-entry discipline), so the fold is the pointwise
    product. -/
theorem weightOfW_joinFlat [WKind K] [WKindMulZero K]
    [cka : CanonKey α] [DecidableEq α] [ckb : CanonKey β] [DecidableEq β]
    {n : List (β × K)} (hsn : KeySortedW n)
    (p : α → β → Bool) :
    ∀ {l : List (α × K)}, KeySortedW l → ∀ (a : α) (b : β),
      weightOfW (l.flatMap (fun pa => n.filterMap (fun pb => if p pa.1 pb.1 then some ((pa.1, pb.1), WKind.mul pa.2 pb.2) else none))) (a, b)
        = if p a b then WKind.mul (weightOfW l a) (weightOfW n b) else WKind.zero := by
  intro l hsorted
  induction hsorted with
  | nil =>
      intro a b
      simp only [List.flatMap_nil, weightOfW]
      split
      · exact (WKind.mul_zero _).symm
      · rfl
  | cons k w r hlt hs ih =>
      intro a b
      simp only [List.flatMap_cons, weightOfW_append]
      by_cases hka : k = a
      · subst hka
        rw [weightOfW_joinInner hsn p k w b]
        have hrest : weightOfW
            (r.flatMap (fun pa => n.filterMap (fun pb => if p pa.1 pb.1 then some ((pa.1, pb.1), WKind.mul pa.2 pb.2) else none))) (k, b)
            = WKind.zero := by
          refine weightOfW_zero_forall_ne _ (fun e he => ?_)
          obtain ⟨pa, hpa, he⟩ := List.mem_flatMap.mp he
          obtain ⟨pb, hpb, he⟩ := List.mem_filterMap.mp he
          by_cases hpp : p pa.1 pb.1
          · rw [if_pos hpp] at he
            have hinj := Option.some.inj he
            have hne1 : pa.1 ≠ k := by
              intro hh
              have h1 := hlt pa hpa
              rw [hh] at h1
              exact cka.irrefl k h1
            refine fun hcon => hne1 (by
              have hfst : (pa.1, pb.1) = e.1 := congrArg Prod.fst hinj
              have hpair : (pa.1, pb.1) = (k, b) := hfst.trans hcon
              exact congrArg Prod.fst hpair)
          · rw [if_neg hpp] at he
            exact absurd he (by simp)
        rw [hrest, WKind.add_zero]
        have hwk : weightOfW ((k, w) :: r) k = w :=
          weightOfW_entry ((k, w) :: r) (KeySortedW.cons k w r hlt hs) (k, w) (by simp)
        have hz : weightOfW r k = WKind.zero :=
          weightOfW_gt k r (fun q hq => hlt q hq)
        simp only [hwk]
      · have hseg : weightOfW (n.filterMap (fun pb => if p k pb.1 then some ((k, pb.1), WKind.mul w pb.2) else none)) (a, b)
            = WKind.zero := by
          refine weightOfW_zero_forall_ne _ (fun e he => ?_)
          obtain ⟨pb, hpb, he⟩ := List.mem_filterMap.mp he
          by_cases hpp : p k pb.1
          · rw [if_pos hpp] at he
            have hinj := Option.some.inj he
            refine fun hcon => hka (by
              have hfst : (k, pb.1) = e.1 := congrArg Prod.fst hinj
              have hpair : (k, pb.1) = (a, b) := hfst.trans hcon
              exact congrArg Prod.fst hpair)
          · rw [if_neg hpp] at he
            exact absurd he (by simp)
        rw [hseg, WKind.zero_add, ih a b]
        simp only [weightOfW, if_neg hka]

theorem joinPairsW_ok [WKind K] [WKindMulZero K]
    (m : Weighted K (RowVals ga)) (n : Weighted K (RowVals gb))
    (p : RowVals ga → RowVals gb → Bool) (a : RowVals ga) (b : RowVals gb) :
    weightW (joinPairsW m n p) (a, b)
      = if p a b then WKind.mul (weightW m a) (weightW n b) else WKind.zero := by
  simp only [joinPairsW, fromListW, weightW, canonW_weight]
  rw [weightOfW_joinFlat n.sorted p m.sorted a b]

/-- The join's commutation (the ONE theorem at the product carrier):
    the weight-map distributes over the multiplied pairs. -/
theorem joinPairsW_wmap [WKind K] [WKindMulZero K]
    {L : Type} [WKind L] [WKindMulZero L]
    (h : WeightMap K L) (m : Weighted K (RowVals ga))
    (n : Weighted K (RowVals gb)) (p : RowVals ga → RowVals gb → Bool) :
    wmap h (joinPairsW m n p) = joinPairsW (wmap h m) (wmap h n) p := by
  apply extW
  intro ab
  obtain ⟨a, b⟩ := ab
  rw [weightW_wmap, joinPairsW_ok, joinPairsW_ok, weightW_wmap, weightW_wmap]
  by_cases hp : p a b
  · rw [if_pos hp, if_pos hp]; exact h.map_mul _ _
  · rw [if_neg hp, if_neg hp]; exact h.map_zero

/-! ## The evaluation (the executable semantics, weight-polymorphic) -/

/-- THE EXECUTABLE EVALUATION: structural over the typed fragment;
    `K`-polymorphic — sets, bags, deltas share the ONE evaluation (02
    §4). Union adds, the equijoin multiplies (over the ON-satisfying
    pairs, collapsed onto the appended schema), projection sums over
    preimages, selection restricts. -/
def evalQ [WKind K] (q : Q fs gs) (m : Weighted K (RowVals fs)) :
    Weighted K (RowVals gs) :=
  match q with
  | .table => m
  | .select p q => filterW p.check (evalQ q m)
  | .project c q => projectW (c.pick _) (evalQ q m)
  | .union q1 q2 => addW (evalQ q1 m) (evalQ q2 m)
  | .join ln rn q1 q2 =>
      projectW (fun pr => Row.append pr.1 pr.2)
        (joinPairsW (evalQ q1 m) (evalQ q2 m) (onEq _ _ ln rn))

/-- The projection's commutation (the ONE theorem at the projection
    node — `weightMap_projectWeight` applied). -/
theorem projectW_wmap [WKind K] {L : Type} [WKind L]
    [CanonKey α] [DecidableEq α] [CanonKey β] [DecidableEq β]
    (h : WeightMap K L) (g : α → β) (m : Weighted K α) :
    wmap h (projectW g m) = projectW g (wmap h m) := by
  apply extW
  intro b
  rw [weightW_wmap, projectW_ok, projectW_ok]
  exact weightMap_projectWeight h g m b

/-- **THE ONE THEOREM's instance** (02 §4): a weight-map on the input
    commutes with the evaluation — `wmap h (evalQ q m) = evalQ q
    (wmap h m)`, by structural induction over the fragment, ONE
    `WeightMap` bundle (zero/add/mul preservation), every instance
    free. Provenance, counts, membership, and deltas connect through
    THIS, not per-query proofs. -/
theorem evalQ_wmap [WKind K] [WKindMulZero K]
    {L : Type} [WKind L] [WKindMulZero L]
    (q : Q fs gs) (h : WeightMap K L) (m : Weighted K (RowVals fs)) :
    wmap h (evalQ q m) = evalQ q (wmap h m) := by
  induction q with
  | table => rfl
  | select p q ih =>
      apply extW
      intro a
      simp only [evalQ, weightW_wmap, filterW_ok, ← ih]
      by_cases hc : p.check a = true
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, h.map_zero]
  | project c q ih =>
      apply extW
      intro b
      simp only [evalQ, weightW_wmap, projectW_ok, ← ih]
      exact weightMap_projectWeight h (c.pick _) (evalQ q m) b
  | union q1 q2 ih1 ih2 =>
      apply extW
      intro a
      simp only [evalQ, weightW_wmap, addW_ok, ← ih1, ← ih2, weightW_wmap]
      exact h.map_add _ _
  | join ln rn q1 q2 ih1 ih2 =>
      apply extW
      intro x
      simp only [evalQ]
      rw [weightW_wmap, projectW_ok, projectW_ok, weightMap_projectWeight,
        joinPairsW_wmap h, ← ih1, ← ih2]

/-! ## The bridge (pattern #1: the executable result satisfies the spec) -/

/-- The Bool-weighted fold's existential reading (the preimage sum
    over Bool is the disjunction). -/
theorem weightOfW_bool_mem [DecidableEq α] (x : α) :
    ∀ (l : List (α × Bool)), weightOfW l x = true ↔ ∃ e ∈ l, e.1 = x ∧ e.2 = true := by
  intro l
  induction l with
  | nil => simp [weightOfW]
  | cons p r ih =>
      obtain ⟨k, w⟩ := p
      by_cases hkx : k = x
      · rw [weightOfW, if_pos hkx, wkindBool_add, Bool.or_eq_true, ih]
        constructor
        · rintro (h | ⟨e, he, hx, hw⟩)
          · exact ⟨(k, w), by simp, hkx, h⟩
          · exact ⟨e, List.mem_cons_of_mem _ he, hx, hw⟩
        · rintro ⟨e, he, hx, hw⟩
          rcases List.mem_cons.mp he with e0 | he'
          · rw [e0] at hx hw
            exact Or.inl hw
          · exact Or.inr ⟨e, he', hx, hw⟩
      · rw [weightOfW, if_neg hkx, ih]
        constructor
        · rintro ⟨e, he, hx, hw⟩
          exact ⟨e, List.mem_cons_of_mem _ he, hx, hw⟩
        · rintro ⟨e, he, hx, hw⟩
          rcases List.mem_cons.mp he with e0 | he'
          · have h1 : e.1 = k := by rw [e0]
            exact absurd (h1.symm.trans hx) hkx
          · exact ⟨e, he', hx, hw⟩

/-- The relabeled list's membership (relabelW preserves the entries,
    retagged). -/
theorem mem_relabelW [CanonKey β] [DecidableEq β]
    (g : α → β) (l : List (α × K)) (e : β × K) :
    e ∈ relabelW g l ↔ ∃ p ∈ l, g p.1 = e.1 ∧ p.2 = e.2 := by
  induction l with
  | nil => simp [relabelW]
  | cons p r ih =>
      constructor
      · intro he
        simp only [relabelW, List.mem_cons] at he
        rcases he with he | he'
        · exact ⟨p, by simp, by rw [he], by rw [he]⟩
        · obtain ⟨q, hq, hg, hw⟩ := ih.mp he'
          exact ⟨q, List.mem_cons_of_mem _ hq, hg, hw⟩
      · rintro ⟨q, hq, hg, hw⟩
        rcases List.mem_cons.mp hq with e0 | hq'
        · rw [e0] at hg hw
          have heq : e = (g p.1, p.2) := by
            obtain ⟨e1, e2⟩ := e
            have h1 : g p.1 = e1 := hg
            have h2 : p.2 = e2 := hw
            rw [h1.symm, h2.symm]
          exact List.mem_cons.mpr (Or.inl heq)
        · exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨q, hq', hg, hw⟩))

/-- The projection's Bool preimage-sum: present iff some preimage row
    is present and projects to the target — the existential reading,
    executable. -/
theorem projectW_bool_exists [CanonKey α] [DecidableEq α] [CanonKey β] [DecidableEq β]
    (g : α → β) (m : Weighted Bool α) (b : β) :
    weightW (projectW g m) b = true ↔ ∃ r, weightW m r = true ∧ g r = b := by
  rw [projectW_ok, projectWeightW_eq, weightOfW_bool_mem]
  constructor
  · rintro ⟨e, he, hb, hw⟩
    obtain ⟨p, hpm, hg, hpw⟩ := (mem_relabelW g m.rep e).mp he
    have hkb : g p.1 = b := by rw [hg, hb]
    have hpwt : p.2 = true := by rw [hpw]; exact hw
    refine ⟨p.1, ?_, hkb⟩
    rw [weightW, weightOfW_bool_mem]
    exact ⟨p, hpm, rfl, hpwt⟩
  · rintro ⟨r, hr, hrb⟩
    rw [weightW, weightOfW_bool_mem] at hr
    obtain ⟨e, he, hx, hw⟩ := hr
    refine ⟨(g e.1, e.2), ?_, ?_, hw⟩
    · exact (mem_relabelW g m.rep _).mpr ⟨e, he, by rw [hx, hrb], rfl⟩
    · rw [hx, hrb]

/-! ## The bridge (pattern #1: the executable result satisfies the spec) -/

/-- **THE BACKWARD BRIDGE FACE**: a spec-satisfying row is present in
    the executable result — by the QSat recursor with the motive named
    EXPLICITLY: the recursor's application never unifies the
    fragment's computed indices (the join's `ga ++ gb`, the
    projection's `c.fields gs`), which is exactly what the
    tactic-level `cases` cannot do here. -/
theorem QSat.weight_true {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (h : QSat fs rows q r) :
    weightW (evalQ q (tableW rows true)) r = true :=
  QSat.rec (motive := fun q' r' _ => weightW (evalQ q' (tableW rows true)) r' = true)
    (table := fun r' hm => by
      rw [evalQ, tableW_bool_ok]
      exact decide_eq_true_iff.mpr hm)
    (select := fun _a hc ih => by
      rw [evalQ, filterW_ok, if_pos hc]; exact ih)
    (project := fun _a hp ih => by
      rw [evalQ, projectW_bool_exists]
      exact ⟨_, ih, hp⟩)
    (unionL := fun _a ih => by
      rw [evalQ, addW_ok, wkindBool_add, Bool.or_eq_true]; exact Or.inl ih)
    (unionR := fun _a ih => by
      rw [evalQ, addW_ok, wkindBool_add, Bool.or_eq_true]; exact Or.inr ih)
    (join := fun {ga gb ln rn q1 q2 la rb r} _a1 _a2 hon hEq ih1 ih2 => by
      rw [evalQ, projectW_bool_exists]
      refine ⟨(la, rb), ?_, hEq⟩
      rw [joinPairsW_ok, wkindBool_mul, if_pos hon, Bool.and_eq_true]
      exact ⟨ih1, ih2⟩)
    h

/-- **THE BRIDGE** (pattern #1, both directions): over Bool weights —
    set semantics — the executable evaluation's membership IS the spec
    (`Query.QSat`): the checker never lies, the spec never lies to fit
    the checker. The forward face is one structural induction over the
    fragment (constructions only); the backward face is
    `QSat.weight_true`. -/
theorem evalQ_true_iff (q : Q fs gs) (rows : List (RowVals fs)) (r : RowVals gs) :
    weightW (evalQ q (tableW rows true)) r = true ↔ QSat fs rows q r := by
  constructor
  · intro h
    induction q with
    | table =>
        rw [evalQ, tableW_bool_ok] at h
        exact QSat.table r (decide_eq_true_iff.mp h)
    | select p q ih =>
        rw [evalQ, filterW_ok] at h
        split at h
        · next hc => exact QSat.select (ih r h) hc
        · exact absurd h (by simp)
    | project c q ih =>
        rw [evalQ, projectW_bool_exists] at h
        obtain ⟨r', hr, hp⟩ := h
        exact QSat.project (ih r' hr) hp
    | union q1 q2 ih1 ih2 =>
        rw [evalQ, addW_ok, wkindBool_add, Bool.or_eq_true] at h
        rcases h with h | h
        · exact QSat.unionL (ih1 r h)
        · exact QSat.unionR (ih2 r h)
    | join ln rn q1 q2 ih1 ih2 =>
        rw [evalQ, projectW_bool_exists] at h
        obtain ⟨⟨la, rb⟩, hw, happ⟩ := h
        rw [joinPairsW_ok, wkindBool_mul] at hw
        by_cases hon : onEq _ _ ln rn la rb = true
        · rw [if_pos hon, Bool.and_eq_true] at hw
          exact QSat.join (ih1 la hw.1) (ih2 rb hw.2) hon happ
        · rw [if_neg hon] at hw
          exact absurd hw (by simp)
  · exact fun h => h.weight_true

end Query

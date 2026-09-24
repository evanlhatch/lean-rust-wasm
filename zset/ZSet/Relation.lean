/-
# ZSet.Relation — the query-fragment layer over the weighted relation (02 §4)

Owned by: the ZSet agent (the mandate tree, `zset/`).

The five questions (notes/v3/01-core.md):
- **Root**: Universe × Change crossing — the ONE relation semantics with
  a family of weights (02 §4): `Weighted K Row` (Basic's canonical-rep
  carrier) read through the query fragment: union adds, join
  multiplies, projection sums over preimages, filter restricts.
- **Carrier grade**: none of its own — this layer CONSUMES Basic's
  canonical-rep `Weighted K Row` (the review's consolidation: one
  machinery, in Basic; this file is the fragment + its theorems).
- **Spine reading**: none — the query-algebra substrate the relational
  lanes consume.
- **Ladder rung**: n/a — Universe-side operations; the Change rung
  stays the ℤ surface's (Basic's `zsetAdditive`).
- **Gate rows**: the axiom report (`gates axioms`) + the ZSetTests
  suites (THE ONE THEOREM, the old-values teeth, the collapse's
  negative controls).

## The shape

`WeightMap` is the homomorphism bundle: preserve zero, add, mul —
nothing else. THE ONE THEOREM `evaluate_wmap`:

```
wmap h (evaluate Q input) = evaluate Q (wmap h input)
```

is proved ONCE by structural induction over the closed `Query`
fragment (union/join/project/filter); every instance — the ℤ→Bool
support collapse, the identity map — is free. The honest limits (02
§4, named not hidden): dedup is NON-LINEAR (`distinctW`/`thresholdW`
carry the old-values requirement as a PARAMETER in their laws —
`distinctW_add_ok`/`thresholdW_add_ok` — and the load-bearing-ness of
the premise is pinned in ZSetTests); negation needs more than this
bundle; ordered operations need an explicit order; the ℤ→Nat map is a
homomorphism only ON BAGS (premise-guarded, not a `WeightMap`).

The ℤ bridge is now the IDENTITY: `ZSet α` IS `Weighted Int α`
(Basic's abbrev) — `ofZSet` remains as the tests' name for the
specialization, by definition weight- and operation-preserving.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import ZSet.Basic

namespace ZSet

variable [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row]

/-! ## Positivity (`_pos`: bags stay bags — the Int instance) -/

/-- The bag predicate: every weight nonnegative (legacy dbsp's
    `isBag`). Only the ORDERED weight kinds can ask it — a named
    limit of the abstract layer. -/
def IsBag (m : Weighted Int Row) : Prop := ∀ a, 0 ≤ weightW m a

theorem addW_pos (m n : Weighted Int Row) (hm : IsBag m) (hn : IsBag n) : IsBag (addW m n) := by
  intro a
  have h1 : 0 ≤ weightW m a := hm a
  have h2 : 0 ≤ weightW n a := hn a
  rw [addW_ok, wkindInt_add]
  omega

theorem joinW_pos (m n : Weighted Int Row) (hm : IsBag m) (hn : IsBag n) : IsBag (joinW m n) := by
  intro a
  rw [joinW_ok, wkindInt_mul]
  exact Int.mul_nonneg (hm a) (hn a)

omit ck [DecidableEq Row] in
/-- The relabeled weight (the preimage sum) over nonnegative entries
    stays nonnegative. -/
theorem relabelWeight_nonneg [CanonKey β] [DecidableEq β]
    (g : Row → β) :
    ∀ (l : List (Row × Int)), (∀ p ∈ l, 0 ≤ p.2) → ∀ b, 0 ≤ weightOfW (relabelW g l) b := by
  intro l
  induction l with
  | nil => intro _ b; simp only [relabelW, weightOfW, wkindInt_zero]; omega
  | cons p r ih =>
    intro hmem b
    simp only [relabelW, weightOfW]
    by_cases hgb : g p.1 = b
    · rw [if_pos hgb, wkindInt_add]
      have h1 := ih (fun q hq => hmem q (by simp [hq])) b
      have h0 : 0 ≤ p.2 := hmem p (by simp)
      omega
    · rw [if_neg hgb]
      exact ih (fun q hq => hmem q (by simp [hq])) b

theorem projectW_pos [CanonKey β] [DecidableEq β] (g : Row → β) (m : Weighted Int Row)
    (hm : IsBag m) (b : β) : 0 ≤ projectWeightW g m b := by
  have entry : ∀ p ∈ m.rep, 0 ≤ p.2 := by
    intro p hp
    have h1 : p.2 = weightOfW m.rep p.1 := (weightOfW_entry m.rep m.sorted p hp).symm
    rw [h1]
    exact hm p.1
  rw [projectWeightW_eq]
  exact relabelWeight_nonneg g m.rep entry b

theorem filterW_pos (p : Row → Bool) (m : Weighted Int Row) (hm : IsBag m) :
    IsBag (filterW p m) := by
  intro a
  rw [filterW_ok]
  by_cases hpa : p a = true
  · rw [if_pos hpa]; exact hm a
  · rw [if_neg hpa, wkindInt_zero]; omega

/-! ## The non-linear operators: distinct + threshold (the old-values rule) -/

/-- The pointwise weight-map lemma the non-linear operators and the
    collapse share: mapping a canonical rep's weights through ANY
    zero-preserving `g` (into ANY weight kind) weighs through `g` of
    the lookup weight (the rep's single-entry discipline makes this
    exact; no additivity of `g` is consumed — the off-support zeros
    are literal). -/
theorem weightOfW_mapPointwise
    (G : Type) (g : Int → G) [wg : WKind G] (h0 : g 0 = wg.zero) :
    ∀ (l : List (Row × Int)), KeySortedW l → ∀ a : Row,
      weightOfW (l.map (fun p => (p.1, g p.2))) a = g (weightOfW l a) := by
  intro l hsorted
  induction hsorted with
  | nil =>
    intro a
    rw [List.map_nil, weightOfW, weightOfW, wkindInt_zero, h0]
  | cons k w r hlt hs ih =>
    intro a
    by_cases hka : k = a
    · subst hka
      have hmapkey : ∀ q ∈ r.map (fun p => (p.1, g p.2)), ck.lt k q.1 := by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact hlt p hp
      simp only [List.map_cons]
      rw [weightOfW, if_pos rfl, ih k, weightOfW, if_pos rfl,
          weightOfW_gt k r (fun q hq => hlt q hq), wkindInt_zero, h0,
          wg.add_zero, wkindInt_add, Int.add_zero]
    · simp only [List.map_cons]
      rw [weightOfW, if_neg hka, weightOfW, if_neg hka, ih a]

/-- DISTINCT: deduplication — every positively-weighted row becomes
    weight 1 (legacy dbsp's `distinct`). NON-LINEAR (02 §4's named
    limit): its incremental form is NOT a function of the delta alone —
    see `distinctW_add_ok`'s old-state parameter. -/
def distinctW (m : Weighted Int Row) :
    Weighted Int Row :=
  fromListW (m.rep.map (fun p => (p.1, if 0 < p.2 then 1 else 0)))

theorem distinctW_ok (m : Weighted Int Row) (a : Row) :
    weightW (distinctW m) a = if 0 < weightW m a then 1 else 0 := by
  simp only [distinctW, fromListW, weightW, canonW_weight]
  exact weightOfW_mapPointwise Int (fun w => if 0 < w then 1 else 0) (by decide)
    m.rep m.sorted a

/-- THRESHOLD: weights at least `k` become 1 (the counting gate).
    Positive thresholds only (`1 ≤ k` — the honest domain: a threshold
    at or below zero fires on absent rows). NON-LINEAR like distinct. -/
def thresholdW (k : Int) (m : Weighted Int Row) :
    Weighted Int Row :=
  fromListW (m.rep.map (fun p => (p.1, if k ≤ p.2 then 1 else 0)))

theorem thresholdW_ok (k : Int) (hk : 1 ≤ k)
    (m : Weighted Int Row) (a : Row) :
    weightW (thresholdW k m) a = if k ≤ weightW m a then 1 else 0 := by
  simp only [thresholdW, fromListW, weightW, canonW_weight]
  exact weightOfW_mapPointwise Int (fun w => if k ≤ w then 1 else 0)
    (by rw [if_neg (show ¬ ((k : Int) ≤ 0) from by omega), wkindInt_zero]) m.rep m.sorted a

/-- THE OLD-VALUES PARAMETER (the mined dbsp discipline: non-linear
    operators need history — the old state `i` appears in the
    incremental form BY NAME, as a parameter; the delta alone does not
    determine it). The leaving/entering sign-transition reading the OLD
    integrated weight. -/
def distinctHAt (i d : Weighted Int Row) (a : Row) : Int :=
  if 0 < weightW i a ∧ weightW (addW i d) a ≤ 0 then -1
  else if weightW i a ≤ 0 ∧ 0 < weightW (addW i d) a then 1 else 0

/-- The old-values law for distinct: the distinct-delta is the old
    distinct state plus the transition term that READS `i`. -/
theorem distinctW_add_ok (i d : Weighted Int Row) (a : Row) :
    weightW (distinctW (addW i d)) a = weightW (distinctW i) a + distinctHAt i d a := by
  rw [distinctW_ok, distinctW_ok, addW_ok, wkindInt_add]
  simp only [distinctHAt, addW_ok, wkindInt_add]
  repeat split <;> omega

/-- The threshold's transition term — same old-values shape. -/
def thresholdHAt (k : Int) (i d : Weighted Int Row)
    (a : Row) : Int :=
  if k ≤ weightW i a ∧ ¬ k ≤ weightW (addW i d) a then -1
  else if ¬ k ≤ weightW i a ∧ k ≤ weightW (addW i d) a then 1 else 0

theorem thresholdW_add_ok (k : Int) (hk : 1 ≤ k)
    (i d : Weighted Int Row) (a : Row) :
    weightW (thresholdW k (addW i d)) a = weightW (thresholdW k i) a + thresholdHAt k i d a := by
  rw [thresholdW_ok k hk, thresholdW_ok k hk, addW_ok, wkindInt_add]
  simp only [thresholdHAt, addW_ok, wkindInt_add]
  repeat split <;> omega

theorem distinctW_pos (m : Weighted Int Row)
    (_hm : IsBag m) : IsBag (distinctW m) := by
  intro a
  rw [distinctW_ok]
  split <;> omega

theorem thresholdW_pos (k : Int) (hk : 1 ≤ k)
    (m : Weighted Int Row) (_hm : IsBag m) : IsBag (thresholdW k m) := by
  intro a
  rw [thresholdW_ok k hk]
  split <;> omega

/-! ## THE ONE THEOREM (02 §4) -/

/-- The weight-map homomorphism bundle: `map` preserves zero, add,
    mul — EXACTLY the operations the fragment's evaluation uses,
    nothing more (02 §4: "h a weight-map preserving the required
    operations"). The provenance-polynomial weight kind is the named
    instance-of-the-future here: a `WKind` over lineage polynomials
    with add = union-of-contributions, mul = how-source-rows-compose;
    not built — its consumer is the relational lanes' explanation
    surface. -/
structure WeightMap (K L : Type) [wk : WKind K] [wl : WKind L] where
  map : K → L
  map_zero : map wk.zero = wl.zero
  map_add : ∀ a b, map (wk.add a b) = wl.add (map a) (map b)
  map_mul : ∀ a b, map (wk.mul a b) = wl.mul (map a) (map b)

/-- Apply a weight map to a relation, weightwise (canonicalization
    preserved by `weightOfW_mapWeight`). -/
def wmap [wl : WKind L]
    (h : WeightMap K L) (m : Weighted K Row) : Weighted L Row :=
  fromListW (m.rep.map (fun p => (p.1, h.map p.2)))

theorem weightOfW_mapWeight [wl : WKind L]
    (h : WeightMap K L) :
    ∀ (l : List (Row × K)) (a : Row),
      weightOfW (canonW (l.map (fun p => (p.1, h.map p.2)))) a
        = h.map (weightOfW l a) := by
  intro l
  induction l with
  | nil => intro a; simp only [List.map_nil, canonW, weightOfW, h.map_zero]
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    intro a
    simp only [List.map_cons, canonW, insertKeyW_weight, weightOfW, ih]
    by_cases hka : k = a
    · rw [if_pos hka, if_pos hka, h.map_add]; wac
    · rw [if_neg hka, if_neg hka]; wac

theorem weightW_wmap [wl : WKind L]
    (h : WeightMap K L) (m : Weighted K Row) (a : Row) :
    weightW (wmap h m) a = h.map (weightW m a) := by
  simp only [wmap, fromListW, weightW, weightOfW_mapWeight]

/-- The homomorphism distributes over the projection's preimage sum
    (the ONE theorem's project step). -/
theorem weightMap_projectWeight [wl : WKind L]
    [CanonKey β] [DecidableEq β]
    (h : WeightMap K L) (g : Row → β) (m : Weighted K Row) (b : β) :
    h.map (projectWeightW g m b) = projectWeightW g (wmap h m) b := by
  rw [projectWeightW_eq]
  have hw : projectWeightW g (wmap h m) b
      = weightOfW (relabelW g (m.rep.map (fun p => (p.1, h.map p.2)))) b := by
    simp only [wmap, fromListW, projectWeightW_eq]
    rw [weightOfW_relabel_canonW]
  rw [hw]
  induction m.rep with
  | nil =>
    rw [List.map_nil, relabelW, relabelW, weightOfW, weightOfW, h.map_zero]
  | cons p r ih =>
    simp only [List.map_cons, relabelW, weightOfW]
    by_cases hgb : g p.1 = b
    · simp only [if_pos hgb, h.map_add, ih]
    · simp only [if_neg hgb, ih]

/-- The fragment's query grammar: a small closed inductive over the
    operators (02 §4's positive fragment). `project` is the
    projection-along-a-row-map (dbsp's `map`: sums over preimages);
    `filter` is the selection. NO negation, NO distinct, NO ordering —
    the doctrine's named limits stay OUT of the grammar. -/
inductive Query (Row : Type) where
  | idQ : Query Row
  | union : Query Row → Query Row → Query Row
  | join : Query Row → Query Row → Query Row
  | project : (Row → Row) → Query Row → Query Row
  | filter : (Row → Bool) → Query Row → Query Row

/-- Evaluate a query over a `K`-weighted relation — generic in the
    weight kind: union adds, join multiplies, projection sums over
    preimages, filter restricts. -/
def evaluate
    (q : Query Row) (m : Weighted K Row) : Weighted K Row :=
  match q with
  | .idQ => m
  | .union q1 q2 => addW (evaluate q1 m) (evaluate q2 m)
  | .join q1 q2 => joinW (evaluate q1 m) (evaluate q2 m)
  | .project g q => projectW g (evaluate q m)
  | .filter p q => filterW p (evaluate q m)

/-- **THE ONE THEOREM** (02 §4): for `h` a weight-map homomorphism,
    `h (evaluate Q input) = evaluate Q (h input)` — proved ONCE by
    structural induction over the query. Every instance (the ℤ→Bool
    support collapse below, the identity map) is free; provenance,
    counts, membership, and deltas connect through THIS, not per-query
    proofs. -/
theorem evaluate_wmap [wl : WKind L]
    (q : Query Row) (h : WeightMap K L) (m : Weighted K Row) :
    wmap h (evaluate q m) = evaluate q (wmap h m) := by
  induction q with
  | idQ => rfl
  | union q1 q2 ih1 ih2 =>
    apply extW
    intro a
    simp only [evaluate, weightW_wmap, addW_ok, ← ih1, ← ih2, weightW_wmap]
    exact h.map_add _ _
  | join q1 q2 ih1 ih2 =>
    apply extW
    intro a
    simp only [evaluate, weightW_wmap, joinW_ok, ← ih1, ← ih2, weightW_wmap]
    exact h.map_mul _ _
  | project g q ih =>
    apply extW
    intro b
    simp only [evaluate, weightW_wmap, projectW_ok, ← ih]
    exact weightMap_projectWeight h g _ b
  | filter p q ih =>
    apply extW
    intro a
    simp only [evaluate, weightW_wmap, filterW_ok, ← ih]
    by_cases hpa : p a = true
    · rw [if_pos hpa, if_pos hpa]
    · rw [if_neg hpa, if_neg hpa, h.map_zero]

/-! ## The instances (the homomorphism family) -/

/-- The identity weight-map (the trivial instance). -/
def idWeightMap [wk : WKind K] : WeightMap K K where
  map a := a
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl

/-! ## The ℤ→Bool support collapse — the bag-restricted instance -/

/-- THE instance (02 §4's table), honestly restricted: the support
    collapse — membership as POSITIVE weight (a delta's nonemptiness,
    on bags). It is deliberately NOT a total `WeightMap`: on signed
    weights the collapse is not additive (`1 + (-1) = 0` — a delta and
    its negation collapse; the negative-control pin lives in
    ZSetTests). ON BAGS it preserves everything the fragment uses
    (`collapse_add`/`collapse_mul`), and the bag-premise threads
    through the whole evaluation (`evaluate_supportCollapse` — the
    ONE theorem's bag instance). -/
def supportCollapseW (m : Weighted Int Row) :
    Weighted Bool Row :=
  fromListW (m.rep.map (fun p => (p.1, decide (0 < p.2))))

theorem weightW_supportCollapseW
    (m : Weighted Int Row) (a : Row) :
    weightW (supportCollapseW m) a = decide (0 < weightW m a) := by
  simp only [supportCollapseW, fromListW, weightW, canonW_weight]
  exact weightOfW_mapPointwise Bool (fun w => decide (0 < w)) (by decide) m.rep m.sorted a

/-- On bags, the collapse preserves add (the sum's nonemptiness is the
    disjunction). -/
theorem collapse_add {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    decide (0 < a + b) = (decide (0 < a) || decide (0 < b)) := by
  have key : decide (0 < a + b) = decide (0 < a ∨ 0 < b) := decide_eq_decide.mpr (by omega)
  rw [key, Bool.decide_or]

/-- On bags, the collapse preserves mul. -/
theorem collapse_mul {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    decide (0 < a * b) = (decide (0 < a) && decide (0 < b)) := by
  have key : decide (0 < a * b) = decide (0 < a ∧ 0 < b) := decide_eq_decide.mpr (by
    constructor
    · intro hpos
      rcases Int.lt_trichotomy a 0 with hlt | rfl | ha1
      · omega
      · rw [Int.zero_mul] at hpos
        omega
      · rcases Int.lt_trichotomy b 0 with hlt | rfl | hb1
        · omega
        · rw [Int.mul_zero] at hpos
          omega
        · exact ⟨ha1, hb1⟩
    · exact fun hx => Int.mul_pos hx.1 hx.2)
  rw [key, Bool.decide_and]

/-- The collapse distributes over the projection's preimage sum (on
    bags — the partial sums stay nonnegative). -/
theorem collapse_projectWeight [CanonKey β] [DecidableEq β]
    (g : Row → β) (m : Weighted Int Row) (hm : IsBag m) (b : β) :
    decide (0 < projectWeightW g m b)
      = projectWeightW g (supportCollapseW m) b := by
  have entry : ∀ p ∈ m.rep, 0 ≤ p.2 := by
    intro p hp
    have h1 : p.2 = weightOfW m.rep p.1 := (weightOfW_entry m.rep m.sorted p hp).symm
    rw [h1]
    exact hm p.1
  rw [projectWeightW_eq]
  have hw : projectWeightW g (supportCollapseW m) b
      = weightOfW (relabelW g (m.rep.map (fun p => (p.1, decide (0 < p.2))))) b := by
    simp only [supportCollapseW, fromListW, projectWeightW_eq]
    rw [weightOfW_relabel_canonW]
  rw [hw]
  revert entry
  induction m.rep with
  | nil =>
    intro entry
    rw [List.map_nil, relabelW, relabelW, weightOfW, weightOfW, wkindInt_zero,
        wkindBool_zero, decide_eq_false_iff_not.mpr (by omega)]
  | cons p r ih =>
    intro entry
    have hmem : ∀ q ∈ r, 0 ≤ q.2 := fun q hq => entry q (by simp [hq])
    have hp2 : 0 ≤ p.2 := entry p (by simp)
    have hpos : 0 ≤ weightOfW (relabelW g r) b := relabelWeight_nonneg g r hmem b
    have hcol : decide (0 < weightOfW (relabelW g r) b)
        = weightOfW (relabelW g (r.map (fun p => (p.1, decide (0 < p.2))))) b := ih hmem
    simp only [List.map_cons, relabelW, weightOfW]
    by_cases hgb : g p.1 = b
    · rw [if_pos hgb, if_pos hgb, wkindInt_add, wkindBool_add,
          collapse_add hp2 hpos, hcol]
    · rw [if_neg hgb, if_neg hgb, hcol]

/-- The fragment preserves bags (the `_pos` family, threaded through
    the evaluation). -/
theorem evaluate_isBag
    (q : Query Row) (m : Weighted Int Row) (hm : IsBag m) : IsBag (evaluate q m) := by
  induction q with
  | idQ => exact hm
  | union q1 q2 ih1 ih2 => exact addW_pos _ _ ih1 ih2
  | join q1 q2 ih1 ih2 => exact joinW_pos _ _ ih1 ih2
  | project g q ih =>
    intro a
    rw [evaluate, projectW_ok]
    exact projectW_pos g (evaluate q m) ih a
  | filter p q ih => exact filterW_pos p _ ih

/-- **THE ONE THEOREM's ℤ→Bool instance** (02 §4's membership-reading),
    honestly bag-restricted: over BAG inputs, evaluate-then-collapse =
    collapse-then-evaluate — the support of the query result IS the
    query over the supports. The bag-premise threads through the
    induction via `evaluate_isBag`; the SIGNED world needs the
    incremental machinery (the old-values rule), not this — that
    boundary is the doctrine's honesty, not a defect. -/
theorem evaluate_supportCollapse
    (q : Query Row) (m : Weighted Int Row) (hm : IsBag m) :
    supportCollapseW (evaluate q m) = evaluate q (supportCollapseW m) := by
  induction q with
  | idQ => rfl
  | union q1 q2 ih1 ih2 =>
    apply extW
    intro a
    have hA : IsBag (evaluate q1 m) := evaluate_isBag q1 m hm
    have hB : IsBag (evaluate q2 m) := evaluate_isBag q2 m hm
    rw [weightW_supportCollapseW]
    simp only [evaluate, addW_ok, wkindInt_add, collapse_add (hA a) (hB a),
      wkindBool_add, ← ih1, ← ih2, ← weightW_supportCollapseW]
  | join q1 q2 ih1 ih2 =>
    apply extW
    intro a
    have hA : IsBag (evaluate q1 m) := evaluate_isBag q1 m hm
    have hB : IsBag (evaluate q2 m) := evaluate_isBag q2 m hm
    rw [weightW_supportCollapseW]
    simp only [evaluate, joinW_ok, wkindInt_mul, collapse_mul (hA a) (hB a),
      wkindBool_mul, ← ih1, ← ih2, ← weightW_supportCollapseW]
  | project g q ih =>
    apply extW
    intro b
    rw [weightW_supportCollapseW]
    simp only [evaluate, projectW_ok]
    rw [← ih]
    exact collapse_projectWeight g (evaluate q m) (evaluate_isBag q m hm) b
  | filter p q ih =>
    apply extW
    intro a
    rw [weightW_supportCollapseW]
    simp only [evaluate, filterW_ok]
    by_cases hpa : p a = true
    · rw [if_pos hpa, if_pos hpa, ← ih, weightW_supportCollapseW]
    · rw [if_neg hpa, if_neg hpa, wkindInt_zero, wkindBool_zero,
          decide_eq_false_iff_not.mpr (by omega)]

/-! ## The ZSet bridge — now the identity -/

/-- The landed `ZSet` IS the ℤ instance (Basic's abbrev:
    `ZSet α = Weighted Int α`), so the old migration bridge is the
    identity — kept as the tests' name for the specialization. Weight-
    and operation-preserving BY DEFINITION. -/
def ofZSet (m : ZSet Row) : Weighted Int Row := m

/-- The identity bridge preserves the weight by definition. -/
theorem weightW_ofZSet (m : ZSet Row) (a : Row) :
    weightW (ofZSet m) a = weight m a := rfl

end ZSet

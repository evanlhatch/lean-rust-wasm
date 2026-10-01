/-
# ZSet.Optimizer — the query algebra's equational theory (02 §6)

Owned by: the ZSet agent (the mandate tree, `zset/`).

notes/v3/02-data-plane.md §6 ("the optimizer is a proof engine") + §4
(the semiring discipline: union adds, join multiplies, projection sums
over preimages): the rewrite rules AS THEOREMS over the weighted
relations — the honest starter set, each proved from the PER-PRIMITIVE
ROWS (`filterW_ok`/`addW_ok`/`joinW_ok`/`projectW_ok`, never a hand
induction where the primitive row covers it):

- **Selection fusion**: `σ p (σ q R) = σ (p ∧ q) R` — the two filters'
  pointwise rows fuse (`filterW_fuse`).
- **Projection-pushdown**: `π g (σ p R) = σ p' (π g R)` when the
  premise holds — and the premise is DATA: "p reads only A" spelled as
  the FACTORING `p = p' ∘ g` (`ReadsThrough`), carried by the theorem
  (`projectW_pushdown`). An unfactored predicate's pushdown is FALSE —
  the negative control pins the difference concretely.
- **Join-commutativity's weight face**: the weights' multiplication
  commutes (the Nat/ℤ/Bool instances), so the joined WEIGHT at each
  row is symmetric. THE ORDER NOTE: the join's output row order is the
  observer's discipline — the honest claim is weight-equality, not
  row-order (`joinW_comm_weight`).
- **Union-idempotence under Bool**: over the set-semantics weights the
  add is OR, so `R ∪ R = R` (`addW_idem_bool`). Over ℤ it is FALSE
  (2 ≠ 1) — the restriction is load-bearing, not decorative.
- **Union-commutativity under the observer**: the add commutes for
  EVERY `WKind` (the law is a field), so `R ∪ S = S ∪ R` as relations
  (`evaluate_union_comm`) — the observer discipline named: this is the
  weight/canonical face, not an output ROW order.
- **Join-associativity's weight face**: the regrouping
  `(A⋈B)⋈C ≡ A⋈(B⋈C)` — with multiplication's associativity as the
  PREMISE (mul_assoc is NOT a `WKind` field, unlike add_assoc — the
  premise discipline; the join's cross term is the Change-side face,
  03 §9). Landed as the pointwise weight row (`joinW_assoc_weight`),
  its three instances, and the lifted relation equality
  (`evaluate_join_assoc`).
- **Selection-through-join's filter faces**: the filter after a
  projection is the projection of the pulled-back filter
  (`filterW_projectW`) — the general row the typed
  selection-through-join rule rides; and a selection on a
  constant-false predicate is the empty relation (`filterW_false`) —
  the feasibility discipline's consumer.
- **Projection cascades**: `π_A (π_B R) = π_A R` when the outer pick
  factors through the inner — the factoring witness AS DATA
  (`projectW_cascade`, the sublist premise's face at the row-map
  layer), lifted through `evaluate` (`evaluate_project_cascade`).
- **The empty-relation annihilators**: `zeroW` is the add-identity and
  the join/filter/project annihilator (`joinW_zeroW_left`,
  `joinW_zeroW_right`, `filterW_zeroW`, `projectW_zeroW`), and the
  fragment evaluates an empty input to the empty relation
  (`evaluate_zeroW`).

Each primitive row lifts through the fragment's `evaluate` by ONE
unfolding step — the lifted forms (`evaluate_filter_fuse`,
`evaluate_project_pushdown`, `evaluate_join_comm_weight`,
`evaluate_union_idem_bool`) are the runtime plans' rewrite library; the
typed face (`Query.Optimize`) consumes the SAME rows, which is 02 §6's
"the SAME rewrite library improves runtime plans and shrinks proof
obligations".

The five questions (notes/v3/01-core.md):
- **Root**: the data plane — §6's proof-engine foundation, stated over
  §4's weighted relations.
- **Carrier grade**: none of its own — consumes `Weighted K Row` +
  `Query` + `evaluate` (Relation's), never re-carries.
- **Spine reading**: none — the rewrite theory the optimizer lanes
  consume.
- **Ladder rung**: hand theorems of the small kind — the per-primitive
  rows, one unfolding each to the lifted forms.
- **Gate rows**: the axiom report + ZSetTests.Optimizer's pins (the
  rules' positive pins + the mandatory negative controls: the
  premise-less pushdown, the ℤ union-idempotence, the unfactored
  cascade, the non-constant-false filter).

Core-only (imports ZSet.Relation — the cone rule).
-/

import ZSet.Relation

namespace ZSet

variable [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row]

/-! ## Selection fusion — `σ p (σ q R) = σ (p ∧ q) R` -/

/-- THE FUSION ROW: two selections fuse into one carrying the
    conjunction — pointwise, from the two `filterW_ok` rows. -/
theorem filterW_fuse (p q : Row → Bool) (m : Weighted K Row) :
    filterW p (filterW q m) = filterW (fun a => p a && q a) m := by
  apply extW
  intro a
  simp only [filterW_ok]
  by_cases hp : p a = true <;> by_cases hq : q a = true <;>
    simp [hp, hq]

/-- The lifted form: the fragment's nested selections fuse — ONE
    unfolding of `evaluate` onto the primitive row. -/
theorem evaluate_filter_fuse (p q : Row → Bool) (R : Query Row)
    (m : Weighted K Row) :
    evaluate (.filter p (.filter q R)) m
      = evaluate (.filter (fun a => p a && q a) R) m := by
  simp only [evaluate, filterW_fuse]

/-! ## Union-idempotence under Bool — `R ∪ R = R` -/

/-- The Bool weight face: the add is OR, so doubling a relation's
    weight changes nothing. Over ℤ this is FALSE (the negative control
    pins it in ZSetTests) — the rule's premise is the weight kind, as
    data. -/
theorem addW_idem_bool (m : Weighted Bool Row) : addW m m = m := by
  apply extW
  intro a
  rw [addW_ok, wkindBool_add]
  exact Bool.or_self _

/-- The lifted form: the fragment's self-union collapses — the Bool
    instance (set semantics) only. -/
theorem evaluate_union_idem_bool (q : Query Row) (m : Weighted Bool Row) :
    evaluate (.union q q) m = evaluate q m := by
  simp only [evaluate, addW_idem_bool]

/-! ## The empty-relation annihilators -/

/-- `zeroW` annihilates the join from the left: `mul zero a = zero` is
    a `WKind` field. -/
theorem joinW_zeroW_left (m : Weighted K Row) : joinW zeroW m = zeroW := by
  apply extW
  intro a
  rw [joinW_ok, zeroW_ok, WKind.mul_zero]

/-- `zeroW` annihilates the join from the right: the RIGHT zero is not
    a `WKind` field, so the law carries it as an explicit premise (the
    Query.Eval `WKindMulZero` bundle is the instance-carrying face;
    this layer stays cone-pure). -/
theorem joinW_zeroW_right (h0 : ∀ a : K, wk.mul a wk.zero = wk.zero)
    (m : Weighted K Row) : joinW m zeroW = zeroW := by
  apply extW
  intro a
  rw [joinW_ok, zeroW_ok, h0]

/-- The ℤ instance of the right annihilator. -/
theorem joinW_zeroW_right_int (m : Weighted Int Row) :
    joinW m zeroW = zeroW := by
  apply extW
  intro a
  rw [joinW_ok, zeroW_ok, wkindInt_mul, wkindInt_zero]
  exact Int.mul_zero _

/-- The empty relation filters to itself. -/
theorem filterW_zeroW (p : Row → Bool) :
    filterW p (zeroW (K := K)) = zeroW (K := K) := by
  apply extW
  intro a
  rw [filterW_ok, zeroW_ok]
  split <;> rfl

/-- The empty relation projects to itself (the preimage sum over the
    empty rep is empty). -/
theorem projectW_zeroW {β : Type} [CanonKey β] [DecidableEq β]
    (g : Row → β) : projectW g (zeroW (K := K)) = zeroW (K := K) := by
  apply extW
  intro b
  rw [projectW_ok, projectWeightW_eq, zeroW_ok]
  rfl

/-- THE ANNIHILATOR THROUGH THE FRAGMENT: an empty input evaluates to
    the empty relation, for EVERY query of the fragment — the
    per-primitive rows composed (no per-query proofs). -/
theorem evaluate_zeroW (q : Query Row) :
    evaluate q (zeroW (K := K)) = zeroW (K := K) := by
  induction q with
  | idQ => rfl
  | union q1 q2 ih1 ih2 =>
      apply extW
      intro a
      simp only [evaluate, ih1, ih2, addW_ok, zeroW_ok, WKind.zero_add]
  | join q1 q2 ih1 ih2 =>
      simp only [evaluate, ih1, ih2, joinW_zeroW_left]
  | project g q ih => simp only [evaluate, ih, projectW_zeroW]
  | filter p q ih => simp only [evaluate, ih, filterW_zeroW]

/-! ## Join-commutativity's weight face -/

/-- THE ORDER NOTE'S HONEST CLAIM: the join's output ROW order is the
    observer's discipline — what the theory gives is the WEIGHT face:
    with commuting multiplication (the Nat/ℤ/Bool instances), the
    joined weight at each row is symmetric. -/
theorem joinW_comm_weight (hcomm : ∀ x y : K, wk.mul x y = wk.mul y x)
    (m n : Weighted K Row) (a : Row) :
    weightW (joinW m n) a = weightW (joinW n m) a := by
  rw [joinW_ok, joinW_ok]
  exact hcomm _ _

/-- The ℤ instance (signed multiplicities). -/
theorem joinW_comm_weight_int (m n : Weighted Int Row) (a : Row) :
    weightW (joinW m n) a = weightW (joinW n m) a := by
  rw [joinW_ok, joinW_ok, wkindInt_mul, wkindInt_mul]
  exact Int.mul_comm _ _

/-- The Nat instance (multiplicities). -/
theorem joinW_comm_weight_nat (m n : Weighted Nat Row) (a : Row) :
    weightW (joinW m n) a = weightW (joinW n m) a := by
  rw [joinW_ok, joinW_ok, wkindNat_mul, wkindNat_mul]
  exact Nat.mul_comm _ _

/-- The Bool instance (membership). -/
theorem joinW_comm_weight_bool (m n : Weighted Bool Row) (a : Row) :
    weightW (joinW m n) a = weightW (joinW n m) a := by
  rw [joinW_ok, joinW_ok, wkindBool_mul, wkindBool_mul]
  exact Bool.and_comm _ _

/-- The lifted weight face: the fragment's join is weight-symmetric. -/
theorem evaluate_join_comm_weight (hcomm : ∀ x y : K, wk.mul x y = wk.mul y x)
    (q1 q2 : Query Row) (m : Weighted K Row) (a : Row) :
    weightW (evaluate (.join q1 q2) m) a = weightW (evaluate (.join q2 q1) m) a := by
  simp only [evaluate]
  exact joinW_comm_weight hcomm _ _ a

/-! ## Projection-pushdown — the premise as DATA -/

/-- THE PREMISE AS DATA (02 §6): "the selection reads only the
    projected columns" is not a comment — it is the FACTORING: the
    pushed-down predicate `p'` reads the projected rows, and the
    original `p` is `p'` THROUGH the projection map `g`. A `p` with no
    such factor (it reads a dropped column) has NO pushdown — the
    negative control pins the resulting difference concretely. -/
def ReadsThrough (g : Row → β) (p : Row → Bool) (p' : β → Bool) : Prop :=
  ∀ r, p r = p' (g r)

omit ck [DecidableEq Row] in
/-- The list-level row the pushdown rests on: relabeling the FILTERED
    rep weighs like the filtered relabeling, exactly when the filter
    factors through `g`. -/
theorem weightOfW_relabel_filter {β : Type} [DecidableEq β]
    (g : Row → β) (p : Row → Bool) (p' : β → Bool) (h : ReadsThrough g p p') :
    ∀ (l : List (Row × K)) (b : β),
      weightOfW (relabelW g (l.filter (fun e => p e.1))) b
        = if p' b = true then weightOfW (relabelW g l) b else wk.zero := by
  intro l
  induction l with
  | nil => intro b; simp [relabelW, weightOfW]
  | cons e r ih =>
      obtain ⟨k, w⟩ := e
      have hkb : p k = p' (g k) := h k
      intro b
      rw [List.filter_cons]
      by_cases hgt : p k = true
      · rw [if_pos hgt]
        simp only [relabelW, weightOfW, ih b]
        by_cases hgb : g k = b
        · have hp'b : p' b = true := by rw [← hgb, ← hkb]; exact hgt
          rw [if_pos hgb, if_pos hgb, if_pos hp'b, if_pos hp'b]
        · rw [if_neg hgb, if_neg hgb]
      · rw [if_neg hgt]
        simp only [relabelW, weightOfW, ih b]
        by_cases hgb : g k = b
        · have hp'b : p' b = false := by
              rw [← hgb, ← hkb]
              exact false_of_not_eq_true hgt
          rw [if_pos hgb, if_neg (by simp [hp'b]), if_neg (by simp [hp'b])]
        · rw [if_neg hgb]

/-- THE PUSHDOWN'S WEIGHT ROW: projecting the filtered relation weighs
    like filtering the projection — exactly the factored premise. -/
theorem projectW_filter_weight {β : Type} [CanonKey β] [DecidableEq β]
    (g : Row → β) (p : Row → Bool) (p' : β → Bool) (h : ReadsThrough g p p')
    (m : Weighted K Row) (b : β) :
    weightW (projectW g (filterW p m)) b
      = if p' b = true then weightW (projectW g m) b else wk.zero := by
  rw [projectW_ok, projectW_ok, projectWeightW_eq, projectWeightW_eq]
  simp only [filterW, fromListW]
  rw [weightOfW_relabel_canonW g b, weightOfW_relabel_filter g p p' h m.rep b]

/-- THE PUSHDOWN (the rule as an equation between relations):
    `π g (σ p R) = σ p' (π g R)` — with the factoring premise DATA. -/
theorem projectW_pushdown {β : Type} [CanonKey β] [DecidableEq β]
    (g : Row → β) (p : Row → Bool) (p' : β → Bool) (h : ReadsThrough g p p')
    (m : Weighted K Row) :
    projectW g (filterW p m) = filterW p' (projectW g m) := by
  apply extW
  intro b
  rw [projectW_filter_weight g p p' h m b, filterW_ok]

/-! ## Union-commutativity under the observer -/

/-- The lifted face: the fragment's union commutes — as CANONICAL
    relations (the add's commutativity is a `WKind` field). THE
    OBSERVER DISCIPLINE, named: this is the weight/canonical face of
    the reordering, not an output ROW order — at the typed fragment
    the row order is the observer's discipline
    (`Query.Optimize`'s note). -/
theorem evaluate_union_comm (q1 q2 : Query Row) (m : Weighted K Row) :
    evaluate (.union q1 q2) m = evaluate (.union q2 q1) m := by
  apply extW
  intro a
  simp only [evaluate, addW_ok]
  exact wk.add_comm _ _

/-! ## Join-associativity's weight face -/

/-- THE REGROUPING'S WEIGHT ROW: `(A⋈B)⋈C ≡ A⋈(B⋈C)` pointwise — with
    multiplication's associativity as the PREMISE (mul_assoc is NOT a
    `WKind` field, unlike add_assoc — the premise discipline). The
    join's cross term (03 §9) is the Change-side face: the INCREMENTAL
    form of this regrouping is where it lives, not here. -/
theorem joinW_assoc_weight
    (hassoc : ∀ x y z : K, wk.mul (wk.mul x y) z = wk.mul x (wk.mul y z))
    (m n p : Weighted K Row) (a : Row) :
    weightW (joinW (joinW m n) p) a = weightW (joinW m (joinW n p)) a := by
  simp only [joinW_ok]
  exact hassoc _ _ _

/-- The ℤ instance (signed multiplicities). -/
theorem joinW_assoc_weight_int (m n p : Weighted Int Row) (a : Row) :
    weightW (joinW (joinW m n) p) a = weightW (joinW m (joinW n p)) a := by
  refine joinW_assoc_weight (fun x y z => ?_) m n p a
  simp only [wkindInt_mul]
  exact Int.mul_assoc _ _ _

/-- The Nat instance (multiplicities). -/
theorem joinW_assoc_weight_nat (m n p : Weighted Nat Row) (a : Row) :
    weightW (joinW (joinW m n) p) a = weightW (joinW m (joinW n p)) a := by
  refine joinW_assoc_weight (fun x y z => ?_) m n p a
  simp only [wkindNat_mul]
  exact Nat.mul_assoc _ _ _

/-- The Bool instance (membership). -/
theorem joinW_assoc_weight_bool (m n p : Weighted Bool Row) (a : Row) :
    weightW (joinW (joinW m n) p) a = weightW (joinW m (joinW n p)) a := by
  refine joinW_assoc_weight (fun x y z => ?_) m n p a
  simp only [wkindBool_mul]
  exact Bool.and_assoc _ _ _

/-- The lifted regrouping: the fragment's join re-brackets — the full
    relation equality (the canonical rep makes the weight face real at
    the untyped carrier; no schema concat intervenes HERE — the typed
    fragment's append-assoc zone is named at `Query.Optimize`). -/
theorem evaluate_join_assoc
    (hassoc : ∀ x y z : K, wk.mul (wk.mul x y) z = wk.mul x (wk.mul y z))
    (R1 R2 R3 : Query Row) (m : Weighted K Row) :
    evaluate (.join (.join R1 R2) R3) m = evaluate (.join R1 (.join R2 R3)) m := by
  apply extW
  intro a
  simp only [evaluate, joinW_ok]
  exact hassoc _ _ _

/-! ## The filter's two faces (through projections; constant-false) -/

/-- THE FILTER-THROUGH-PROJECTION ROW: filtering the projected relation
    is the projection of the pulled-back filter — the general row the
    typed selection-through-join rule composes with the join's filter
    face. `projectW_pushdown` is the factored special case. -/
theorem filterW_projectW {β : Type} [CanonKey β] [DecidableEq β]
    (p : β → Bool) (g : Row → β) (m : Weighted K Row) :
    filterW p (projectW g m) = projectW g (filterW (fun a => p (g a)) m) := by
  apply extW
  intro b
  rw [filterW_ok, projectW_filter_weight g (fun a => p (g a)) p (fun _ => rfl) m b]

/-- THE CONSTANT-FOLD ROW: a selection on a constant-false predicate
    is the empty relation — the feasibility discipline's consumer: a
    checked-infeasible condition folds the selection away. -/
theorem filterW_false (p : Row → Bool) (h : ∀ a, p a = false)
    (m : Weighted K Row) : filterW p m = zeroW (K := K) := by
  apply extW
  intro a
  rw [filterW_ok, h a, zeroW_ok]
  simp

/-- The lifted fold: the fragment's dead selection evaluates empty. -/
theorem evaluate_filter_false (p : Row → Bool) (h : ∀ a, p a = false)
    (R : Query Row) (m : Weighted K Row) :
    evaluate (.filter p R) m = zeroW (K := K) := by
  simp only [evaluate, filterW_false p h]

/-! ## Projection cascades — the sublist premise as DATA -/

omit wk ck [DecidableEq Row] in
/-- Relabeling respects pointwise-equal maps (the cascade's congruence
    face). -/
theorem relabelW_congr {β : Type} (f f' : Row → β)
    (h : ∀ r, f r = f' r) :
    ∀ l : List (Row × K), relabelW f l = relabelW f' l := by
  intro l
  induction l with
  | nil => rfl
  | cons e r ih =>
    obtain ⟨k, w⟩ := e
    simp only [relabelW, h k, ih]

omit ck [DecidableEq Row] in
/-- The relabeling's composition: relabeling twice weighs like labeling
    once through the composite (the cascade's arithmetic). -/
theorem weightOfW_relabel_comp {β γ : Type} [CanonKey β] [DecidableEq β]
    [CanonKey γ] [DecidableEq γ]
    (h : Row → β) (g : β → γ) :
    ∀ (l : List (Row × K)) (c : γ),
      weightOfW (relabelW g (relabelW h l)) c
        = weightOfW (relabelW (fun r => g (h r)) l) c := by
  intro l
  induction l with
  | nil => intro c; rfl
  | cons e r ih =>
    obtain ⟨k, w⟩ := e
    intro c
    simp only [relabelW, weightOfW, ih]

/-- THE CASCADE ROW (the projection's composition): `π g1 (π g2 R) =
    π (g1 ∘ g2) R` — no premise at all, the preimage sums compose.
    The RULE's face (the sublist premise as data) is
    `projectW_cascade` below. -/
theorem projectW_compose {β γ : Type} [CanonKey β] [DecidableEq β]
    [CanonKey γ] [DecidableEq γ]
    (g1 : β → γ) (g2 : Row → β) (m : Weighted K Row) :
    projectW g1 (projectW g2 m) = projectW (fun r => g1 (g2 r)) m := by
  apply extW
  intro c
  rw [projectW_ok, projectWeightW_eq, projectW_ok, projectWeightW_eq]
  -- the inner projection's rep is canonical — strip it
  show weightOfW (relabelW g1 (canonW (relabelW g2 m.rep))) c
      = weightOfW (relabelW (fun r => g1 (g2 r)) m.rep) c
  rw [weightOfW_relabel_canonW, weightOfW_relabel_comp g2 g1]

/-- THE CASCADE RULE: `π_A (π_B R) = π_A R` — with the "A's pick reads
    through B's pick" premise as the FACTORING DATA (`gA = g1 ∘ g2`
    pointwise — the sublist premise's face at the row-map layer). A
    `gA` that does not factor has NO cascade — the negative control
    pins the difference concretely. -/
theorem projectW_cascade {β γ : Type} [CanonKey β] [DecidableEq β]
    [CanonKey γ] [DecidableEq γ]
    (g1 : β → γ) (g2 : Row → β) (gA : Row → γ)
    (h : ∀ r, gA r = g1 (g2 r)) (m : Weighted K Row) :
    projectW g1 (projectW g2 m) = projectW gA m := by
  rw [projectW_compose g1 g2]
  apply extW
  intro c
  rw [projectW_ok, projectWeightW_eq, projectW_ok, projectWeightW_eq,
    relabelW_congr (fun r => g1 (g2 r)) gA (fun r => (h r).symm) m.rep]

/-- The lifted cascade: the fragment's nested projections fold — ONE
    unfolding of `evaluate` onto the rule row. -/
theorem evaluate_project_cascade (g1 g2 gA : Row → Row)
    (h : ∀ r, gA r = g1 (g2 r)) (R : Query Row) (m : Weighted K Row) :
    evaluate (.project g1 (.project g2 R)) m = evaluate (.project gA R) m := by
  simp only [evaluate, projectW_cascade g1 g2 gA h]

/-- The lifted form: the fragment's selection under a projection
    pushes down — the typed optimizer's rule row (the `Query.Optimize`
    face consumes THIS row). -/
theorem evaluate_project_pushdown (g : Row → Row) (p p' : Row → Bool)
    (h : ReadsThrough g p p') (R : Query Row) (m : Weighted K Row) :
    evaluate (.project g (.filter p R)) m
      = evaluate (.filter p' (.project g R)) m := by
  simp only [evaluate, projectW_pushdown g p p' h]

end ZSet

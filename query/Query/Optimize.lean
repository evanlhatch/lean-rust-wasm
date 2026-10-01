/-
# Query.Optimize — the checked rewriter (02 §6's proof engine)

Owned by: the Query agent (the mandate tree, `query/`).

notes/v3/02-data-plane.md §6 ("the optimizer is a proof engine: an
untrusted optimizer proposes the rewrite sequence; the kernel checks
it") + 04 §3's certificate pattern (untrusted search + small verified
checker; a generated proof term checked by the kernel is not less
trustworthy than a handwritten one).

What lands here — the typed face of the SAME rewrite library whose
weighted-relation rows live in `ZSet.Optimizer` (this file CONSUMES
those rows; nothing is re-proved):

- The rule theorems over the typed fragment: selection fusion
  (`evalQ_select_fuse`), the pushdown through a projection with the
  "reads only the kept columns" premise as the FACTORING WITNESS DATA
  (`evalQ_select_project_pushdown`), union-idempotence under Bool
  (`evalQ_union_idem_bool`), selection-through-join with the "reads
  only the LEFT schema's columns" factoring as data
  (`evalQ_select_join_pushdown`), the redundant-selection fold
  (`evalQ_select_true`), the constant-false fold's weight face
  (`evalQ_select_false`), and union-commutativity under the Bool
  observer (`evalQ_union_comm_bool`).
- `OptStep` — one rewrite STEP: the rule cited (the constructor IS the
  rule's name) + the premises discharged (the witness rides the
  constructor as a proof field). THE CHECKER IS LEAN'S KERNEL: a step
  that mis-cites a rule or lacks a witness does not typecheck.
- `Cert` — the rewrite SEQUENCE (the certificate): a chain of steps
  whose source/target plans must line up by construction.
- `Cert.eval_eq` / `Cert.qsat_iff` / `Optimized.agrees` — THE
  OPTIMIZER'S CONTRACT (02 §6's exact shape): the certificate's
  optimized plan + the proof that every valid database gives
  equivalent results. The observer is the Bool weight (set semantics —
  the bridge's reading); the spec face composes through the LANDED
  bridge `evalQ_true_iff` (`Cert.qsat_iff`), never a second bridge.
- The refusal teeth as theorems: a premise-less pushdown's
  constructor payload refuses a wrong `p'` (the data-level pin), a
  union step fuses only identical branches
  (`OptStep.union_branches`), a step from a rule-inapplicable shape
  does not exist (`OptStep.noStepFromBadShape`), and no step exists
  from a join- or projection-headed plan (`OptStep.noStepFromJoin`,
  `OptStep.noStepFromProject`) — the kernel's refusals PINNED, so
  they cannot rot.
- THE MULTI-SCHEMA ZONE, honestly named: the current `Cert` is
  SINGLE-schema, and every `OptStep` constructor PRESERVES the result
  schema — per rule, by construction (the constructor's indices).
  The rules that CHANGE the result schema are NOT steps: join
  associativity's typed regrouping moves between `(ga ++ gb) ++ gc`
  and `ga ++ (gb ++ gc)` (the append-assoc zone), and the projection
  cascade's single-`Cols` fold needs a composite column datum whose
  computed fields must match the nested one definitionally. Both live
  at the ZSet weight face (`ZSet.Optimizer`'s `evaluate_join_assoc` /
  `projectW_cascade`); the boundary is PINNED by the kernel
  (`noStepFromJoin`/`noStepFromProject`).

The honest boundary: the rules hold for every weight kind EXCEPT
union-idempotence, which is Bool-only (over ℤ doubling is 2 ≠ 1 — the
contract's observer is the set-semantics weight, named not hidden).
Join-commutativity's weight face lives at the ZSet layer: at the typed
fragment a commuted join changes the RESULT SCHEMA (`ga ++ gb` vs
`gb ++ ga`) — the row order is the observer's discipline, not a typed
rewrite.

The five questions (notes/v3/01-core.md):
- **Root**: the data plane — §6's optimizer interface over the typed
  fragment.
- **Carrier grade**: none of its own — `Q`/`evalQ`/`QSat` consumed,
  never re-carried.
- **Spine reading**: none — the proof-engine face the query lanes
  consume.
- **Ladder rung**: hand theorems of the small kind — each rule is the
  ZSet layer's per-primitive row, one unfolding into the typed
  fragment; the contract composes the landed bridge.
- **Gate rows**: the axiom report + QueryTests.Optimize's pins (the
  qlang! pipeline end-to-end + the refusal teeth + the negative
  controls).

Core-only (imports Query.Eval + ZSet.Optimizer — the cone rule).
-/

import Query.Eval
import ZSet.Optimizer

namespace Query

open SchemaCore ZSet

/-! ## The rule theorems (the SAME rewrite library, the typed face) -/

/-- SELECTION FUSION: `select p (select q inner)` = one selection
    carrying the conjunction — `ZSet.filterW_fuse`'s row, unfolded
    once into the typed fragment. -/
theorem evalQ_select_fuse {fs gs : List Field} [WKind K]
    (p q : Pred gs) (inner : Q fs gs) (m : Weighted K (RowVals fs)) :
    evalQ (.select p (.select q inner)) m
      = evalQ (.select (Pred.and p q) inner) m := by
  apply extW
  intro a
  simp only [evalQ, filterW_ok, Pred.check]
  by_cases h1 : p.check a = true <;> by_cases h2 : q.check a = true <;>
    simp [h1, h2]

/-- UNION-IDEMPOTENCE under Bool (set semantics): the self-union
    collapses. Over ℤ the claim is FALSE (the ZSetTests negative
    control pins it) — the weight kind is the rule's premise, as
    data. -/
theorem evalQ_union_idem_bool {fs gs : List Field}
    (q : Q fs gs) (m : Weighted Bool (RowVals fs)) :
    evalQ (.union q q) m = evalQ q m := by
  simp only [evalQ, ZSet.addW_idem_bool]

/-- PROJECTION-PUSHDOWN: `select p (project c inner)` = `project c
    (select p' inner)` — with the "p reads only the kept columns"
    premise as the FACTORING WITNESS: `p'` on the source schema agrees
    with `p` through the pick. `ZSet.projectW_pushdown`'s row,
    unfolded once. A `p'` without the agreement does not witness —
    the witness's type refuses. -/
theorem evalQ_select_project_pushdown {fs gs : List Field} [WKind K]
    {c : Cols gs} {inner : Q fs gs}
    {p : Pred (c.fields gs)} {p' : Pred gs}
    (hw : ∀ r : RowVals gs, p.check (c.pick gs r) = p'.check r)
    (m : Weighted K (RowVals fs)) :
    evalQ (.select p (.project c inner)) m
      = evalQ (.project c (.select p' inner)) m := by
  apply extW
  intro b
  simp only [evalQ]
  rw [← ZSet.projectW_pushdown (c.pick gs) p'.check p.check
    (fun r => (hw r).symm) (evalQ inner m)]

/-- THE JOIN'S FILTER FACE: filtering the joined pairs is joining the
    LEFT-filtered pairs — with the factoring of `q` through the left
    row as DATA. The join's weight formula's right-zero bundle
    (`WKindMulZero`) rides the proof: the off branch multiplies the
    zeroed left weight into the right. -/
theorem joinPairsW_filter_left [WKind K] [WKindMulZero K]
    {ga gb : List Field}
    (m : Weighted K (RowVals ga)) (n : Weighted K (RowVals gb))
    (onp : RowVals ga → RowVals gb → Bool)
    (q : RowVals ga × RowVals gb → Bool) (q' : RowVals ga → Bool)
    (h : ∀ (la : RowVals ga) (rb : RowVals gb), q (la, rb) = q' la) :
    filterW q (joinPairsW m n onp) = joinPairsW (filterW q' m) n onp := by
  apply extW
  intro ab
  obtain ⟨la, rb⟩ := ab
  rw [filterW_ok (p := q) (m := joinPairsW m n onp) (a := (la, rb)),
    joinPairsW_ok m n onp la rb, h la rb,
    joinPairsW_ok (filterW q' m) n onp la rb,
    filterW_ok (p := q') (m := m) (a := la)]
  by_cases hon : onp la rb = true <;> by_cases hq : q' la = true <;>
    simp [hon, hq]
  · exact (WKind.mul_zero _).symm

/-- SELECTION-THROUGH-JOIN: `select p (join ln rn q1 q2) = join ln rn
    (select p' q1) q2` — with the "p reads only the LEFT schema's
    columns" premise as the FACTORING WITNESS: `p` through the joined
    row's append agrees with `p'` on the left row. The join's filter
    face composes the ZSet rows: `filterW_projectW` (the filter after
    the append-projection is the projection of the pulled-back filter)
    with `joinPairsW_filter_left` (the pulled-back filter is the LEFT
    side's filter). A `p` reading a RIGHT column has no witness —
    the constructor's payload refuses. -/
theorem evalQ_select_join_pushdown [WKind K] [WKindMulZero K]
    {fs ga gb : List Field} {p : Pred (ga ++ gb)} {p' : Pred ga}
    {ln rn : String} {q1 : Q fs ga} {q2 : Q fs gb}
    (hw : ∀ (la : RowVals ga) (rb : RowVals gb),
      p.check (Row.append la rb) = p'.check la)
    (m : Weighted K (RowVals fs)) :
    evalQ (.select p (.join ln rn q1 q2)) m
      = evalQ (.join ln rn (.select p' q1) q2) m := by
  simp only [evalQ]
  rw [filterW_projectW, joinPairsW_filter_left]
  exact fun la rb => hw la rb

/-- THE REDUNDANT-SELECTION FOLD: a selection on a constant-true
    predicate is its input — the witness rides the premise as data
    (`fun _ => rfl` for a `.lit true`). -/
theorem evalQ_select_true [WKind K] {fs gs : List Field} {p : Pred gs}
    {inner : Q fs gs} (h : ∀ r : RowVals gs, p.check r = true)
    (m : Weighted K (RowVals fs)) :
    evalQ (.select p inner) m = evalQ inner m := by
  apply extW
  intro r
  simp [evalQ, filterW_ok, h r]

/-- THE CONSTANT-FALSE FOLD's weight face: a selection on a
    constant-false predicate is the EMPTY relation — the feasibility
    discipline's consumer: a checked-infeasible condition folds the
    selection away. The honest boundary, named: the FRAGMENT has no
    empty-plan node, so this is a weight face (to `fromListW []`), not
    an `OptStep` — a fold-to-empty plan needs the fragment's empty
    node first. -/
theorem evalQ_select_false [WKind K] {fs gs : List Field} {p : Pred gs}
    {inner : Q fs gs} (h : ∀ r : RowVals gs, p.check r = false)
    (m : Weighted K (RowVals fs)) :
    evalQ (.select p inner) m = (zeroW (K := K) : Weighted K (RowVals gs)) := by
  apply extW
  intro r
  simp [evalQ, filterW_ok, h, zeroW_ok]

/-- UNION-COMMUTATIVITY under the observer: the branches reorder — as
    CANONICAL relations over the Bool weight (the contract's observer,
    set semantics; the add's OR commutes). The observer discipline,
    named: this is the weight/canonical face, not an output ROW
    order. -/
theorem evalQ_union_comm_bool {fs gs : List Field} (q1 q2 : Q fs gs)
    (m : Weighted Bool (RowVals fs)) :
    evalQ (.union q1 q2) m = evalQ (.union q2 q1) m := by
  apply extW
  intro r
  simp only [evalQ, addW_ok, wkindBool_add]
  exact Bool.or_comm _ _

/-! ## The checked rewriter (04 §3's certificate pattern) -/

/-- ONE REWRITE STEP: the rule cited (the constructor's name) + the
    premises discharged (the witness rides the constructor as a proof
    field). THE CHECKER IS LEAN'S KERNEL: the untrusted proposer
    emits the step's data; a step that mis-cites a rule, targets an
    uninvolved plan, or lacks a witness does not typecheck — 04 §3's
    "generated evidence, independently checked against the
    authoritative declaration".

    SCHEMA PRESERVATION, PER RULE (the multi-schema zone's honest
    disposition): every constructor's source and target indices are
    the ONE result schema, by construction — `selFuse`/`selTrue`
    (selection never re-shapes), `projPush` (the select/project
    reorder over one shape), `selJoinPush` (the selection moves
    across the join, the appended schema unchanged), `unionIdem`/
    `unionComm` (the branches share the schema). The rules that
    CHANGE the result shape are NOT here — see the module header's
    multi-schema zone note; the boundary is pinned by
    `noStepFromJoin`/`noStepFromProject`. -/
inductive OptStep : {fs : List Field} → {gs : List Field} →
    Q fs gs → Q fs gs → Type where
  | selFuse {fs gs : List Field} {p q : Pred gs} {inner : Q fs gs} :
      OptStep (.select p (.select q inner)) (.select (Pred.and p q) inner)
  | projPush {fs gs : List Field} {c : Cols gs} {inner : Q fs gs}
      {p : Pred (c.fields gs)} {p' : Pred gs}
      (hw : ∀ r : RowVals gs, p.check (c.pick gs r) = p'.check r) :
      OptStep (.select p (.project c inner)) (.project c (.select p' inner))
  | selJoinPush {fs ga gb : List Field} {p : Pred (ga ++ gb)} {p' : Pred ga}
      {ln rn : String} {q1 : Q fs ga} {q2 : Q fs gb}
      (hw : ∀ (la : RowVals ga) (rb : RowVals gb),
        p.check (Row.append la rb) = p'.check la) :
      OptStep (.select p (.join ln rn q1 q2))
        (.join ln rn (.select p' q1) q2)
  | selTrue {fs gs : List Field} {p : Pred gs} {inner : Q fs gs}
      (h : ∀ r : RowVals gs, p.check r = true) :
      OptStep (.select p inner) inner
  | unionIdem {fs gs : List Field} {q : Q fs gs} :
      OptStep (.union q q) q
  | unionComm {fs gs : List Field} {q1 q2 : Q fs gs} :
      OptStep (.union q1 q2) (.union q2 q1)

/-- THE CERTIFICATE: the rewrite SEQUENCE — a chain of steps whose
    source/target plans line up by construction (a step targeting a
    plan the chain is not at does not typecheck). -/
inductive Cert : {fs : List Field} → {gs : List Field} →
    Q fs gs → Q fs gs → Type where
  | done {fs gs : List Field} {q : Q fs gs} : Cert q q
  | step {fs gs : List Field} {q mid : Q fs gs}
      (s : OptStep q mid) {out : Q fs gs} (rest : Cert mid out) : Cert q out

/-- One step's checked contract: the step's target evaluates exactly
    as its source — the rule theorems, dispatched by the kernel's own
    rule check (the `cases`). -/
theorem OptStep.eval_eq {fs gs : List Field} {q mid : Q fs gs}
    (s : OptStep q mid) (rows : List (RowVals fs)) :
    evalQ mid (tableW (K := Bool) rows true)
      = evalQ q (tableW (K := Bool) rows true) := by
  cases s with
  | selFuse => rw [evalQ_select_fuse (K := Bool)]
  | projPush hw => rw [evalQ_select_project_pushdown hw (K := Bool)]
  | selJoinPush hw => rw [evalQ_select_join_pushdown hw (K := Bool)]
  | selTrue h => rw [evalQ_select_true h (K := Bool)]
  | unionIdem => rw [evalQ_union_idem_bool]
  | unionComm => rw [evalQ_union_comm_bool]

/-- **THE OPTIMIZER'S CONTRACT** (02 §6's exact shape): the
    certificate's optimized plan + the proof that every valid database
    gives equivalent results — the observer is the Bool weight (set
    semantics), every step discharged by its rule theorem. -/
theorem Cert.eval_eq {fs gs : List Field} {q out : Q fs gs}
    (c : Cert q out) (rows : List (RowVals fs)) :
    evalQ out (tableW (K := Bool) rows true)
      = evalQ q (tableW (K := Bool) rows true) := by
  induction c with
  | done => rfl
  | step s rest ih => rw [ih]; exact OptStep.eval_eq s rows

/-- The spec face of the contract: the optimized plan and the original
    satisfy the SAME rows — composed through the LANDED bridge
    (`evalQ_true_iff`), never a second bridge. -/
theorem Cert.qsat_iff {fs gs : List Field} {q out : Q fs gs}
    (c : Cert q out) (rows : List (RowVals fs)) (r : RowVals gs) :
    QSat fs rows out r ↔ QSat fs rows q r := by
  rw [← evalQ_true_iff, ← evalQ_true_iff, c.eval_eq rows]

/-- THE OPTIMIZER'S OUTPUT (02 §6's interface): the optimized query +
    the certificate — "optimized query + proof: every valid database
    gives equivalent results" as a TYPE. -/
structure Optimized {fs gs : List Field} (q : Q fs gs) : Type where
  plan : Q fs gs
  cert : Cert q plan

theorem Optimized.agrees {fs gs : List Field} {q : Q fs gs}
    (o : Optimized q) (rows : List (RowVals fs)) :
    evalQ o.plan (tableW (K := Bool) rows true)
      = evalQ q (tableW (K := Bool) rows true) :=
  o.cert.eval_eq rows

/-! ## The refusal teeth (the kernel's refusals, pinned) -/

-- The pushdown's premise is the constructor's PAYLOAD (the `hw`
-- field's type): a proposer without the factoring has no step to
-- give — the kernel refuses the argument. The extraction face (any
-- pushdown step YIELDS its witness) is the computed-index wall's
-- residue at this layer — the SAME wall F2 named (the recursor's
-- application never unifies `Cols.fields`'s computed index; the
-- `QSat.weight_true` precedent); the tooth's load-bearing pin is
-- DECIDABLE at the data level and lives in QueryTests.Optimize (the
-- wrong `p'`'s witness refuted by `decide` at a row).

/-- A union step fuses only IDENTICAL branches — the idempotence's
    shape is checked, never assumed. -/
theorem OptStep.union_branches {fs gs : List Field} {q1 q2 : Q fs gs}
    (s : OptStep (.union q1 q2) q1) : q1 = q2 := by
  cases s
  rfl

/-- A BAD REWRITE SEQUENCE REFUSES: from a selection over a union,
    the theory's ONLY step is the redundant-fold (the `selTrue` fold
    rides ANY inner plan); the fusion and pushdown rules do not apply
    — the kernel's case analysis pins the fold as the unique shape.
    (The tooth's honest REFORMULATION: with `selTrue` landed, the old
    "no step at all" pin rotted — the extended theory's case analysis
    is the check, never assumed.) -/
theorem OptStep.noStepFromBadShape {fs gs : List Field} {p : Pred gs}
    {q1 q2 : Q fs gs} {out : Q fs gs}
    (s : OptStep (.select p (.union q1 q2)) out) : out = Q.union q1 q2 := by
  cases s with
  | selTrue _ => rfl

/-- ANY step's source is SELECT- or UNION-headed (the rule theorems'
    shapes) — the variable-indexed form keeps `cases` un-stuck (the
    schema indices stay variables). -/
theorem OptStep.srcSelectOrUnion {fs hx : List Field} {q : Q fs hx}
    {out : Q fs hx} (s : OptStep q out) :
    (∃ (p : Pred hx) (inner : Q fs hx), q = Q.select p inner)
      ∨ (∃ (u v : Q fs hx), q = Q.union u v) := by
  cases s with
  | selFuse => exact Or.inl ⟨_, _, rfl⟩
  | projPush _ => exact Or.inl ⟨_, _, rfl⟩
  | selJoinPush _ => exact Or.inl ⟨_, _, rfl⟩
  | selTrue _ => exact Or.inl ⟨_, _, rfl⟩
  | unionIdem => exact Or.inr ⟨_, _, rfl⟩
  | unionComm => exact Or.inr ⟨_, _, rfl⟩

/-- THE MULTI-SCHEMA ZONE'S KERNEL PIN: no step of the theory has a
    JOIN-headed source — the join's regrouping (associativity's
    append-assoc zone) and the commuted join's schema change
    (`ga ++ gb` vs `gb ++ ga`) are the ZSet weight face's business,
    not a typed step. -/
theorem OptStep.noStepFromJoin {fs ga gb : List Field} {ln rn : String}
    {q1 : Q fs ga} {q2 : Q fs gb} {out : Q fs (ga ++ gb)}
    (s : OptStep (.join ln rn q1 q2) out) : False := by
  rcases s.srcSelectOrUnion with ⟨_, _, heq⟩ | ⟨_, _, heq⟩
  · exact absurd heq (by simp)
  · exact absurd heq (by simp)

/-- THE MULTI-SCHEMA ZONE'S KERNEL PIN (the projection's face): no
    step of the theory has a PROJECTION-headed source — the cascade's
    single-`Cols` fold needs the composite column datum (the computed
    fields must match definitionally), so the cascade lives at the
    ZSet weight face (`projectW_cascade`), not as a typed step. -/
theorem OptStep.noStepFromProject {fs gs : List Field} {c : Cols gs}
    {inner : Q fs gs} {out : Q fs (c.fields gs)}
    (s : OptStep (.project c inner) out) : False := by
  rcases s.srcSelectOrUnion with ⟨_, _, heq⟩ | ⟨_, _, heq⟩
  · exact absurd heq (by simp)
  · exact absurd heq (by simp)

end Query

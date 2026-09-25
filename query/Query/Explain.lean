/-
# Query.Explain — the explanations lane: why present / why absent as data

Owned by: the explanations-lane agent (the mandate tree, `query/`).
Driving decisions: notes/v3/02-data-plane.md §11 (explanations are
QUERY SEMANTICS: why present → the supporting derivations; why absent
→ the blocking conditions under DECLARED completeness assumptions;
never a generic invariant failure) + notes/v3/02-data-plane.md §2
(the same expression as query and explanation source) +
notes/v3/02-data-plane.md §8 (absence claims need knowing the input is
complete — the knowledge is a declared assumption, never a blanket
claim).

What lands here (the honest minimal):

- `Derivation` — THE WHY-PRESENT DISCIPLINE: a query answer's
  supporting derivation AS DATA — which facts and which rules produced
  the answer, riding the query's own structure (one constructor per
  `QSat` face: the base fact, the filter's acceptance, the
  projection's preimage, the union's disjunct, the join's paired
  rows). The bridge runs BOTH ways (pattern #1): `Derivation.qsat`
  (a derivation is sound — it implies the spec) and
  `QSat.derivation_nonempty` (every present answer HAS a derivation —
  the derivation is never missing, only unrendered).
- `Blocker` — THE WHY-ABSENT DISCIPLINE's structural face: one
  blocking condition as data over the fragment's structure — the base
  miss, the filter's failed predicate (with the sub-answer PRESENT —
  the honest complete face), the projection's exhausted preimages
  (the exhaustive ∀ face — one live preimage would resurrect the
  answer), the union's double absence. The join's per-row face is the
  KEY-JOIN's (`KeyJoinMiss`): the general join's result row
  decomposes ambiguously (many pairs append to one row), so a
  per-decomposition blocker would not prove absence — the key-join
  drives from the right row and its absence face is honest
  (`KeyJoinMiss.not_mem`).
- `Completeness` + `WhyAbsent` — THE HONESTY TOOTH: a why-absent
  answer is the blocking condition RIDING the declared completeness
  assumption; WITHOUT the declaration the only honest answer is
  `.refusal` — a refusal, never a guess. The type FORCES this: the
  `.blocked` constructor cannot be built without a `Completeness`
  value, and `WhyAbsent.verdict_sound` proves a blocked answer's
  absence claim (over Bool weights, through `blocker_absent`); a
  refusal makes no claim at all.

Deliberate exclusions (the leftover rule, each names its reason): the
executable derivation FINDER (a decision procedure extracting the
derivation from the evaluation — the existence face is proved here;
the finder lands with its first consumer that cannot supply the
derivation by construction); sensitivity analysis ("what would change
the result" — the inspector's what-if lane is that face over the
journal; a query-fragment sensitivity calculus has no consumer yet);
stratified-negation absence ("why absent because NOTHING matches" —
negation is outside the fragment, 02 §2's named boundary).

The five questions (notes/v3/01-core.md):
- **Root**: the data plane's explanation face (02 §11) — the query
  semantics' third consumer of the ONE expression.
- **Carrier grade**: the derivation/blocker as GADT data over the
  fragment's indices — a derivation for a different query or row is
  unconstructible.
- **Spine reading**: none — the explanations ride the query's
  structure and the evaluation's bridge.
- **Ladder rung**: hand theorems of the small kind — the bridge's two
  faces (one structural induction each over the fragment/QSat) and
  the blocker-absence induction over the fragment.
- **Gate rows**: the axiom report + the explanations suites in
  QueryTests (the worked derivations, the refusal tooth, the
  mandatory negative controls).

Core-only (imports Query.Eval — the cone rule; no mathlib, no
Batteries).
-/

import Query.Eval

namespace Query

open SchemaCore ZSet

variable {fs : List Field}

/-! ## The render indent (the derivation tree's face) -/

/-- Two spaces per depth. -/
def Explain.indent : Nat → String
  | 0 => ""
  | n + 1 => "  " ++ Explain.indent n

/-! ## Why present — the derivation tree as data -/

/-- THE WHY-PRESENT DERIVATION: the answer's supporting derivation as
    DATA (02 §11: which facts/rules produced the answer), riding the
    query's structure — one constructor per `QSat` face. The bridges:
    `Derivation.qsat` (soundness) and `QSat.derivation_nonempty`
    (completeness — every present answer has one). -/
inductive Derivation (fs : List Field) (rows : List (RowVals fs)) :
    {gs : List Field} → Q fs gs → RowVals gs → Type where
  /-- A fact: the row is a base-table row. -/
  | table : (r : RowVals fs) → r ∈ rows → Derivation fs rows .table r
  /-- A rule: the filter accepts a sub-answer. -/
  | select : {gs : List Field} → {p : Pred gs} → {q : Q fs gs} → {r : RowVals gs} →
      Derivation fs rows q r → p.check r = true → Derivation fs rows (.select p q) r
  /-- A rule: the projection picks a sub-answer's preimage. -/
  | project : {gs : List Field} → {c : Cols gs} → {q : Q fs gs}
      → {r' : RowVals gs} → {r : RowVals (c.fields gs)} →
      Derivation fs rows q r' → c.pick gs r' = r → Derivation fs rows (.project c q) r
  /-- A rule: the union's left disjunct. -/
  | unionL : {gs : List Field} → {q1 q2 : Q fs gs} → {r : RowVals gs} →
      Derivation fs rows q1 r → Derivation fs rows (.union q1 q2) r
  /-- A rule: the union's right disjunct. -/
  | unionR : {gs : List Field} → {q1 q2 : Q fs gs} → {r : RowVals gs} →
      Derivation fs rows q2 r → Derivation fs rows (.union q1 q2) r
  /-- A rule: the join pairs two sub-answers on the ON columns; the
      result row IS the append (the index carries it — the same shape
      the evaluation's join case compiles under). -/
  | join : {ga gb : List Field} → {ln rn : String} → {q1 : Q fs ga} → {q2 : Q fs gb}
      → {la : RowVals ga} → {rb : RowVals gb} →
      Derivation fs rows q1 la → Derivation fs rows q2 rb →
      onEq ga gb ln rn la rb = true →
      Derivation fs rows (.join ln rn q1 q2) (Row.append la rb)

/-- THE BRIDGE, soundness face (pattern #1): a derivation implies the
    spec — the derivation never fabricates an answer. -/
theorem Derivation.qsat {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (d : Derivation fs rows q r) : QSat fs rows q r := by
  induction d with
  | table r hm => exact QSat.table r hm
  | select _ hc ih => exact QSat.select ih hc
  | project _ hp ih => exact QSat.project ih hp
  | unionL _ ih => exact QSat.unionL ih
  | unionR _ ih => exact QSat.unionR ih
  | join _ _ hon ih1 ih2 => exact QSat.join ih1 ih2 hon rfl

/-- THE BRIDGE, completeness face: every present answer HAS a
    derivation — the derivation tree is never missing, only
    unrendered. (`Nonempty` is a Prop, so the elimination of the
    Prop-level `QSat` into it is honest; the derivation is data.) -/
theorem QSat.derivation_nonempty {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (h : QSat fs rows q r) : Nonempty (Derivation fs rows q r) := by
  induction h with
  | table r hm => exact ⟨.table r hm⟩
  | select _ hc ih => obtain ⟨d⟩ := ih; exact ⟨.select d hc⟩
  | project _ hp ih => obtain ⟨d⟩ := ih; exact ⟨.project d hp⟩
  | unionL _ ih => obtain ⟨d⟩ := ih; exact ⟨.unionL d⟩
  | unionR _ ih => obtain ⟨d⟩ := ih; exact ⟨.unionR d⟩
  | @join ga gb ln rn q1 q2 la rb r d1 d2 hon happ ih1 ih2 =>
      obtain ⟨e1⟩ := ih1
      obtain ⟨e2⟩ := ih2
      rw [← happ]
      exact ⟨.join (ga := ga) (gb := gb) (ln := ln) (rn := rn) e1 e2 hon⟩

/-- The derivation's rendering: the fact/rule lines, innermost first,
    indented by depth (which facts/rules produced the answer). -/
def Derivation.render {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (d : Derivation fs rows q r) : Nat → String :=
  match d with
  | .table rr _ =>
      fun _n => Explain.indent _n ++
        s!"fact: the base row [{Pred.renderRow fs rr}]"
  | @Derivation.select _ _ _ p _ _ sub _ =>
      fun n => Derivation.render sub (n + 1) ++ "\n" ++ Explain.indent n ++
        s!"rule: the filter `{p.render}` accepts it"
  | @Derivation.project _ _ _ c _ _ _ sub _ =>
      fun n => Derivation.render sub (n + 1) ++ "\n" ++ Explain.indent n ++
        "rule: the projection picks it from the preimage row above"
  | .unionL sub =>
      fun n => Derivation.render sub (n + 1) ++ "\n" ++ Explain.indent n ++
        "rule: the union's left disjunct"
  | .unionR sub =>
      fun n => Derivation.render sub (n + 1) ++ "\n" ++ Explain.indent n ++
        "rule: the union's right disjunct"
  | @Derivation.join _ _ _ _ ln _ _ _ _ _ sub1 sub2 _ =>
      fun n => Derivation.render sub1 (n + 1) ++ "\n" ++
        Derivation.render sub2 (n + 1) ++ "\n" ++ Explain.indent n ++
        s!"rule: the join pairs the two rows above on `{ln}`"

/-- The why-present answer's top line + the derivation. -/
def Derivation.renderTop {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (d : Derivation fs rows q r) : String :=
  s!"present: [{Pred.renderRow gs r}]\n" ++ d.render 1

/-! ## Why absent — the blocking conditions -/

/-- THE WHY-ABSENT BLOCKER: one blocking condition as data over the
    fragment's structure (02 §11). The faces:

    - `base` — the row is absent from the base table (where the
      completeness assumption bites);
    - `select` — the filter's predicate fails on a row the SUBQUERY
      answered (the honest complete face: the sub-answer rides the
      blocker);
    - `project` — EVERY preimage is blocked (the exhaustive ∀ face —
      a single live preimage would resurrect the answer);
    - `union` — both disjuncts are blocked.

    The general join has NO per-decomposition face: many pairs append
    to one result row, so a per-pair blocker would not prove absence —
    the join's honest per-row face is the key-join's `KeyJoinMiss`. -/
inductive Blocker (fs : List Field) (rows : List (RowVals fs)) :
    {gs : List Field} → Q fs gs → RowVals gs → Type where
  /-- The base-table miss (the completeness assumption bites here). -/
  | base : {r : RowVals fs} → r ∉ rows → Blocker fs rows .table r
  /-- The filter's failed predicate — the sub-answer is PRESENT. -/
  | select : {gs : List Field} → {p : Pred gs} → {q : Q fs gs} → {r : RowVals gs} →
      QSat fs rows q r → p.check r = false → Blocker fs rows (.select p q) r
  /-- The projection's exhausted preimages. -/
  | project : {gs : List Field} → {c : Cols gs} → {q : Q fs gs}
      → {r : RowVals (c.fields gs)} →
      (∀ r' : RowVals gs, c.pick gs r' = r → Blocker fs rows q r') →
      Blocker fs rows (.project c q) r
  /-- The union's double absence. -/
  | union : {gs : List Field} → {q1 q2 : Q fs gs} → {r : RowVals gs} →
      Blocker fs rows q1 r → Blocker fs rows q2 r → Blocker fs rows (.union q1 q2) r

/-- THE BLOCKER'S SOUNDNESS: a blocker proves the row's ABSENCE (over
    Bool weights — set semantics, through the evaluation). One
    induction over the fragment, `r` generalized. -/
theorem blocker_absent (rows : List (RowVals fs)) :
    ∀ {gs : List Field} {q : Q fs gs} {r : RowVals gs},
      Blocker fs rows q r → weightW (evalQ q (tableW rows true)) r = false := by
  intro gs q r b
  induction b with
  | base hmem =>
      rw [evalQ, tableW_bool_ok]
      exact decide_eq_false_iff_not.mpr hmem
  | @select _ p q r _ hcheck =>
      have hnt : ¬ (p.check r = true) := fun hc => by
        rw [hcheck] at hc; simp at hc
      rw [evalQ, filterW_ok, if_neg hnt]
      rfl
  | @project _ c q r f ih =>
      rw [evalQ]
      cases h : weightW (projectW (c.pick _) (evalQ q (tableW rows true))) r with
      | false => rfl
      | true =>
          obtain ⟨r', hr, hpick⟩ := (projectW_bool_exists _ _ _).mp h
          rw [ih r' hpick] at hr
          exact Bool.noConfusion hr
  | @union _ q1 q2 r b1 b2 ih1 ih2 =>
      rw [evalQ, addW_ok, wkindBool_add, ih1, ih2]
      rfl

/-- The blocker's description (the why-absent answer's condition
    line). The select face names the failed predicate from the query
    the blocker authenticates. -/
def Blocker.describe {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (b : Blocker fs rows q r) : String :=
  match b with
  | .base _ => "the row is absent from the base table"
  | @Blocker.select _ _ _ p _ _ _ _ =>
      s!"the filter's predicate rejects it: {p.render}"
  | .project _ => "every preimage row is blocked (no live preimage projects to it)"
  | .union _ _ => "both disjuncts are absent"

/-! ## The key-join's missing partner (the join's honest absence face) -/

/-- THE KEY-JOIN'S WHY-ABSENT FACES (02 §3's Option-shape discipline,
    at the explanation grade): for the driving right row, either its
    ON-column projection fails, or the key lookup misses — THE JOIN'S
    MISSING PARTNER, named. (Data, not a Prop: the rendering reads
    the face.) -/
inductive KeyJoinMiss (kd : KeyDecl) (ln : String)
    (left : List (RowVals kd.fields)) {gb : List Field}
    (right : List (RowVals gb)) (rb : RowVals gb) : Type where
  /-- The driving row has no `{ln}` column value to join on. -/
  | noProjection : RowVals.project? gb rb ln = none → KeyJoinMiss kd ln left right rb
  /-- The missing partner: no left row carries the joined key. -/
  | keyMiss (k : FieldVal) :
      RowVals.project? gb rb ln = some k → kd.lookup? left k = none →
      KeyJoinMiss kd ln left right rb

/-- THE KEY-JOIN BLOCKER'S SOUNDNESS: a miss proves the pair is absent
    from the key-join's result (the Option shape's honesty, as data). -/
theorem KeyJoinMiss.not_mem {kd : KeyDecl} {ln : String}
    {left : List (RowVals kd.fields)} {gb : List Field}
    {right : List (RowVals gb)} {rb : RowVals gb}
    (h : KeyJoinMiss kd ln left right rb) (la : RowVals kd.fields) :
    (la, rb) ∉ keyJoinRows kd ln left right := by
  intro hmem
  simp only [keyJoinRows, List.mem_filterMap] at hmem
  obtain ⟨x, hx, hf⟩ := hmem
  cases hp : RowVals.project? gb x ln with
  | none =>
      rw [hp] at hf
      exact absurd hf (by simp)
  | some k =>
      rw [hp] at hf
      obtain ⟨y, hly, hpair⟩ := Option.map_eq_some_iff.mp hf
      have hxr : x = rb := by
        have hrb : rb = x := congrArg Prod.snd hpair.symm
        exact hrb.symm
      subst hxr
      cases h with
      | noProjection hpn =>
          rw [hpn] at hp
          simp at hp
      | keyMiss k' hlook hmiss =>
          rw [hlook] at hp
          have hkk : k' = k := Option.some.inj hp
          subst hkk
          rw [hmiss] at hly
          exact absurd hly (by simp)

/-- The key-join miss's description. -/
def KeyJoinMiss.render {kd : KeyDecl} {ln : String}
    {left : List (RowVals kd.fields)} {gb : List Field}
    {right : List (RowVals gb)} {rb : RowVals gb}
    (h : KeyJoinMiss kd ln left right rb) : String :=
  match h with
  | .noProjection _ =>
      s!"the join's driving row [{Pred.renderRow gb rb}] has no `{ln}` \
        column value to join on"
  | .keyMiss _ _ _ =>
      s!"the join's missing partner: no {kd.record} row carries the key \
        joined from [{Pred.renderRow gb rb}] on `{ln}`"

/-! ## The completeness assumption + the why-absent answer -/

/-- THE DECLARED COMPLETENESS ASSUMPTION (02 §8: absence claims need
    knowing the input is complete — the knowledge is a DECLARED
    assumption with a NAMED scope, never a blanket claim). The scope
    is what the answer's honesty is bound to; the rendering carries
    it. -/
structure Completeness (fs : List Field) (rows : List (RowVals fs)) where
  /-- The named scope the completeness is declared over (e.g. "the
      transfer ledger as committed"). -/
  scope : String

/-- THE WHY-ABSENT ANSWER: the blocking condition RIDING the declared
    completeness assumption. THE HONESTY TOOTH: without a declared
    `Completeness`, the `.blocked` constructor is unbuildable and the
    only honest answer is `.refusal` — a refusal, never a guess. -/
inductive WhyAbsent (fs : List Field) (rows : List (RowVals fs)) :
    {gs : List Field} → Q fs gs → RowVals gs → Type where
  /-- No completeness assumption declared — no absence claim is made. -/
  | refusal : WhyAbsent fs rows q r
  /-- The blocking condition, under the declared completeness. -/
  | blocked : Completeness fs rows → Blocker fs rows q r → WhyAbsent fs rows q r

/-- The why-absent answer's VERDICT (what the answer actually claims):
    a blocked answer claims the row's absence — PROVED
    (`WhyAbsent.verdict_sound`); a refusal claims NOTHING. -/
def WhyAbsent.verdict {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (h : WhyAbsent fs rows q r) : Prop :=
  match h with
  | .refusal => True
  | .blocked _ _b => weightW (evalQ q (tableW rows true)) r = false

/-- THE WHY-ABSENT SOUNDNESS: a blocked answer's absence claim is
    PROVED (the blocker's soundness, under the carried completeness);
    a refusal's vacuous claim is trivial. -/
theorem WhyAbsent.verdict_sound {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (h : WhyAbsent fs rows q r) : h.verdict := by
  match h with
  | .refusal => exact trivial
  | .blocked _ b => exact blocker_absent rows b

/-- The why-absent answer's rendering: the blocking condition + the
    NAMED completeness assumption — or the refusal, loudly. -/
def WhyAbsent.render {fs : List Field} {rows : List (RowVals fs)}
    {gs : List Field} {q : Q fs gs} {r : RowVals gs}
    (h : WhyAbsent fs rows q r) : String :=
  match h with
  | .refusal =>
      "why absent: REFUSED — no completeness assumption is declared, so an\n" ++
      "  absence claim would be a guess; declare the assumption and re-ask."
  | .blocked c b =>
      "why absent: the row is not in the result\n" ++
      s!"  blocking condition: {b.describe}\n" ++
      s!"  under the declared completeness assumption: {c.scope}\n" ++
      "  (the absence claim is about the declared scope ONLY)"

end Query

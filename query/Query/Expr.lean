/-
# Query.Expr — the typed query fragment + the FD-driven result typing

Owned by: the Query agent (the mandate tree, `query/`).

notes/v3/02-data-plane.md §2 (the relational fragment: selection /
projection / equijoin / union — the same expression as executable
query and logical proposition) + §3 (functional dependencies are
determinacy theorems: the result TYPE follows the PROVED determinacy —
an ordinary query is collection-shaped, a key-backed query is
Option-shaped, and the inference is conservative: unproven uniqueness
yields collections, never invented uniqueness).

What lands here:

- `Cols` — the projection's column DATA: positions in the source
  schema, in result order. The result row type `c.fields fs` is
  COMPUTED from the column data — the projection's shape is in the
  type, by construction (total: the reader `Row.field` is total).
- `Q fs gs` — the typed fragment: `table` / `select` (a `SchemaCore.Pred`
  over the row — the schema's OWN predicate fragment, consumed
  read-only) / `project` (the column subsets) / `union` (disjunction:
  over Bool weights the add is OR — set semantics; over bags/deltas it
  counts) / `join` (conjunction: the equijoin on named columns; the
  result row is the left schema ++ the right schema — computed).
- `onEq` — the equijoin's ON semantics as data: both projections
  resolve and the values are equal (`FieldVal.beq`, lawfully equality).
  A missing or mistyped column does not match — the refusal reading,
  never a fabricated comparison.
- `QSat` — THE SPEC OF RECORD (pattern #1's Prop side): the honest
  relational reading — table membership, selection restricts,
  projection is EXISTENTIAL (some preimage row projects to the result
  row), union is disjunctive, join is conjunctive with an appended
  result row. This is 02 §2's table, stated as an inductive family;
  the executable evaluation is `Query.Eval.evalQ`, and the bridge is
  `evalQ_true_iff` (over Bool weights — set semantics).
- `keyJoinRows` + `keyJoinRows_atMostOne` — THE KEY-BACKED JOIN (02
  §3's payoff): the right row drives; the left match is looked up
  THROUGH the declared key (`KeyDecl.lookup?` — the Option shape);
  for a fixed right row the left component is determined — the
  `KeyDecl.uniqueOn_determines` theorem consumed, not re-proved.

The honest boundary (02 §2): negation, aggregation, universal
conditions, and ordering are NOT operators here — each needs explicit
additional semantics with named laws. The general join's result typing
is collection-shaped BY DEFAULT: uniqueness attaches only through a
declared key's CHECKED `uniqueOn` (the conservative inference).

The five questions (notes/v3/01-core.md):
- **Root**: the data plane's query fragment over the schema's rows.
- **Carrier grade**: the typed fragment — a mistyped column reference
  is a refusal at run time (the Pred discipline), and the result row
  type is computed, never declared separately.
- **Spine reading**: none — the fragment the data-plane lanes consume.
- **Ladder rung**: `keyJoinRows_atMostOne` cites the Keys lane's
  determinacy theorems (never a second proof); `QSat` is the spec.
- **Gate rows**: the axiom report + QueryTests' pins (the spec built
  both ways + the determinacy typing + the negative controls).

Core-only (imports Query.Basic + SchemaCore.Pred + SchemaCore.Keys —
the cone rule).
-/

import Query.Basic
import SchemaCore.Pred
import SchemaCore.Keys

namespace Query

open SchemaCore

/-! ## The projection's column data -/

/-- The projection's columns: positions in the source schema, in
    result order — the RESULT row type is computed from it
    (`Cols.fields`). Duplicates are allowed (the bag reading keeps the
    count; the set reading collapses). -/
inductive Cols : List Field → Type where
  | nil : Cols fs
  | cons : {fs : List Field} → (i : Fin fs.length) → Cols fs → Cols fs

/-- The projected schema: the selected source fields, in column order. -/
def Cols.fields (fs : List Field) : Cols fs → List Field
  | .nil => []
  | .cons i c => fs[i.val] :: c.fields fs

/-- The projection's reader: a source row becomes the result row over
    the computed schema — total (the positions are in range by
    construction), no projection failure path at all. -/
def Cols.pick (fs : List Field) (c : Cols fs) (row : RowVals fs) :
    RowVals (c.fields fs) :=
  match c with
  | .nil => .nil
  | .cons i c => .cons (Row.field fs row i) (c.pick fs row)

/-! ## The typed fragment -/

/-- THE TYPED QUERY FRAGMENT (02 §2's honest minimal fragment): `fs`
    is the base table's schema; the second index is the result schema —
    COMPUTED from the query structure (projection's column data, the
    join's schema concatenation). No negation, no aggregation, no
    universal conditions, no ordering — 02 §2's named limits stay out
    of the grammar. -/
inductive Q (fs : List Field) : List Field → Type where
  /-- The base table itself. -/
  | table : Q fs fs
  /-- Selection: keep the rows satisfying the schema's predicate
      (weights unchanged). -/
  | select : {gs : List Field} → Pred gs → Q fs gs → Q fs gs
  /-- Projection: the column subsets — the result schema is the
      column data's computed field list. -/
  | project : {gs : List Field} → (c : Cols gs) → Q fs gs → Q fs (c.fields gs)
  /-- Disjunction: union. Over Bool weights the add is OR — set
      semantics; over bags/deltas it counts (the weight polymorphism
      is the semantics, never a flag). -/
  | union : {gs : List Field} → Q fs gs → Q fs gs → Q fs gs
  /-- Conjunction: the equijoin on named columns (left field `ln`, right
      field `rn`); the result row is the appended schema's row. -/
  | join : {ga gb : List Field} → (ln rn : String) → Q fs ga → Q fs gb →
      Q fs (ga ++ gb)

/-- The equijoin's ON semantics: both projections resolve and the
    values are equal. A missing or mistyped column does not match (the
    refusal reading — never a fabricated comparison). -/
def onEq (ga gb : List Field) (ln rn : String) (la : RowVals ga) (rb : RowVals gb) :
    Bool :=
  match RowVals.project? ga la ln, RowVals.project? gb rb rn with
  | some x, some y => x.beq y
  | _, _ => false

/-! ## The spec of record (the Prop-level relational reading) -/

/-- THE SPEC (pattern #1's Prop side, stated BEFORE the checker's
    twin): the honest relational semantics of the fragment. Projection
    is EXISTENTIAL (the result row has some preimage the subquery
    satisfies — 02 §2's quantifier reading); join is conjunctive with
    the appended row. The executable evaluation's bridge is
    `Query.Eval.evalQ_true_iff` — over Bool weights (set semantics),
    BOTH directions proved. -/
inductive QSat (fs : List Field) (rows : List (RowVals fs)) :
    {gs : List Field} → Q fs gs → RowVals gs → Prop where
  /-- The base table: membership. -/
  | table : ∀ (r : RowVals fs), r ∈ rows → QSat fs rows .table r
  /-- Selection restricts. -/
  | select : ∀ {gs : List Field} {p : Pred gs} {q : Q fs gs} {r : RowVals gs},
      QSat fs rows q r → p.check r = true → QSat fs rows (.select p q) r
  /-- Projection: existential over the preimage. -/
  | project : ∀ {gs : List Field} {c : Cols gs} {q : Q fs gs}
      {r' : RowVals gs} {r : RowVals (c.fields gs)},
      QSat fs rows q r' → c.pick gs r' = r → QSat fs rows (.project c q) r
  /-- Union, left disjunct. -/
  | unionL : ∀ {gs : List Field} {q1 q2 : Q fs gs} {r : RowVals gs},
      QSat fs rows q1 r → QSat fs rows (.union q1 q2) r
  /-- Union, right disjunct. -/
  | unionR : ∀ {gs : List Field} {q1 q2 : Q fs gs} {r : RowVals gs},
      QSat fs rows q2 r → QSat fs rows (.union q1 q2) r
  /-- Join: the conjunctive reading, the row appended. -/
  | join : ∀ {ga gb : List Field} {ln rn : String} {q1 : Q fs ga} {q2 : Q fs gb}
      {la : RowVals ga} {rb : RowVals gb} {r : RowVals (ga ++ gb)},
      QSat fs rows q1 la → QSat fs rows q2 rb → onEq ga gb ln rn la rb = true →
      Row.append la rb = r → QSat fs rows (.join ln rn q1 q2) r

/-! ## The key-backed join (02 §3's payoff) -/

/-- THE KEY-BACKED JOIN: the right row drives; the left match is looked
    up THROUGH the declared key — the per-right-row result is the
    Option shape (`KeyDecl.lookup?`), at most one left row per right
    row. A right row whose `ln` projection fails contributes nothing
    (the refusal reading). This is the Keys lane's discipline consumed,
    not a parallel lookup table. -/
def keyJoinRows (kd : KeyDecl) (ln : String)
    (left : List (RowVals kd.fields)) (right : List (RowVals gb)) :
    List (RowVals kd.fields × RowVals gb) :=
  right.filterMap fun rb =>
    match RowVals.project? gb rb ln with
    | none => none
    | some k => (kd.lookup? left k).map fun la => (la, rb)

/-- THE DETERMINACY TYPING (02 §3): under the left table's CHECKED
    `uniqueOn`, a fixed right row's joined left row is determined —
    any two results with the same right component have the SAME left
    component. The theorem is `KeyDecl.lookup?_atMostOne`'s content
    through the join; the Option shape above is its type-level face. -/
theorem keyJoinRows_atMostOne (kd : KeyDecl) (ln : String)
    (left : List (RowVals kd.fields)) (right : List (RowVals gb))
    (huniq : kd.uniqueOn left = true) (rb : RowVals gb)
    {la1 la2 : RowVals kd.fields}
    (h1 : (la1, rb) ∈ keyJoinRows kd ln left right)
    (h2 : (la2, rb) ∈ keyJoinRows kd ln left right) :
    la1 = la2 := by
  have key : ∀ {la : RowVals kd.fields},
      (la, rb) ∈ keyJoinRows kd ln left right →
      ∃ k : FieldVal, RowVals.project? gb rb ln = some k ∧ kd.lookup? left k = some la := by
    intro la hmem
    obtain ⟨rb', hrb', hs⟩ := List.mem_filterMap.mp hmem
    cases hproj : RowVals.project? gb rb' ln with
    | none => simp only [hproj] at hs; simp at hs
    | some k =>
        simp only [hproj] at hs
        obtain ⟨x, hlk, hxe⟩ := Option.map_eq_some_iff.mp hs
        injection hxe with hx1 hx2
        subst hx1
        subst hx2
        exact ⟨k, hproj, hlk⟩
  obtain ⟨k1, hk1, hl1⟩ := key h1
  obtain ⟨k2, hk2, hl2⟩ := key h2
  rw [hk1] at hk2
  have hkk : k1 = k2 := Option.some.inj hk2
  rw [← hkk] at hl2
  exact kd.lookup?_atMostOne left huniq k1 hl1 hl2

end Query

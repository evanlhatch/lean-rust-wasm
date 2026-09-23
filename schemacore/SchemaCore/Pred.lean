/-
# SchemaCore.Pred — the check lane's predicate fragment (the seed of the
relational predicate core)

Owner: the SchemaCore agent (the macht tree, `schemacore/`).
Driving decisions: notes/v3/02-data-plane.md §1-2 (the schema describes
valid worlds; a row predicate is a constraint over one row; a failed
check carries the VIOLATING ROWS); notes/v3/15-patterns.md #1 (the
relation-as-spec + executable checker + proved bridge — THE pattern);
notes/v3/04-verification.md §1 (the ladder: the bridge is the small
hand kind, written once, cited by every lane after).

The fragment (the honest minimal set a first lane consumes — a CLOSED
inductive over a row's fields):

- `lit` — a constant verdict;
- `u64EqLit n v` / `u64GtLit n v` — the u64 column `n` equals / exceeds
  the literal (the legacy VExpr's `eq`/`gt` scalars);
- `u64Eq a b` — two u64 columns equal (the legacy `eq` arm's
  field-to-field shape);
- `strEqLit n s` — the string column `n` equals the literal;
- `and` / `or` / `not` — the boolean combinations (the legacy `and` +
  `not`; `or` rides the same evaluator shape).

DELIBERATELY EXCLUDED from the legacy VExpr's surface (each names its
reason — the leftover rule: nothing lands without a consumer):

- `i64` comparisons/arithmetic — the legacy scalar lane is u64-only
  (`gt`/`eq` on `VExpr s .u64`); extend when the first i64 invariant
  lands;
- `strlen` — the legacy compiled-lane primitive (the `string_len`
  intrinsic); Pred has NO emitter (the check lane is check-only at
  slice size; emission is a later order's consumer);
- implication — expressible as `¬p ∨ q` in the combinations above;
- quantifiers/aggregation — the TABLE-level lane's business (the
  legacy `TableInvariant` sibling): a row-local check cannot see the
  row-set, the two tiers stay separate;
- named references/open terms — `Pred` ranges over `RowVals fs` (the
  closed carrier); no `.ty` refs in the slice's universe.

The three faces (pattern #1): `Pred.Sat` — the spec of record (the
honest semantics, defined BEFORE the checker; the spec never lies to
fit the checker); `Pred.check` — the decidable procedure; the bridge
(`check_iff`, with `check_sound`/`check_complete` as the projections) —
BOTH directions proved, so the `CheckedProp` completeness choice is
`.proved` (the loud two-constructor choice honored with the proof,
never defaulted).

A missing or mistyped column makes the atomic claim FALSE — the row
does not satisfy the predicate (a refusal, never a fabricated
comparison; the legacy `columnU64?` discipline). The violating-rows
discipline (02 §1): `Pred.violations` returns the failing rows AS DATA.

The five questions (notes/v3/01-core.md): root = the check lane's
predicate layer (data); carrier = the GADT-indexed fragment over the
closed `Ty` (a mistyped comparison unconstructible in the fragment);
spine reading = a value fold (project + compare); ladder rung = the
bridge is the small hand kind, both directions; gate row = SchemaTests'
predSpec pins + the axiom report.

Core-only (imports SchemaCore.RowVals only — the cone rule).
-/

import SchemaCore.RowVals

namespace SchemaCore

/-! ## The projected-column readings -/

/-- The u64 reading of a projected field: `some x` when the column is
    a u64 carrying `x`; `none` when the column is missing or mistyped
    (a refusal, never a zero — the legacy `columnU64?` discipline). -/
def FieldVal.u64? : FieldVal → Option UInt64
  | ⟨.u64, .u64 v⟩ => some v
  | _ => none

/-- The string reading of a projected field. -/
def FieldVal.str? : FieldVal → Option String
  | ⟨.string, .string s⟩ => some s
  | _ => none

/-! ## The comparison helper -/

/-- The u64 strict comparison as DATA (a plain Bool-valued helper —
    the `>` notation's Prop/Bool ambiguity double-coerces under the
    expected-Prop positions of `Sat`'s arms; the helper pins ONE
    reading). -/
def u64gt (a b : UInt64) : Bool := b < a

/-! ## The fragment -/

/-- The predicate fragment over a schema-aligned row: `fs` is the
    field list (a plain parameter — the fragment does not branch on
    it; the ROW is what carries the well-formedness). -/
inductive Pred (fs : List Field) : Type where
  /-- A constant verdict. -/
  | lit : Bool → Pred fs
  /-- The u64 column `n` equals the literal. -/
  | u64EqLit : String → UInt64 → Pred fs
  /-- The u64 column `n` exceeds the literal. -/
  | u64GtLit : String → UInt64 → Pred fs
  /-- Two u64 columns equal. -/
  | u64Eq : String → String → Pred fs
  /-- The string column `n` equals the literal. -/
  | strEqLit : String → String → Pred fs
  /-- Conjunction. -/
  | and : Pred fs → Pred fs → Pred fs
  /-- Disjunction. -/
  | or : Pred fs → Pred fs → Pred fs
  /-- Negation (the ≤-shaped invariants: `not (u64GtLit n v)` =
      `n ≤ v` — the legacy `not` arm's reading). -/
  | not : Pred fs → Pred fs

/-- THE CHECKER — the decidable procedure. A projection failure
    refuses (`false`): a missing or mistyped column is not a satisfied
    comparison. -/
def Pred.check {fs : List Field} : Pred fs → RowVals fs → Bool
  | .lit b, _ => b
  | .u64EqLit n v, row =>
      match (RowVals.project? fs row n).bind FieldVal.u64? with
      | some x => x == v
      | none => false
  | .u64GtLit n v, row =>
      match (RowVals.project? fs row n).bind FieldVal.u64? with
      | some x => u64gt x v
      | none => false
  | .u64Eq a b, row =>
      match (RowVals.project? fs row a).bind FieldVal.u64?,
            (RowVals.project? fs row b).bind FieldVal.u64? with
      | some x, some y => x == y
      | _, _ => false
  | .strEqLit n s, row =>
      match (RowVals.project? fs row n).bind FieldVal.str? with
      | some t => t == s
      | none => false
  | .and p q, row => p.check row && q.check row
  | .or p q, row => p.check row || q.check row
  | .not p, row => !(p.check row)

/-! ## The semantics (the spec of record) -/

/-- THE SEMANTICS: a predicate's meaning over a row — the honest
    relation, defined before and independently of the checker (the
    spec never lies to fit the checker, 15-patterns #1). An atomic
    claim quantifies the column's reading; a missing/mistyped column
    fails the claim (no reading = no satisfaction). -/
def Pred.Sat {fs : List Field} : Pred fs → RowVals fs → Prop
  | .lit b, _ => b = true
  | .u64EqLit n v, row =>
      ∃ x, (RowVals.project? fs row n).bind FieldVal.u64? = some x ∧ x = v
  | .u64GtLit n v, row =>
      ∃ x, (RowVals.project? fs row n).bind FieldVal.u64? = some x
        ∧ (u64gt x v) = true
  | .u64Eq a b, row =>
      ∃ x y, (RowVals.project? fs row a).bind FieldVal.u64? = some x
        ∧ (RowVals.project? fs row b).bind FieldVal.u64? = some y ∧ x = y
  | .strEqLit n s, row =>
      ∃ t, (RowVals.project? fs row n).bind FieldVal.str? = some t ∧ t = s
  | .and p q, row => p.Sat row ∧ q.Sat row
  | .or p q, row => p.Sat row ∨ q.Sat row
  | .not p, row => ¬ p.Sat row

/-! ## THE BRIDGE (pattern #1) — checker → relation, both directions -/

/- The bridge is ONE induction over the fragment carrying BOTH
    directions (`not`'s soundness needs the operand's completeness and
    vice versa — a single iff-shaped induction is the honest shape;
    proved once, cited by every lane after, 01 §6). -/
theorem Pred.check_iff {fs : List Field} :
    ∀ (p : Pred fs) (row : RowVals fs), p.check row = true ↔ p.Sat row := by
  intro p
  induction p with
  | lit b => intro row; exact ⟨fun h => h, fun h => h⟩
  | u64EqLit n v =>
      intro row
      simp only [check, Sat]
      cases hb : (RowVals.project? fs row n).bind FieldVal.u64? with
      | none => simp
      | some x =>
          refine ⟨fun h => ⟨x, rfl, beq_iff_eq.mp h⟩, fun h => ?_⟩
          obtain ⟨x', hx, hxv⟩ := h
          have hinj : x = x' := Option.some.inj hx
          rw [hinj]
          exact beq_iff_eq.mpr hxv
  | u64GtLit n v =>
      intro row
      simp only [check, Sat]
      cases hb : (RowVals.project? fs row n).bind FieldVal.u64? with
      | none => simp
      | some x =>
          refine ⟨fun h => ⟨x, rfl, h⟩, fun h => ?_⟩
          obtain ⟨x', hx, hxv⟩ := h
          have hinj : x = x' := Option.some.inj hx
          rw [hinj]
          exact hxv
  | u64Eq a b =>
      intro row
      simp only [check, Sat]
      cases hbx : (RowVals.project? fs row a).bind FieldVal.u64? with
      | none => simp
      | some x =>
          cases hby : (RowVals.project? fs row b).bind FieldVal.u64? with
          | none => simp
          | some y =>
              refine ⟨fun h => ⟨x, y, rfl, rfl, beq_iff_eq.mp h⟩, fun h => ?_⟩
              obtain ⟨x', y', hx, hy, hxy⟩ := h
              have hx' : x = x' := Option.some.inj hx
              have hy' : y = y' := Option.some.inj hy
              rw [hx', hy']
              exact beq_iff_eq.mpr hxy
  | strEqLit n s =>
      intro row
      simp only [check, Sat]
      cases hb : (RowVals.project? fs row n).bind FieldVal.str? with
      | none => simp
      | some t =>
          refine ⟨fun h => ⟨t, rfl, beq_iff_eq.mp h⟩, fun h => ?_⟩
          obtain ⟨t', ht, hts⟩ := h
          have hinj : t = t' := Option.some.inj ht
          rw [hinj]
          exact beq_iff_eq.mpr hts
  | and p q ihp ihq =>
      intro row
      simp only [check, Sat, Bool.and_eq_true, ihp row, ihq row]
  | or p q ihp ihq =>
      intro row
      simp only [check, Sat, Bool.or_eq_true, ihp row, ihq row]
  | not p ihp =>
      intro row
      simp only [check, Sat]
      constructor
      · intro h hs
        rw [(ihp row).mpr hs] at h
        simp at h
      · intro hs
        cases hc : p.check row with
        | false => simp
        | true => exact absurd ((ihp row).mp hc) hs

/-- SOUNDNESS: a `true` verdict is a proof of `Sat` — the checker
    never fabricates a satisfaction. -/
theorem Pred.check_sound {fs : List Field} (p : Pred fs) (row : RowVals fs)
    (h : p.check row = true) : p.Sat row :=
  (p.check_iff row).mp h

/-- COMPLETENESS: every satisfying row's verdict is `true` — the
    fragment is decidable both ways, so the `CheckedProp` below takes
    `.proved` (no `.missing` default is available or used). -/
theorem Pred.check_complete {fs : List Field} (p : Pred fs) (row : RowVals fs)
    (h : p.Sat row) : p.check row = true :=
  (p.check_iff row).mpr h

/-! ## The CheckedProp assembly (the statement-as-instance) -/

/-- Pattern #1's assembly: the predicate's check lane as a
    `Kit.CheckedProp` over the row carrier — soundness mandatory, and
    the completeness constructor is `.proved` (the bridge above). The
    lanes consume this, never a re-proof. -/
def Pred.checked {fs : List Field} (p : Pred fs) : Kit.CheckedProp (RowVals fs) :=
  { P := fun row => p.Sat row
    check := fun row => p.check row
    sound := p.check_sound
    complete? := .proved p.check_complete }

/-! ## The violating-rows discipline (02 §1) -/

/-- THE VIOLATING ROWS: a failed table check carries the failing rows
    AS DATA — every row whose verdict is `false`, in table order (the
    diagnostic's payload, never a bare `false`). -/
def Pred.violations {fs : List Field} (p : Pred fs)
    (rows : List (RowVals fs)) : List (RowVals fs) :=
  rows.filter (fun r => !p.check r)

/-! ## The rendering (diagnostics + test pins; NOT byte-tied) -/

/-- The predicate's rendering. -/
def Pred.render {fs : List Field} : Pred fs → String
  | .lit b => s!"{b}"
  | .u64EqLit n v => s!"{n} = {v}"
  | .u64GtLit n v => s!"{n} > {v}"
  | .u64Eq a b => s!"{a} = {b}"
  | .strEqLit n s => s!"{n} = \"{s}\""
  | .and p q => s!"({p.render} ∧ {q.render})"
  | .or p q => s!"({p.render} ∨ {q.render})"
  | .not p => s!"¬{p.render}"

/-- A row's rendering as `name=value; …` — the violating-rows
    diagnostics carrier (the diagnostic shows the row's DATA, 02 §11). -/
def Pred.renderRow : (fs : List Field) → RowVals fs → String
  | [], .nil => ""
  | f :: fs, .cons v vs =>
      let cur := s!"{f.name}={Value.render f.ty v}"
      let rest := Pred.renderRow fs vs
      if rest.isEmpty then cur else s!"{cur}; {rest}"

/-! ## The coverage pins (the fragment reduces — kernel-visible) -/

/-- The Example-shaped two-field row fixture, local to the pins. -/
private def pinFields : List Field :=
  [ { name := "ready", ty := .bool }, { name := "count", ty := .u64 } ]

example : Pred.check (fs := pinFields) (.u64EqLit "count" 0)
    (.cons (.bool true) (.cons (.u64 0) .nil)) = true := rfl
example : Pred.check (fs := pinFields) (.u64GtLit "count" 0)
    (.cons (.bool true) (.cons (.u64 0) .nil)) = false := rfl
example : Pred.check (fs := pinFields) (.u64Eq "count" "count")
    (.cons (.bool true) (.cons (.u64 3) .nil)) = true := rfl
example : Pred.check (fs := pinFields)
    (.and (.lit true) (.not (.u64GtLit "count" 3)))
    (.cons (.bool true) (.cons (.u64 3) .nil)) = true := rfl
-- the refusal discipline: a missing column refuses, never fabricates
example : Pred.check (fs := pinFields) (.u64EqLit "nope" 0)
    (.cons (.bool true) (.cons (.u64 3) .nil)) = false := rfl
-- the mistyped column refuses, never fabricates
example : Pred.check (fs := pinFields) (.u64EqLit "ready" 0)
    (.cons (.bool true) (.cons (.u64 3) .nil)) = false := rfl
-- the violating rows come back as data
example : Pred.violations (fs := pinFields) (.u64GtLit "count" 0)
    [ .cons (.bool true) (.cons (.u64 0) .nil)
    , .cons (.bool false) (.cons (.u64 2) .nil) ]
  = [.cons (.bool true) (.cons (.u64 0) .nil)] := rfl

end SchemaCore

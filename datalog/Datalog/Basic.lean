/-
# Datalog.Basic — the typed fragment: syntax, safety, the grounding engine

Owned by: the datalog agent (the mandate tree, `datalog/`).
Driving decisions: notes/v3/02-data-plane.md §9 (Datalog as the
EXECUTABLE fragment: typed predicates, safe/range-restricted rules; the
trap — finite keys alone don't terminate recursive bag weights, so the
fragment is deliberately Boolean-fact-only) + notes/v3/01-core.md §6
(the relational engine: per-primitive preservation + ONE generic
correctness theorem) + notes/v3/15-patterns.md #1 (relation-as-spec +
executable checker + proved bridge) and #16 (the closed-world error
discipline — a refusal names the offending variable, never a bare "no").

## The fragment's exact shape (and the honest exclusions)

- Values: an arbitrary `Value : Type` with `DecidableEq` and
  `Inhabited` (inhabitance is used only to totalize the spec-level
  grounding; the finite fact universe is carved out of the EDB values +
  program constants at Semantics.lean — the type itself need not be
  finite).
- Facts: GROUND atoms only (a predicate symbol + a value tuple).
- Rules: head + body of literals over `Term Value` (constants or
  string-named variables). The SAFETY discipline is a CHECKED property
  (`Rule.safe` + `Rule.check` + `Program.checked` — the loud refusal
  renders the offending variable): every head/body variable must occur
  in a positive body literal (range-restrictedness).
- **Named exclusion — negation**: a NEGATED body literal fails the
  safety check outright (`SafetyError.negation` — the named refusal).
  Stratified negation is a separate extension with its own laws (02 §9:
  it is deliberate, not an oversight): this fragment's consequence
  operator is MONOTONE, which negation destroys.
- **Named exclusions** (each lands with its named law, 02 §9): no
  aggregation, no arithmetic generation, no recursive bag weights
  (finite keys alone don't terminate those), no external effects.

The five questions (notes/v3/01-core.md):
- **Root**: Universe (data) — the relational-closure side of the data
  plane; the evaluation semantics lives in `Datalog.Semantics`.
- **Carrier grade**: pattern #1 — the executable grounding engine
  (`matchArgs`/`matchAll`) here; the Prop-level spec reading and the
  bridge theorems live in `Datalog.Semantics`.
- **Spine reading**: none — Datalog is a substrate; lanes instantiate
  programs over their own value universes.
- **Ladder rung**: the safety checker is rung 3 (`Bool` check + the
  error datum); the bridge lemmas are rung 6 hand theorems at the
  structure.
- **Gate rows**: the axiom report pins in DatalogTests.Axioms.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Kit.Change

/-! ## Predicates, ground atoms, terms, literals, rules -/

namespace Datalog

/-- A predicate symbol: a name + a fixed arity. -/
structure Pred where
  name : String
  arity : Nat
deriving DecidableEq, Repr, Inhabited

/-- A GROUND atom: predicate symbol + value tuple. Facts are ground
    atoms — the fragment has no function symbols, so grounding
    terminates by construction. -/
structure Atom (Value : Type) where
  pred : Pred
  args : List Value
deriving Repr, Inhabited

/-- A term: a constant of the value universe or a string-named
    variable. -/
inductive Term (Value : Type) where
  | cst : Value → Term Value
  | var : String → Term Value
deriving DecidableEq, Repr, Inhabited

/-- A body literal: a positive or negated occurrence of a predicate.
    NOTE: the fragment's safety check REFUSES negated literals (the
    named exclusion in the header) — the flag exists so the refusal is
    a check result, not an unrepresentable syntax. -/
structure Lit (Value : Type) where
  positive : Bool
  pred : Pred
  args : List (Term Value)
deriving DecidableEq, Repr, Inhabited

/-- A rule: head predicate + head terms + body literals. -/
structure Rule (Value : Type) where
  headPred : Pred
  headArgs : List (Term Value)
  body : List (Lit Value)
deriving DecidableEq, Repr, Inhabited

/-- A program: a rule list (order is immaterial to the semantics; the
    list is the representation). -/
abbrev Program (Value : Type) := List (Rule Value)

/-! ## Atom equality (hand-rolled: structure fields decide) -/

theorem atom_ext_iff {Value : Type} (a b : Atom Value) :
    a = b ↔ a.pred = b.pred ∧ a.args = b.args :=
  ⟨fun h => ⟨h ▸ rfl, h ▸ rfl⟩, fun h => by
    cases a
    cases b
    cases h.1
    cases h.2
    rfl⟩

instance Atom.instDecidableEq [DecidableEq Value] : DecidableEq (Atom Value) :=
  fun a b => decidable_of_decidable_of_iff (atom_ext_iff a b).symm

/-! ## Variables and constants -/

/-- The variables of a term (a constant names none). -/
def Term.vars : Term Value → List String
  | .cst _ => []
  | .var x => [x]

/-- The constants of a term. -/
def Term.consts : Term Value → List Value
  | .cst v => [v]
  | .var _ => []

/-- The variables occurring in a literal. -/
def Lit.vars (l : Lit Value) : List String := l.args.flatMap Term.vars

/-- The constants occurring in a literal. -/
def Lit.consts (l : Lit Value) : List Value := l.args.flatMap Term.consts

/-- The constants occurring in a rule (head + body) — part of the
    program's finite value universe (Semantics.lean). -/
def Rule.consts (r : Rule Value) : List Value :=
  r.headArgs.flatMap Term.consts ++ r.body.flatMap Lit.consts

/-! ## Safety: range-restrictedness as a CHECKED property -/

/-- The variables BOUND by the rule's positive body literals. -/
def Rule.bound (r : Rule Value) : List String :=
  (r.body.filter (fun l => l.positive = true)).flatMap Lit.vars

/-- The safety discipline, as data:
    (1) every body literal is positive — NEGATION IS OUTSIDE THE
    FRAGMENT (the named refusal `SafetyError.negation`; stratified
    negation is a separate extension with its own laws); and
    (2) range-restrictedness — every head/body variable occurs in a
    positive body literal. (2)'s body half is vacuous once (1) holds —
    the general form is what survives into the stratified extension. -/
def Rule.safe (r : Rule Value) : Bool :=
  r.body.all (fun l => l.positive = true)
    && (r.headArgs.flatMap Term.vars).all (fun x => r.bound.contains x)
    && r.body.all (fun l => l.vars.all (fun x => r.bound.contains x))

/-- WHY a rule was refused — the closed-world error vocabulary
    (15-patterns #16): each constructor names the offending site. -/
inductive SafetyError where
  /-- Body literal #`i` is negated: stratified negation is not in this
      fragment (02-data-plane §9's deliberate exclusion). -/
  | negation (i : Nat)
  /-- Head variable `v` occurs in no positive body literal. -/
  | unboundHead (v : String)
  /-- Body literal #`i` has variable `v` bound by no positive literal. -/
  | unboundBody (i : Nat) (v : String)
deriving DecidableEq, Repr, Inhabited

/-- The refusal rendered (the error is the API's teaching surface). -/
def SafetyError.render : SafetyError → String
  | .negation i =>
      s!"body literal #{i} is NEGATED — negation is outside this fragment " ++
      s!"(the consequence operator must stay monotone; stratified negation " ++
      s!"is a separate extension with its own laws)"
  | .unboundHead v =>
      s!"head variable '{v}' does not occur in any positive body literal " ++
      s!"— the rule is not range-restricted (unsafe: it could derive atoms " ++
      s!"over values no fact justifies)"
  | .unboundBody i v =>
      s!"body literal #{i}: variable '{v}' is bound by no positive body " ++
      s!"literal — the rule is not range-restricted"

instance : ToString SafetyError := ⟨SafetyError.render⟩

/-- Body-literal scan for the checker: the first unbound variable,
    with the literal's index in the report. -/
def checkBody (bound : List String) : List (Lit Value) → Nat → Option SafetyError
  | [], _ => none
  | l :: rest, i =>
    match l.vars.find? (fun x => !bound.contains x) with
    | some v => some (.unboundBody i v)
    | none => checkBody bound rest (i + 1)

/-- The safety CHECKER: the first offense, loudly, or none. -/
def Rule.check (r : Rule Value) : Option SafetyError :=
  match r.body.findIdx? (fun l => !(l.positive = true)) with
  | some i => some (.negation i)
  | none =>
    match (r.headArgs.flatMap Term.vars).find? (fun x => !r.bound.contains x) with
    | some v => some (.unboundHead v)
    | none => checkBody r.bound r.body 0

/-- A program-level check: the FIRST failing rule, with its index. -/
def Program.check (P : Program Value) : Option (Nat × SafetyError) :=
  match P with
  | [] => none
  | r :: rest =>
    match r.check with
    | some e => some (0, e)
    | none => (Program.check rest).map fun (i, e) => (i + 1, e)

/-- The checked program, or the LOUD refusal: the rendered message names
    the rule index and the offending variable (15-patterns #16). The
    evaluator's entry point (`Datalog.run`) goes through here — an
    unsafe program never reaches evaluation. -/
def Program.checked (P : Program Value) : Except String (Program Value) :=
  match P.check with
  | none => .ok P
  | some (i, e) => .error s!"unsafe rule #{i}: {e}"

/-! ## The grounding engine (executable substitutions + matching) -/

/-- An executable substitution: an association list. -/
abbrev Subst (Value : Type) := List (String × Value)

/-- Lookup — core `List.lookup` over string equality. -/
def Subst.lookup (s : Subst Value) (x : String) : Option Value :=
  List.lookup x s

/-- Apply a substitution to a term: a constant passes through; a
    variable MUST be bound (an unbound variable has no value — the
    range-restriction discipline keeps this from happening on safe
    rules' heads). -/
def Subst.apply (s : Subst Value) : Term Value → Option Value
  | .cst v => some v
  | .var x => s.lookup x

/-- Apply a substitution to a term list: `none` iff some term is
    unbound. -/
def Subst.applyAll (s : Subst Value) : List (Term Value) → Option (List Value)
  | [] => some []
  | t :: ts => (s.apply t).bind fun v => (s.applyAll ts).map (v :: ·)

/-- Match a term pattern against a value list, extending `s`:
    constants must agree; variables bind consistently (first binding
    wins; a conflicting re-binding fails). -/
def matchArgs [DecidableEq Value] :
    List (Term Value) → List Value → Subst Value → Option (Subst Value)
  | [], [], s => some s
  | .cst c :: pt, v :: vt, s => if c = v then matchArgs pt vt s else none
  | .var x :: pt, v :: vt, s =>
    match s.lookup x with
    | some v' => if v' = v then matchArgs pt vt s else none
    | none => matchArgs pt vt ((x, v) :: s)
  | _, _, _ => none

/-- Match one literal against one ground atom. -/
def Lit.matchLit [DecidableEq Value] (l : Lit Value) (a : Atom Value)
    (s : Subst Value) : Option (Subst Value) :=
  if l.pred = a.pred then matchArgs l.args a.args s else none

/-- Match a conjunction of positive literals against the fact set:
    ALL extensions of `s` that ground every literal against some fact.
    (The engine is only ever driven over positive literal lists —
    `Rule.fire` guards this; negation never reaches matching.) -/
def matchAll [DecidableEq Value] (lits : List (Lit Value))
    (F : List (Atom Value)) (s : Subst Value) : List (Subst Value) :=
  match lits with
  | [] => [s]
  | l :: rest =>
    (F.filterMap fun a => l.matchLit a s).flatMap (matchAll rest F)

end Datalog

/-
LintKit.DecideFirst — the ladder's rung-3-over-6 enforcement
(notes/v3/04-verification.md §1: lower rungs need written reasons; the
T5 lesson: small closed spaces get `cases`/`decide`, not sweeps or
scripts).

The finding: a THEOREM whose statement is a decidable proposition over
a CLOSED FINITE space, whose proof is a hand script — `decide` (or the
equation lemmas, or the written reason) is the honest rung below.

The honest minimal detection (and its limits, stated plainly — the
census exists because this is a heuristic):

* STATEMENT side: `Decidable <type>` is SYNTHESIZABLE (the real gate —
  classical fallback is not an instance in scope, so only genuinely
  decidable closed propositions pass; a `∀`-ed statement never does) AND
  the statement mentions a constructor of an ENUM-LIKE inductive
  (2..16 constructors, each field-free and parameter-free — the finite
  space; Nat literals/ctors never qualify, so closed arithmetic trivia
  is not flagged).
* PROOF side: the elaborated proof term is NOT already
  decide/computation-shaped. `by decide` routes through
  `of_decide_eq_true`/`decide`/`ofReduceBool`; `by rfl` is `Eq.refl`-
  headed; a single `simp` that bottoms in `eq_self`/`of_eq_true` is
  kernel computation modulo presentation — all QUIET. A script whose
  term depends on non-computational lemmas (`noConfusion`, simp lemma
  casts, `casesOn` chains) FIRES.

Invisible to this linter: the source-level tactic script itself (the
environment stores elaborated terms, not scripts) — "multi-tactic
script" is approximated by "the term depends on non-computational
lemmas". A script that happens to elaborate to pure computation is
rung-fine and stays quiet.

Default-OFF (the `default_false` token below — the recursiveSimpEqns/
guestBan precedent): the census answers "where do hand scripts stand on
decidable closed spaces" for every theorem of a package; promote to a
gate only after the false-positive review:

  lake exe lintkit --enable=linter.guestlang.decideFirst <roots>

Opt out per site: `@[nolint linter.guestlang.decideFirst "reason"]`.

The five questions (notes/v3/01-core.md):
- root: none — the proof-hygiene census.
- carrier grade: none — host machinery.
- spine reading: interpretation (env → findings).
- ladder rung: this linter ENFORCES 04 §1's rung discipline (decide
  before scripts on closed finite spaces).
- gate row: census only (default OFF) — the sweep reports, the gate
  does not consume.
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- Enum-like inductive: 2..16 constructors, each field-free and
parameter-free (the closed finite space). -/
def enumLikeInduct (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo ii) =>
    ii.ctors.length ≥ 2 && ii.ctors.length ≤ 16 &&
      ii.ctors.all fun c =>
        match env.find? c with
        | some (.ctorInfo ci) =>
          -- strip all leading binders; a field-free ctor's type is the
          -- inductive applied to NOTHING (a parameterized ctor body is
          -- an application, and a fielded ctor has leading foralls)
          let rec stripForall : Expr → Expr
            | .forallE _ _ b _ => stripForall b
            | e => e
          (stripForall ci.type).isConstOf n
        | _ => false
  | _ => false

/-- Does `e` mention a constructor of an enum-like inductive? -/
def mentionsEnumCtor (env : Environment) (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    match env.find? c with
    | some (.ctorInfo ci) => enumLikeInduct env ci.induct
    | _ => false

/-- The decide-routing constants: a proof mentioning any of these IS the
decide rung (`by decide`, `native_decide`, `decide`-routing instances). -/
def decideRoute : List Name :=
  [``of_decide_eq_true, ``Decidable.decide, ``decide, ``Lean.ofReduceBool]

/-- The bottom constant of a proof's application spine (through mdata /
let): `Eq.refl _` → `Eq.refl`, `of_eq_true (eq_self _)` → `of_eq_true`. -/
def proofSpine : Expr → Option Name
  | .mdata _ e => proofSpine e
  | .letE _ _ _ b _ => proofSpine b
  | .app f _ => proofSpine f
  | .const n _ => some n
  | _ => none

/-- Computation-leaf spine bottoms: proofs ELABORATING to these are
kernel computation (the rung-4 shape), not scripts. -/
def computationSpines : List Name :=
  [``Eq.refl, ``of_eq_true, ``eq_self, ``id]

/-- Is `proof` already the decide/computation rung (quiet), as opposed
to a script depending on non-computational lemmas (a finding)? -/
def isComputationProof (proof : Expr) : Bool :=
  let used := proof.getUsedConstants
  used.any (decideRoute.contains ·) ||
    (proofSpine proof).any (computationSpines.contains ·)

meta def decideFirstTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some (.thmInfo di) := env.find? decl | return none
  -- statement side: `Decidable <type>` synthesizable (closed, decidable)
  let dec? : Option Expr ←
    try (some <$> synthInstance (.app (mkConst ``Decidable) di.type))
    catch _ => pure none
  let some _ := dec? | return none
  unless mentionsEnumCtor env di.type do return none
  -- proof side: not already decide/computation-shaped
  if isComputationProof di.value then return none
  return some m!"hand proof over a closed finite space: the statement is \
    decidable, yet the proof term depends on non-computational lemmas — \
    `decide` (or the equation lemmas) is the honest rung \
    (04 §1: lower rungs need written reasons); opt out with \
    `@[nolint linter.guestlang.decideFirst \"reason\"]` if the script is \
    the point"

meta def decideFirstLinter : EnvLinter where
  test := decideFirstTest
  noErrorsFound := "every decidable closed-space theorem decides or computes"
  errorsFound := "hand-script proofs over decidable closed finite spaces"

end LintKit

-- the census linter: registered default-OFF via the `default_false` token
-- (LintKit.Basic — the one-liner registration).
register_guestlang_linter linter.guestlang.decideFirst
  LintKit.decideFirstLinter default_false
  "flag theorems whose statement is decidable over a closed finite space \
    but whose proof is a hand script (04 §1: decide first — census: \
    default OFF, promote to gate after the false-positive review)"

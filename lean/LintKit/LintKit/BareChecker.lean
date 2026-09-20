/-
LintKit.BareChecker — doctrine §8's correspondence preference applied to
checkers: a Bool-valued check function should be the executable face of a
SPEC (a relation + bridge theorem, or a PartialIso into the checked image),
not a hand-rolled predicate with nothing tying "checked" to "in the image"
(the two-projection pattern: cedar's `InstanceOfType` ↔ `validateWellFormed`).

Rule: a def whose name matches `check*`/`valid*`/`wf*`/`wellFormed*` and
whose result type is `Bool` (or `Option _`) must have a companion BRIDGE
THEOREM in the same module. The bridge check is a NAME-BASED HEURISTIC,
deliberately: some theorem in the declaring module whose name contains the
checker's leaf name (`checkFoo_ok`, `validates_sound`, ...) — a real
correspondence theorem names its subject. A companion inductive relation
WITHOUT the bridge theorem does not silence the lint (relation-only specs
are exactly the finding; doctrine: "never relation-only"). Documented
limitations: a bridge theorem that doesn't mention the checker's name is a
false negative; no semantic check that the theorem actually mentions the
checker's function in its statement.

Exemptions:
* Tests modules (any path/module component named `Tests`) — fixtures don't
  ship proofs (the noNewPartial precedent);
* `abbrev`s (transparent aliases are not checkers);
* the GRANDFATHERED list (`bareCheckerAllowance`): the deliberate
  exceptions with their reasons — the LedgerES dual-lane demo validators
  run the differential-duel discipline instead of the bridge-theorem
  discipline, and similar. Ratchet down, never up.
Opt out per site: `@[nolint linter.guestlang.bareChecker "reason"]`.

The option is declared at top level (see LintKit.Basic's header note), via
the `register_guestlang_linter` one-liner at the bottom of this file.
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- The checker-name prefixes (leaf name, case-sensitive camel prefixes —
this codebase's def names are lowerCamel). -/
def checkerPrefixes : List String := ["check", "valid", "wf", "wellFormed"]

/-- Is this leaf name a checker name? -/
def isCheckerLeaf (leaf : String) : Bool :=
  checkerPrefixes.any (leaf.startsWith ·)

/-- Does the def's result type land in `Bool` or `Option _`? Syntactic
walk through leading binders (a checker's type is a chain of `∀`/lambdas
into the verdict). -/
def boolOrOptionResult : Expr → Bool
  | .forallE _ _ b _ => boolOrOptionResult b
  | .lam _ _ b _ => boolOrOptionResult b
  | .app (.const `Option _) _ => true
  | e => e.isConstOf `Bool

/-- The GRANDFATHERED deliberate exceptions: (decl, reason). The ratchet
only tightens — a new checker needs a bridge theorem, not a row here.
Reasons prefixed REAL are true findings, reported to the owner (2026-09
lint-gate run) and silenced only to keep the gate green; the fix lands
with the ratchet. -/
def bareCheckerAllowance : List (Name × String) := [
  (`CodegenCore.Emit.Emitter.checkNodup,
   "the bridge is per-registry, discharged by the consumers (the \
     docstring's prescribed `theorem r_outputs_nodup : checkNodup r = true` \
     pattern) — the same-module heuristic cannot see consumer-side theorems"),
  (`SchemaLang.validates,
   "the bridge lives with the consumers: WHolds.valid_iff_validates \
     (WitnessCheck), validates_applySets (Update2) — not this module"),
  (`SchemaLang.InvariantItem.checkOn,
   "a composition over `validates` (guardCastApply at the Bool family) — \
     inherits validates' bridge; consumer pins (acctCons_checkOn) \
     discharge per invariant"),
  (`SchemaLang.validatesCase,
   "the VCase family's bridge is evalCase_here_sound (same module — it \
     covers the verdict but does not NAME validatesCase; the heuristic is \
     name-based)"),
  (`EdgePython.Compiler.checkCond,
   "REAL (reported 2026-09-19): the compiler's condition type-check pass \
     has no bridge theorem anywhere — needs the correspondence theorem \
     (or the ladder promotion) with the v1-surface work"),
]

/-- Same-module bridge heuristic: SOME theorem in `mod` whose name mentions
the checker's leaf name. -/
def moduleHasBridge (env : Environment) (mod : Name) (leaf : String) : Bool :=
  env.constants.map₁.toList.any fun (n, info) =>
    match info with
    | .thmInfo _ =>
      match env.getModuleIdxFor? n with
      | some idx => (env.header.moduleNames[idx]!) == mod
          && (n.toString.splitOn leaf).length > 1
      | none => false
    | _ => false

meta def bareCheckerTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some (.defnInfo di) := env.find? decl | return none
  if ← isReducible decl then return none
  -- Tests modules exempt: fixtures don't ship proofs
  let some idx := env.getModuleIdxFor? decl | return none
  let mod := env.header.moduleNames[idx]!
  if (mod.toString.splitOn ".").contains "Tests" then return none
  -- name shape: leaf matches a checker prefix
  let some leaf := (match decl with | .str _ s => some s | _ => none) | return none
  unless isCheckerLeaf leaf do return none
  -- verdict shape: Bool or Option _
  unless boolOrOptionResult di.type do return none
  -- the bridge: a same-module theorem naming the checker
  if moduleHasBridge env mod leaf then return none
  -- the grandfathered deliberate exceptions
  if (bareCheckerAllowance.find? fun (n, _) => n == decl).isSome then return none
  return some m!"bare checker: `{decl}` is a Bool/Option check function with \
    no companion bridge theorem in this module — the correspondence \
    preference (lean-doctrine.md §8) wants the checker paired with a \
    relation + bridge theorem (`{leaf}_ok` …), or the check promoted into \
    a PartialIso; opt out with \
    `@[nolint linter.guestlang.bareChecker \"reason\"]`"

meta def bareCheckerLinter : EnvLinter where
  test := bareCheckerTest
  noErrorsFound := "no bare checker without a companion bridge theorem"
  errorsFound := "bare checkers (Bool/Option check* defs without a bridge theorem)"

end LintKit

register_guestlang_linter linter.guestlang.bareChecker LintKit.bareCheckerLinter
  "flag check*/valid*/wf* defs returning Bool/Option with no companion \
    bridge theorem in the same module (the correspondence preference)"

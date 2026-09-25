/-
LintKit.BareChecker — the correspondence preference (notes/v3 doctrine,
pattern #1's enforcement) applied to checkers: a Bool-valued check
function should be the executable face of a SPEC (a relation + bridge
theorem, or a CheckedProp registration), not a hand-rolled predicate with
nothing tying "checked" to "in the image".

Rule: a def whose LEAF name matches `check*`/`valid*`/`wf*`/`wellFormed*`
and whose result type is `Bool` (or `Option _`) must have a companion
BRIDGE in its own module. Two bridge shapes, both name/expression-based
heuristics, deliberately:

1. NAME bridge: some THEOREM in the declaring module whose name contains
   the checker's leaf name (`checkFoo_ok`, `validates_sound`, …) — a real
   correspondence theorem names its subject (the legacy heuristic).
2. REGISTRATION bridge: some DEFINITION in the declaring module whose
   VALUE mentions the checker's full name — the tree's compliant
   `CheckedProp` shape (`Kit.CodeRegistry.codeRegistryWf` carries
   `check := CodeRegistry.check` with the sound/complete proofs beside
   it). Documented approximation: ANY same-module value-level consumer
   counts, so a checker bundled into an unrelated def is a false
   negative; the theorem-name bridge is the primary signal.

A companion inductive relation WITHOUT the bridge does not silence the
lint (relation-only specs are exactly the finding). Documented
limitations: a bridge that neither names the checker nor consumes it in
a value is a false negative; no semantic check that a bridge theorem's
STATEMENT mentions the checker's function.

Exemptions: test modules (any module-name component named `Tests` —
fixtures don't ship proofs), `abbrev`s (transparent aliases are not
checkers), and the GRANDFATHERED list `bareCheckerAllowance` (empty at
the fresh port — the ratchet only tightens; a new checker needs a
bridge, not a row here).
Opt out per site: `@[nolint linter.guestlang.bareChecker "reason"]`.

The five questions (notes/v3/01-core.md):
- root: none — the correspondence preference's enforcement face.
- carrier grade: none — host machinery; the check is decided.
- spine reading: interpretation (env → findings) for the checker class.
- ladder rung: n/a.
- gate row: the lintkit sweep over the gated roots.
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

/-- The GRANDFATHERED deliberate exceptions: (decl, reason). EMPTY at the
fresh port — the ratchet only tightens: a new checker needs a bridge
theorem, not a row here. -/
def bareCheckerAllowance : List (Name × String) := []

/-- One module's (decl, info) pairs — the two bridge walks' shared
same-module resolution prelude (the env-walk twins collapsed). -/
def moduleDecls (env : Environment) (mod : Name) :
    Array (Name × ConstantInfo) :=
  (env.constants.map₁.toList.filterMap fun (n, info) =>
      match env.getModuleIdxFor? n with
      | some idx => if env.header.moduleNames[idx]! == mod then some (n, info) else none
      | none => none).toArray

/-- Same-module NAME bridge: SOME theorem in `mod` whose name mentions
the checker's leaf name. -/
def moduleHasBridge (env : Environment) (mod : Name) (leaf : String) : Bool :=
  (moduleDecls env mod).any fun (n, info) =>
    match info with
    | .thmInfo _ => (n.toString.splitOn leaf).length > 1
    | _ => false

/-- Same-module REGISTRATION bridge: some def in `mod` whose VALUE
mentions the checker's full name (the CheckedProp shape:
`check := CodeRegistry.check`). -/
def moduleHasRegistration (env : Environment) (mod : Name) (decl : Name) : Bool :=
  (moduleDecls env mod).any fun (n, info) =>
    n != decl &&
    match info with
    | .defnInfo di => di.value.getUsedConstants.contains decl
    | _ => false

meta def bareCheckerTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some (.defnInfo di) := env.find? decl | return none
  if ← isReducible decl then return none
  -- Tests modules exempt: fixtures don't ship proofs (LintKit.isTestModule)
  let some mod := modOfDecl env decl | return none
  if isTestModule mod then return none
  -- name shape: leaf matches a checker prefix
  let some leaf := (match decl with | .str _ s => some s | _ => none) | return none
  unless isCheckerLeaf leaf do return none
  -- verdict shape: Bool or Option _
  unless boolOrOptionResult di.type do return none
  -- the bridge: a same-module theorem naming the checker, or a same-module
  -- def whose value consumes it (the CheckedProp registration shape)
  if moduleHasBridge env mod leaf then return none
  if moduleHasRegistration env mod decl then return none
  -- the grandfathered deliberate exceptions
  if (bareCheckerAllowance.find? fun (n, _) => n == decl).isSome then return none
  return some m!"bare checker: `{decl}` is a Bool/Option check function with \
    no companion bridge theorem in this module — the correspondence \
    preference wants the checker paired with a relation + bridge theorem \
    (`{leaf}_ok` …), registered in a CheckedProp, or promoted into a \
    PartialIso/Codec; opt out with \
    `@[nolint linter.guestlang.bareChecker \"reason\"]`"

meta def bareCheckerLinter : EnvLinter where
  test := bareCheckerTest
  noErrorsFound := "no bare checker without a companion bridge theorem"
  errorsFound := "bare checkers (Bool/Option check* defs without a bridge theorem)"

end LintKit

register_guestlang_linter linter.guestlang.bareChecker LintKit.bareCheckerLinter
  "flag check*/valid*/wf* defs returning Bool/Option with no companion \
    bridge theorem in the same module (the correspondence preference)"

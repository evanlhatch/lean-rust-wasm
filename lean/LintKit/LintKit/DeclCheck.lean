/-
LintKit.DeclCheck — the shared DECLARATION-CHECK shape (W7.13; canon row
"an elaboration gate = a decl-check mounted as attribute-gate or lint").

ONE check = `Name → Environment → List DeclDiag`. TWO mounts:

* GATE — `CodegenCore.mountAsGate` (beside `register_check_attribute` in
  CodegenCore.AttrKit): nonempty diags = a hard elaboration error.
* LINT — `mountAsLinter` here: the same diags become an env-linter report.

Enforcement level is the mount, not the check.

Home: LintKit, not codegen-core — LintKit is first in `lean_pkgs` with zero
requires (core-only, no LSpec), so codegen-core may import LintKit but never
the reverse (the `guestlang-lint`-over-oleans discipline would otherwise pull
LSpec into LintKit through codegen-core → TestKit).

Deliberate exclusions: the check is PURE — both mounts supply the
environment. Side effects a gate needs beyond the verdict (e.g. GuestGate's
guest-mark registry write) stay in the attribute handler, outside the check.
-/
module

public meta import Lean
public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- One finding of a declaration check: a stable machine-readable `code`
    plus the rendered `message` (what the gate throws / the lint reports). -/
structure DeclDiag where
  code    : String
  message : String
  deriving Repr, Inhabited, BEq

/-- A declaration check: the decl's name + the environment → its diagnostics
    (empty = pass). Pure on purpose: elaboration gates (CoreM) and
    env-linters (MetaM) both have the env at hand. -/
abbrev DeclCheck := Name → Environment → List DeclDiag

/-- The LINT mount: a `DeclCheck` as a guestlang env-linter — findings are
    reported, elaboration is untouched. The shared skip predicate applies
    (private/internal/compiler-generated decls are never linted). The
    registration boilerplate (option + `addEnvLinterOption` +
    `@[builtin_env_linter]` + the Runner table row) stays per-linter — the
    option must be declared at top level beside the attribute (see
    LintKit.Basic's header note). -/
meta def mountAsLinter (check : DeclCheck) (noErrorsFound errorsFound : String) :
    EnvLinter where
  test decl := do
    if ← skipDecl decl then return none
    match check decl (← getEnv) with
    | [] => return none
    | ds => return some m!"{String.intercalate "\n" (ds.map (·.message))}"
  noErrorsFound := noErrorsFound
  errorsFound := errorsFound

end LintKit

/-
LintKit.DeclCheck — the shared DECLARATION-CHECK shape (an elaboration
gate = a decl-check mounted as attribute-gate or lint; mined from
legacy/lean/LintKit/LintKit/DeclCheck.lean).

ONE check = `Name → Environment → List DeclDiag`. TWO mounts:

* GATE — an attribute handler at `.afterCompilation` (the module system
  commits the body ASYNC: the env at attr time holds only the signature
  axiom, so the gate awaits the committed constant —
  `LintKit.GuestGate.checkGuestAt` is the mount and scans the real
  `defnInfo` directly).
* LINT — `mountAsLinter` here: the same diags become an env-linter report.

Enforcement level is the mount, not the check.

Deliberate exclusions: the check is PURE — both mounts supply the
environment. Side effects a gate needs beyond the verdict (e.g.
GuestGate's guest-mark registry write) stay in the attribute handler,
outside the check.

The five questions (notes/v3/01-core.md):
- root: none — the shared check shape (why one check mounts twice).
- carrier grade: none — the diags are host-side findings, not data.
- spine reading: the check IS the interpretation stage (decl + env → diags).
- ladder rung: n/a (host machinery; no proof family).
- gate row: the guest gate (`LintKit.GuestGate`) + the guestBan census
  lint mount through this shape.
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

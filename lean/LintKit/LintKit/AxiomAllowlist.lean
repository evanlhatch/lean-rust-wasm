/-
LintKit.AxiomAllowlist — env-linter form of `just lean-axioms`
(notes/lean-refactor-guide.md 6.1, notes/lean-doctrine.md §3).

For every theorem/def/opaque declared in a linted module, `collectAxioms`
and flag dependencies outside the allowlist: the core triple
(`propext`, `Classical.choice`, `Quot.sound`) plus the disclosed
`native_decide` trust base — matched by the same rule the justfile's
`lean-axioms` gate uses: an axiom name containing `_native.native_decide.`
(e.g. `Foo._native.native_decide.ax_1_1`, the v4.33 shape). A bare `axiom`
declaration is flagged unless its own name is allowlisted.

This is the per-declaration upgrade over the hand-maintained `#print axioms`
lists: coverage is every linted decl, not a remembered headline set.
Opt out per site with `@[nolint linter.guestlang.axiomAllowlist "reason"]`.

The option is declared at top level (see LintKit.Basic's header note).
-/
import LintKit.Basic

open Lean Meta Linter EnvLinter

@[nolint linter.guestlang.packageNamespace "option declarations must be top-level: the builtin_env_linter registration checks `env.contains <raw option name>` at attribute time (see LintKit.Basic header)"]
register_option linter.guestlang.axiomAllowlist : Bool := {
  defValue := true
  descr := "flag declarations depending on axioms outside the allowlist \
    (propext, Classical.choice, Quot.sound, disclosed native_decide trust base)"
}

-- Feed the option into v4.33's per-declaration snapshot machinery so
-- `set_option linter.guestlang.axiomAllowlist false in <decl>` opts out
-- exactly where written (recorded at `addDecl` for modules importing
-- LintKit, replayed by the runner and by `lake lint --builtin-lint`).
initialize Linter.addEnvLinterOption linter.guestlang.axiomAllowlist

namespace LintKit

/-- The axiom allowlist: core triple + disclosed native_decide trust base
(the justfile `lean-axioms` rule, kept identical in meaning). -/
def isAllowedAxiom (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound ||
  ((toString n).splitOn "_native.native_decide.").length != 1

meta def axiomAllowlistTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some info := env.find? decl | return none
  match info with
  | .axiomInfo _ =>
    if isAllowedAxiom decl then return none
    return some m!"declaration is itself an axiom outside the allowlist \
      (propext, Classical.choice, Quot.sound, disclosed native_decide trust base). \
      Zero-sorry/zero-axiom is the gate (notes/lean-doctrine.md §3)"
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
    let axioms ← collectAxioms decl
    let bad := axioms.filter fun a => !isAllowedAxiom a
    if bad.isEmpty then return none
    return some m!"depends on axioms outside the allowlist: {
      bad.toList} (allowed: propext, Classical.choice, Quot.sound, \
      *_native.native_decide.*)"
  | _ => return none

meta def axiomAllowlistLinter : EnvLinter where
  test := axiomAllowlistTest
  noErrorsFound := "no declarations depend on non-allowlisted axioms"
  errorsFound := "declarations depending on non-allowlisted axioms"

end LintKit

@[builtin_env_linter linter.guestlang.axiomAllowlist]
meta def LintKit.axiomAllowlistLinter.reg : EnvLinter := LintKit.axiomAllowlistLinter

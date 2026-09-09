/-
LintKit.PackageNamespace — notes/lean-refactor-guide.md 6.6:
declarations defined in a package's modules carry the package's namespace
prefix. Cross-namespace leakage is how "temporary" extensions to someone
else's namespace become load-bearing.

Scope: the linted module's root is mapped to the expected prefix(es) by
`packagePrefixes` (one row per workspace package lib root — mirror of
`lean_pkgs` in the justfile). Unknown roots (test exes, drivers: `Tests`,
`GenMain`, `CheckMain`, `BreakingMain`) are skipped, not flagged.

Allowlist mechanisms:
* `@[nolint linter.guestlang.packageNamespace "reason"]` per site — required
  for deliberate `Lean.`-prefixed extensions;
* option `linter.guestlang.packageNamespace.extraPrefixes` (comma-separated,
  set by the driver) for whole extra prefixes.

The options are declared at top level (see LintKit.Basic's header note).
-/
import LintKit.Basic

open Lean Meta Linter EnvLinter

@[nolint linter.guestlang.packageNamespace "option declarations must be top-level: the builtin_env_linter registration checks `env.contains <raw option name>` at attribute time (see LintKit.Basic header)"]
register_option linter.guestlang.packageNamespace : Bool := {
  defValue := true
  descr := "flag declarations whose name lacks their package's namespace prefix"
}

@[nolint linter.guestlang.packageNamespace "option declarations must be top-level: the builtin_env_linter registration checks `env.contains <raw option name>` at attribute time (see LintKit.Basic header)"]
register_option linter.guestlang.packageNamespace.extraPrefixes : String := {
  defValue := ""
  descr := "comma-separated extra allowed namespace prefixes for \
    linter.guestlang.packageNamespace (set by the lint driver)"
}

initialize Linter.addEnvLinterOption linter.guestlang.packageNamespace

namespace LintKit

/-- Module root → allowed declaration-name prefixes. One row per workspace
package library root (the `lean_pkgs` mirror, plus this package and the
demo/oracle roots). -/
def packagePrefixes : List (Name × List Name) := [
  (`Substrait,    [`Substrait]),
  (`CodegenCore,  [`CodegenCore]),
  (`TestKit,      [`TestKit]),
  (`Dbsp,         [`Dbsp]),
  (`Machines,     [`Machines]),
  (`SchemaLang,   [`SchemaLang]),
  (`Demo,         [`Demo]),
  (`Faults,       [`Faults]),
  (`WasmBackend,  [`WasmBackend]),
  (`DemoFn,       [`DemoFn]),
  (`Oracle,       [`Oracle]),
  (`GuestlangStd, [`GuestlangStd]),
  (`LintKit,      [`LintKit])
]

/-- Parse the comma-separated `extraPrefixes` option. -/
def extraPrefixesOf (s : String) : List Name :=
  (s.splitOn ",").filterMap fun p =>
    let p := p.trimAscii.toString
    if p.isEmpty then none else some p.toName

meta def packageNamespaceTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  -- Syntax kinds (`macro`/`syntax`/`elab` declarations) are named by Lean's
  -- own convention (`tacticFoo_`, ...) — outside the package prefix by
  -- design, not by drift.
  if Parser.isValidSyntaxNodeKind env decl then return none
  let some mod ← findModuleOf? decl | return none
  let some expected := packagePrefixes.lookup mod.getRoot | return none
  let allowed := expected ++ extraPrefixesOf
    (linter.guestlang.packageNamespace.extraPrefixes.get (← getOptions))
  if allowed.any (·.isPrefixOf decl) then return none
  return some m!"declaration is outside its package's namespace: module root \
    `{mod.getRoot}` expects prefix {expected} — move it under the prefix, or \
    for a deliberate cross-namespace extension opt out with \
    `@[nolint linter.guestlang.packageNamespace \"reason\"]`"

meta def packageNamespaceLinter : EnvLinter where
  test := packageNamespaceTest
  noErrorsFound := "every declaration carries its package's namespace prefix"
  errorsFound := "declarations outside their package's namespace"

end LintKit

@[builtin_env_linter linter.guestlang.packageNamespace]
meta def LintKit.packageNamespaceLinter.reg : EnvLinter := LintKit.packageNamespaceLinter

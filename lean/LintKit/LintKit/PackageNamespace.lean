/-
LintKit.PackageNamespace — notes/lean-refactor-guide.md 6.6:
declarations defined in a package's modules carry the package's namespace
prefix. Cross-namespace leakage is how "temporary" extensions to someone
else's namespace become load-bearing.

Scope, DEFAULT mode — the FOREIGN-NAMESPACE rule (the `Fin.ofList?`
lesson, flatland lineage): a decl is flagged only when its name is parked
in a namespace that is not this module's own business — a core/framework
root (`Lean`, `Fin`, `List`, …; `foreignRoots`) or ANOTHER workspace
package's root. Unprefixed local names (`Demo.User`) and module-local
namespaces (`Async.Future` in Demo) are ordinary organization and pass.
STRICT mode — the original module-root→prefix rule — is opt-in via
`linter.guestlang.packageNamespace.strict` (whole-tree ratchet if ever
wanted; default off: the strict rule fires on every unprefixed local
decl, which is noise, not hazard).

Unknown module roots (test exes, drivers: `Tests`, `GenMain`,
`CheckMain`, `BreakingMain`) are skipped in strict mode; the foreign rule
needs no root table.

Allowlist mechanisms:
* `@[nolint linter.guestlang.packageNamespace "reason"]` per site — required
  for deliberate `Lean.`-prefixed extensions;
* option `linter.guestlang.packageNamespace.extraPrefixes` (comma-separated,
  set by the driver) for whole extra prefixes.

Structural exemptions (no per-site opt-out exists at the decl's source):
* `@[derived]` (LintKit.Basic) — generated output, stamped by the emitting
  command (the per-consumer `set_option … false` ritual is dead);
* `linter.`-rooted decls — option declarations live at TOP LEVEL by Lean's
  own registration contract (`builtin_env_linter` checks `env.contains <raw
  option name>` at attribute time), so their root is not drift; the 16
  verbatim per-option nolint copies this replaced.
* `Lean.Parser.Category.*` — a syntax category cannot live in a library
  namespace (Lean's constraint; the machineClause lesson).

The options are declared at top level (see LintKit.Basic's header note).
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

register_option linter.guestlang.packageNamespace.extraPrefixes : String := {
  defValue := ""
  descr := "comma-separated extra allowed namespace prefixes for \
    linter.guestlang.packageNamespace (set by the lint driver)"
}

register_option linter.guestlang.packageNamespace.strict : Bool := {
  defValue := false
  descr := "strict mode: require EVERY declaration in a table-root module to \
    carry the package prefix (the original rule; default is the \
    foreign-namespace rule)"
}

namespace LintKit

/-- Module root → allowed declaration-name prefixes. One row per workspace
package library root (the `lean_pkgs` mirror, plus this package and the
demo/oracle roots). -/
def packagePrefixes : List (Name × List Name) := [
  (`Substrait,    [`Substrait]),
  (`QLang,        [`QLang]),
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
  (`LintKit,      [`LintKit]),
  (`Ledger,       [`Ledger]),
  (`LedgerFn,     [`LedgerFn]),
  (`FeatureFlags,       [`FeatureFlags]),
  (`FeatureFlagsFn,     [`FeatureFlagsFn]),
  (`EdgePython,   [`EdgePython]),
]

/-- Parse the comma-separated `extraPrefixes` option. -/
def extraPrefixesOf (s : String) : List Name :=
  (s.splitOn ",").filterMap fun p =>
    let p := p.trimAscii.toString
    if p.isEmpty then none else some p.toName

/-- Core/framework namespaces a module must NOT park helpers in — the
`Fin.ofList?` hazard: a helper here reads as stock API and can collide or
become load-bearing on an upstream rename. Extending this list is a
deliberate doctrine decision, not a convenience. -/
def foreignRoots : List Name :=
  [`Lean, `Init, `Std, `Lake,
   `Fin, `List, `String, `Option, `Array, `IO, `Nat, `Int, `Float, `Bool,
   `Char, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `Order, `System]

meta def packageNamespaceTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  -- GENERATED output: the emitting command stamps `@[derived]` — the
  -- structural exemption. A generated decl has no honest source site for a
  -- per-site opt-out (the schema_update instances park in SchemaLang by
  -- the framework's construction); the per-consumer `set_option … false`
  -- ritual this replaces is dead.
  if hasDerived env decl then return none
  -- OPTION declarations: `register_option` must sit at TOP LEVEL (the
  -- `builtin_env_linter` registration checks `env.contains <raw option
  -- name>` at attribute time), so an option decl's root IS `linter` —
  -- Lean's own option-registration namespace, not drift. (The per-option
  -- `@[nolint]` copies this replaces were 16 verbatim strings.)
  if decl.getRoot == `linter then return none
  -- Syntax kinds (`macro`/`syntax`/`elab` declarations) are named by Lean's
  -- own convention (`tacticFoo_`, ...) — outside the package prefix by
  -- design, not by drift.
  if Parser.isValidSyntaxNodeKind env decl then return none
  -- Syntax CATEGORIES (`declare_syntax_cat`) are named
  -- `Lean.Parser.Category.<name>` BY LEAN ITSELF — a category cannot live
  -- in a library namespace, so this is Lean's constraint, not namespace
  -- drift. (The per-site nolint can't carry this: elaborating the attr
  -- needs the linter registered in THAT file's env, which mathlib-side
  -- packages don't import — the machineClause lesson, 2026-09-19.)
  if (`Lean.Parser.Category).isPrefixOf decl then return none
  let some mod ← findModuleOf? decl | return none
  if linter.guestlang.packageNamespace.strict.get (← getOptions) then
    let some expected := packagePrefixes.lookup mod.getRoot | return none
    let allowed := expected ++ extraPrefixesOf
      (linter.guestlang.packageNamespace.extraPrefixes.get (← getOptions))
    if allowed.any (·.isPrefixOf decl) then return none
    return some m!"declaration is outside its package's namespace: module root \
      `{mod.getRoot}` expects prefix {expected} — move it under the prefix, or \
      for a deliberate cross-namespace extension opt out with \
      `@[nolint linter.guestlang.packageNamespace \"reason\"]"
  -- Default: the foreign-namespace rule.
  match decl with
  | .str p _ =>
    -- unprefixed module-local names are ordinary, not drift
    if p.isAnonymous then return none
    let root := p.getRoot
    -- the declaring module's own package prefix is never foreign
    if (packagePrefixes.lookup mod.getRoot).getD []
        |>.any (fun pref : Name => pref.isPrefixOf decl) then
      return none
    -- a root owned by a constant of the SAME module (e.g. `Order.items`
    -- where `structure Order` is declared in this module) is the module's
    -- own type namespace — projections necessarily live under it
    if (env.find? root).isSome
        && env.getModuleIdxFor? root == env.getModuleIdxFor? decl then
      return none
    let foreignCore := foreignRoots.contains root
    let foreignPkg :=
      packagePrefixes.any fun (r, _) => r == root && r != mod.getRoot
    if foreignCore || foreignPkg then
      return some m!"declaration parked in a foreign namespace `{root}`: \
        helpers must not extend core's or another package's namespace (the \
        `Fin.ofList?` lesson) — move it under this module's own namespace, \
        or opt out with `@[nolint linter.guestlang.packageNamespace \
        \"reason\"]"
    return none
  | _ => return none

meta def packageNamespaceLinter : EnvLinter where
  test := packageNamespaceTest
  noErrorsFound := "no declaration parked in a foreign namespace"
  errorsFound := "declarations parked in foreign namespaces"

end LintKit

-- the main switch registered via `register_guestlang_linter` (LintKit.Basic):
-- option + snapshot hookup + the stock-`lake lint` mount, one command.
register_guestlang_linter linter.guestlang.packageNamespace
  LintKit.packageNamespaceLinter
  "flag declarations whose name lacks their package's namespace prefix"

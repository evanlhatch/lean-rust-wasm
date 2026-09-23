/-
LintKit.PackageNamespace — the cone/discipline linter (mined from
legacy/lean/LintKit/LintKit/PackageNamespace.lean): declarations defined
in a package's modules carry the package's namespace prefix. Cross-
namespace leakage is how "temporary" extensions to someone else's
namespace become load-bearing (the `Fin.ofList?` lesson).

DEFAULT mode — the FOREIGN-NAMESPACE rule: a decl is flagged only when
its name is parked in a namespace that is not this module's own business
— a core/framework root (`Lean`, `Fin`, `List`, …; `foreignRoots`) or
ANOTHER workspace package's root. Unprefixed local names (`Demo.User`)
and module-local namespaces are ordinary organization and pass.

Unknown module roots (test exes, drivers) pass: the foreign rule needs
no root table.

Allowlist mechanisms:
* `@[nolint linter.guestlang.packageNamespace "reason"]` per site —
  required for deliberate `Lean.`-prefixed extensions;
* option `linter.guestlang.packageNamespace.extraPrefixes` (comma-
  separated, set by the driver) for whole extra prefixes.

Structural exemptions (no per-site opt-out exists at the decl's source):
* `linter.`-rooted decls — option declarations live at TOP LEVEL by
  Lean's own registration contract (`builtin_env_linter` checks
  `env.contains <raw option name>` at attribute time), so their root is
  not drift;
* `Lean.Parser.Category.*` — a syntax category cannot live in a library
  namespace (Lean's constraint; the machineClause lesson);
* syntax kinds generally (`macro`/`syntax`/`elab` decls are named by
  Lean's own convention — `isValidSyntaxNodeKind` covers them).

Deliberate exclusions vs the legacy module: the STRICT mode (module-
root→prefix for every decl) and the `@[derived]` structural exemption —
strict is a whole-tree ratchet nobody asked for yet; `derived` arrives
with the codegen lane that stamps it (nothing-without-a-consumer).

The options are declared at top level (see LintKit.Basic's header note).

The five questions (notes/v3/01-core.md):
- root: none — the namespace-discipline linter.
- carrier grade: none — a decided name-prefix check, not a crossing.
- spine reading: the interpretation stage (linted env → findings).
- ladder rung: n/a (host machinery).
- gate row: the lintkit sweep over the gated roots.
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

namespace LintKit

/-- Module root → allowed declaration-name prefixes. One row per
workspace library root. -/
def packagePrefixes : List (Name × List Name) := [
  (`LintKit, [`LintKit]),
  (`Gates,   [`Gates]),
  (`SchemaCore, [`SchemaCore])
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
  -- OPTION declarations: `register_option` must sit at TOP LEVEL (the
  -- `builtin_env_linter` registration checks `env.contains <raw option
  -- name>` at attribute time), so an option decl's root IS `linter` —
  -- Lean's own option-registration namespace, not drift.
  if decl.getRoot == `linter then return none
  -- Syntax kinds (`macro`/`syntax`/`elab` declarations) are named by Lean's
  -- own convention (`tacticFoo_`, ...) — outside the package prefix by
  -- design, not by drift.
  if Parser.isValidSyntaxNodeKind env decl then return none
  -- Syntax CATEGORIES (`declare_syntax_cat`) are named
  -- `Lean.Parser.Category.<name>` BY LEAN ITSELF — a category cannot live
  -- in a library namespace, so this is Lean's constraint, not namespace
  -- drift. (The machineClause lesson.)
  if (`Lean.Parser.Category).isPrefixOf decl then return none
  let some mod ← findModuleOf? decl | return none
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

-- the main switch registered via `register_guestlang_linter` (LintKit.Basic's
-- one-liner): option + snapshot hookup + the stock-`lake lint` mount.
register_guestlang_linter linter.guestlang.packageNamespace
  LintKit.packageNamespaceLinter
  "flag declarations whose name is parked in a foreign (core's or another \
    package's) namespace"

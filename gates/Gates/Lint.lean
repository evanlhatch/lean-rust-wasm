/-
Gates.Lint — the lint gate row (`gates lint [--package=<dir>]`): the
env/text linters' CI teeth (the enforcement wave's headline — the audit
found `gates all` with no lintkit row, the env/text linters toothless in
the battery).

The row rides LintKit's runner — the `lintkit` exe's OWN discipline in a
gate row: the shard body is `LintKit.lintShard` (Runner), the SAME
function the `lintkit` exe's `--package=` dispatch calls (one writer of
the lint fold; no parallel copy to drift). The dispatch is the shared
`Gates.gateDispatch` — the warm fold without `--package`, one package's
shard face in-process with it; the warm fold is TWO legs (the library
rows in-process against the shared env, the tests-lib rows as child
shards via `Gates.testLibPool` — the root-`main` collision's honest
remainder, the RSS admission's pool discipline in Gates.Common).

Teeth: the row FAILS when any gated package has findings (exit 1 per
shard, the fold collects). The tree must be lint-clean to land it — the
enforcement wave's adjudications: the SchemaCore str-lit duplicate
deduped into `Spine.strLit`, the TS wire face's unregistered round-trip
and the differential twins' deliberate copies carried as NAMED
allowance/nolint rows. The GATE's own sabotage teeth live in
GatesTests.Main: the shard verdict over the planted violator
(`LintKitFixtures.Violations`) MUST fail, the compliant module
(`LintKitFixtures.Clean`) MUST pass — a planted finding the row cannot
silence, and its negative control.

The five questions (notes/v3/01-core.md): none of its own — the lint
fold's answers live in LintKit.Runner; this module is the gate row.
-/
import Lean
import LintKit
import Gates.Packages
import Gates.Common

namespace Gates.Lint

open Gates (PkgSpec gatedPackages pkgIsTestLib testLibPackages)

/-- The text-lint mounts for one package's roots (the `lintkit` exe's
`Cli.defaultSrcRoots` derivation, scoped to the package — the same
table-driven shape, Gates.Packages the single source). -/
def srcRootsFor (pkg : PkgSpec) : Array (Lean.Name × String) :=
  pkg.roots.map fun r => (r, pkg.srcDir)

/-- ONE gated package's lint shard (the child dispatch's body): the
package's env loaded, `LintKit.lintShard` over the EXACT roots (the
planted fixture rigs' namespace siblings stay out — the runner's
lintModulesExact discipline), the text lints over the same roots'
sources. Exit 1 = findings (or a load failure — loud on stderr). -/
unsafe def runPkg (pkg : PkgSpec) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  let cfg : LintKit.DriverConfig := { srcRoots := srcRootsFor pkg }
  match ← Gates.loadPkgEnv base pkg with
  | .error e =>
      IO.eprintln s!"lint: {pkg.dir}: LOAD FAILED — {e}"
      return 1
  | .ok env =>
      let mods := String.intercalate " " (pkg.roots.map toString).toList
      return if ← LintKit.lintShard s!"{pkg.dir} ({mods})" pkg.roots cfg env
        then 1 else 0

/-- The WARM face, TWO LEGS (the Axioms twin's shape): the LIBRARY
rows' lint fold against the shared warm env (per-package root scopes
via `lintModulesExact`'s prefix filter + the per-root dup caches), the
TESTS-LIB rows as child shards (`Gates.testLibPool` — the root-`main`
collision bars them from the warm env), their captured stdout
re-printed per package (the findings' bytes unchanged, batched at
completion). The fold fails when ANY package has findings.
Verdict-equivalent to the shard discipline: the env linters are
per-decl or explicitly scoped per root, the text lints scan the same
sources (the warm note in `Gates.loadWarmEnv`'s header). -/
unsafe def runWarm (env : Lean.Environment) : IO UInt32 := do
  let mut failed := false
  for pkg in gatedPackages do
    unless pkgIsTestLib pkg do
      let mods := String.intercalate " " (pkg.roots.map toString).toList
      let cfg : LintKit.DriverConfig := { srcRoots := srcRootsFor pkg }
      if ← LintKit.lintShard s!"{pkg.dir} ({mods})" pkg.roots cfg env then
        failed := true
  for (_, code, out) in ← Gates.testLibPool "lint" do
    IO.print out
    if code != 0 then failed := true
  if failed then
    IO.println <| toString (GateDiag eGT0013
      "lint: FAILED — fix the findings or carry the named \
      `@[nolint … \"reason\"]`/allowance row (the adjudication discipline)")
    return 1
  IO.println s!"lint: clean ({gatedPackages.size} gated package(s) folded — \
    Gates.Packages' table, the single source)"
  return 0

/-- `gates lint [--package=<dir>]` — the lint gate row: without the
flag, the WARM fold (the tree's env loaded once, every package's lint
in-process); with it, ONE package's shard face in-process (the debug
face). The fold fails when ANY package has findings. -/
unsafe def run (package : Option String) : IO UInt32 :=
  Gates.gateDispatch "lint" package runPkg
    (Gates.withWarmEnv "lint" runWarm)

end Gates.Lint

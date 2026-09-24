/-
Gates.Packages — the gated package set, as data (mined from
legacy/lean/gates/Gates/Packages.lean: the per-package gates' shared
loader + package table).

The fresh tree is ONE lake package; its libraries are the gated set.
Oleans live in the ROOT build dir (the single-lake layout); the exe runs
from the repo root, so paths are root-relative.

Deliberate exclusions vs the legacy module: the monolith override fields
(`oleanDir`/`srcDir`/`leanPath` — one layout here) and the per-package
`Tests.Main` roots (no test drivers yet — they arrive with their first
spec).

The five questions (notes/v3/01-core.md):
- root: Universe — the gated set as closed data (cone-ordered).
- carrier grade: none — a plain table.
- spine reading: the shared input every gate folds (the loader is the
replay preamble).
- ladder rung: n/a.
- gate row: the shared row of ALL gate rows — the axiom report sweeps
exactly these roots; a new gated root lands here deliberately.
-/
import Lean

namespace Gates

/-- One gated package: its report-section key (`dir`) + the root modules
whose code the per-package gates cover. -/
structure PkgSpec where
  dir : String
  roots : Array Lean.Name
  deriving Repr, Inhabited

/-- Load one gated package's environment: the root build dir prepended to
the search path (its modules win over same-named dependency modules),
initializers executed, its root modules `importModules`'d at the
per-package gate trust level. The loading gates own only their
per-package post-processing after this. -/
unsafe def loadPkgEnv (base : Lean.SearchPath) (pkg : PkgSpec) :
    IO (Except String Lean.Environment) := do
  Lean.searchPathRef.set (".lake/build/lib/lean" :: base)
  try
    Lean.enableInitializersExecution
    let env ← Lean.importModules (pkg.roots.map ({ module := · })) {}
      (trustLevel := 1024) (loadExts := true)
    return .ok env
  catch e =>
    return .error (toString e)

/-- The gated set: the tree's own libraries, cone-ordered. -/
def gatedPackages : Array PkgSpec := #[
  { dir := "LintKit", roots := #[`LintKit] },
  { dir := "Gates",   roots := #[`Gates] },
  { dir := "Wit",     roots := #[`Wit] },
  { dir := "SchemaCore", roots := #[`SchemaCore, `SchemaCore.Slice] },
  { dir := "ZSet",    roots := #[`ZSet] },
  { dir := "Machines", roots := #[`Machines] }
]

end Gates

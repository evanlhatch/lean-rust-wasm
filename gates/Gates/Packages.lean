/-
Gates.Packages — the gated package set, as data (mined from
legacy/lean/gates/Gates/Packages.lean: the per-package gates' shared
loader + package table).

The fresh tree is ONE lake package; its libraries are the gated set.
Oleans live in the ROOT build dir (the single-lake layout); the exe runs
from the repo root, so paths are root-relative.

SINGLE SOURCE (the re-audit's finding: this table and lintkit's
`Cli.gatedRoots` had drifted apart — the newest lanes gated by neither).
ONE table here now drives EVERY consumer: the axiom sweep, the lint
driver (`lintkit`'s default roots + its source mounts), the kernel-check
replay's srcDirs, the docs-check envs, the impact core's gated test —
each consumes this table, never a parallel copy. The drift guard
(`gates packages-check`) checks the table against the LAKEFILE both
directions: a lakefile library with no row, a row naming no library, a
lakefile root missing from its row, and a row root with no source file
are all findings — a landed library without its gates row fails CI (the
cone-table's loud-gap precedent).

Row conventions (each library gets its honest row — the tests-libs
included):
- `dir` IS the lakefile `[[lean_lib]]` name (the report-section key and
  the drift guard's join key);
- `srcDir` IS the lakefile row's srcDir (the text lints' source mounts);
- `roots` mirror the lakefile row's declared `roots` — IMPORTABLE
  modules (there are no bare `<Lib>Tests` umbrellas; the tests-libs'
  own lakefile comment records that), named in full so the
  `packageDecls` prefix filter and `importModules` both see them.
  DELIBERATE ADDITIONS beyond the lakefile roots: fixture modules the
  lib's discipline claims — `SchemaCore.Slice` (the registered fixture
  the drivers replay), the existing convention kept.
- DELIBERATE EXCLUSIONS, named: the planted lint fixtures
  (`LintKitTests.Violator`, `LintKitFixtures.Violations`,
  `LintKitFixturesUntabled.Violator`) stay OUT of every row — they
  exist to FAIL the lints (their consumers are the LintKitTests pins,
  which demand exactly that failure); gating them would gate a
  permanent red. The glob-absorbed test SIBLINGS a TestsLib root
  imports (e.g. `SchemaTests.Commit`) ride the kernel-check module
  sweep; the decl-level sweeps cover the declared roots.

The five questions (notes/v3/01-core.md):
- root: Universe — the gated set as closed data (cone-ordered).
- carrier grade: none — a plain table.
- spine reading: the shared input every gate folds (the loader is the
replay preamble).
- ladder rung: n/a.
- gate row: the shared row of ALL gate rows — the axiom report sweeps
exactly these roots; a new gated root lands here deliberately, and
`gates packages-check` refuses the tree until it does.
-/
import Lean

namespace Gates

/-- One gated package: its lakefile library name (`dir` — the
report-section key + the drift guard's join key), the library's srcDir
(the text lints' source mounts) + the root modules whose code the
per-package gates cover. -/
structure PkgSpec where
  dir : String
  srcDir : String
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

/-- The gated set: the tree's own libraries, cone-ordered (C0 machinery
→ C1 domain cores → C2 host lanes → C3 apps; the cone table's order).
ONE row per gated `[[lean_lib]]`; the ABSENT rows are named in
`Gates.PackagesCheck.expectedUngated` (the loud exclusion list) —
`gates packages-check` enforces the agreement against the lakefile. -/
def gatedPackages : Array PkgSpec := #[
  -- ── C0 machinery ──
  { dir := "Kit", srcDir := "kit", roots := #[`Kit] },
  { dir := "KitTestsLib", srcDir := "kit",
    roots := #[`KitTests.Main, `KitTests.Axioms] },
  { dir := "TextKit", srcDir := "textkit", roots := #[`TextKit] },
  { dir := "TestingKit", srcDir := "testingkit", roots := #[`TestingKit] },
  { dir := "LintKit", srcDir := "lintkit", roots := #[`LintKit] },
    -- LintKitTestsLib: row DELIBERATELY ABSENT (the linter's own rig —
    -- LintKitFixtures.Clean turns the census linters ON via set_option;
    -- its consumers are the LintKitTests pins). Same class as the
    -- planted-violator exclusions in the header.
  { dir := "Gates", srcDir := "gates", roots := #[`Gates] },
  { dir := "GatesTestsLib", srcDir := "gates",
    roots := #[`GatesTests.Main, `GatesTests.Axioms] },
  -- ── C1 domain cores ──
  { dir := "SchemaCore", srcDir := "schemacore",
    roots := #[`SchemaCore, `SchemaCore.Slice] },
    -- `Slice` is the registered fixture module (the drivers replay it)
    -- SchemaTestsLib: row PENDING (PackagesCheck.expectedUngated — the
    -- sweep's first firing: ghostMachineKeys/ticketMachineKeys
    -- alpha-equivalent duplicates; the schema owner's dedup/nolint)
  { dir := "WasmCore", srcDir := "wasmcore", roots := #[`WasmCore] },
  { dir := "WasmCoreTestsLib", srcDir := "wasmcore",
    roots := #[`WasmCoreTests.Main, `WasmCoreTests.Axioms] },
  { dir := "Wit", srcDir := "wit", roots := #[`Wit] },
  { dir := "Machines", srcDir := "machines", roots := #[`Machines] },
  { dir := "MachinesTestsLib", srcDir := "machines",
    roots := #[`MachinesTests.Main, `MachinesTests.Axioms] },
  { dir := "ZSet", srcDir := "zset", roots := #[`ZSet] },
  { dir := "ZSetTestsLib", srcDir := "zset",
    roots := #[`ZSetTests.Main, `ZSetTests.Axioms] },
  { dir := "Datalog", srcDir := "datalog", roots := #[`Datalog] },
  { dir := "DatalogTestsLib", srcDir := "datalog",
    roots := #[`DatalogTests.Main, `DatalogTests.Axioms] },
  { dir := "Cost", srcDir := "cost", roots := #[`Cost] },
  { dir := "CostTestsLib", srcDir := "cost",
    roots := #[`CostTests.Main, `CostTests.Axioms] },
  { dir := "Effects", srcDir := "effects", roots := #[`Effects] },
  { dir := "EffectsTestsLib", srcDir := "effects",
    roots := #[`EffectsTests.Main, `EffectsTests.Axioms] },
  { dir := "Contracts", srcDir := "contracts", roots := #[`Contracts] },
  { dir := "ContractsTestsLib", srcDir := "contracts",
    roots := #[`ContractsTests.Main, `ContractsTests.Axioms] },
  { dir := "Analysis", srcDir := "analysis", roots := #[`Analysis] },
  { dir := "AnalysisTestsLib", srcDir := "analysis",
    roots := #[`AnalysisTests.Main, `AnalysisTests.Axioms] },
  { dir := "Query", srcDir := "query", roots := #[`Query] },
  { dir := "QueryTestsLib", srcDir := "query",
    roots := #[`QueryTests.Main, `QueryTests.Axioms] },
  { dir := "Vortex", srcDir := "vortex", roots := #[`Vortex] },
  { dir := "VortexTestsLib", srcDir := "vortex",
    roots := #[`VortexTests.Main, `VortexTests.Axioms] },
  { dir := "Circuit", srcDir := "circuit", roots := #[`Circuit] },
  { dir := "CircuitTestsLib", srcDir := "circuit",
    roots := #[`CircuitTests.Main, `CircuitTests.Axioms] },
  -- ── C2 host lanes ──
  { dir := "Inspector", srcDir := "inspector", roots := #[`Inspector] },
  { dir := "InspectorTestsLib", srcDir := "inspector",
    roots := #[`InspectorTests.Main, `InspectorTests.Axioms] },
  { dir := "Scaffold", srcDir := "scaffold", roots := #[`Scaffold] },
  { dir := "ScaffoldTestsLib", srcDir := "scaffold",
    roots := #[`ScaffoldTests.Main, `ScaffoldTests.Axioms] },
  { dir := "Guest", srcDir := "guest", roots := #[`Guest] },
  { dir := "GuestTestsLib", srcDir := "guest",
    roots := #[`GuestTests.Main, `GuestTests.Fixture, `GuestTests.Axioms] },
  { dir := "ComponentTestsLib", srcDir := "guest",
    roots := #[`ComponentTests.Main, `ComponentTests.Fixture,
               `ComponentTests.Axioms, `ComponentTests.StringFixture] },
    -- the component lane's battery + its fixtures: one lib, one row
  -- ── C3 apps ──
  { dir := "ScaffoldDemo", srcDir := ".",
    roots := #[`DemoApp.Reg, `DemoApp.App, `DemoApp.Flow, `DemoApp.Tests] },
  { dir := "ScaffoldLedger", srcDir := ".",
    roots := #[`LedgerApp.Reg, `LedgerApp.App, `LedgerApp.Flow, `LedgerApp.Tests] }
]

end Gates

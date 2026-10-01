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
module

public import Lean

@[expose] public section

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
    -- `importAll := true`: the gates see the tree's INTERNALS — the
    -- module system's privacy hides non-public decls from a plain
    -- import; same-package, so the private scope is the gates' by
    -- right (the blind spot was measured: 0 decls read under plain).
    let env ← Lean.importModules (pkg.roots.map ({ module := ·, importAll := true })) {}
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
    -- LaneDemo: the lane-teeth fixture — its teeth + entourage pins fire
    -- at ELABORATION, so it must be a swept root (a module's own
    -- initializers run only at import; the registration/consumption
    -- pair is LaneReg → LaneDemo). LaneDemo2 is the wave-30 A2
    -- acceptance fixture (a NEW lane = one row + one reader over the
    -- ONE log; the pair is LaneReg2 → LaneDemo2).
    roots := #[`KitTests.Main, `KitTests.Axioms, `KitTests.LaneReg,
               `KitTests.LaneDemo, `KitTests.LaneReg2, `KitTests.LaneDemo2,
               `KitTests.Cli] },
  { dir := "TextKit", srcDir := "textkit", roots := #[`TextKit] },
  { dir := "TestingKit", srcDir := "testingkit", roots := #[`TestingKit] },
  { dir := "LintKit", srcDir := "lintkit", roots := #[`LintKit] },
    -- LintKitTestsLib: row DELIBERATELY ABSENT (the linter's own rig —
    -- LintKitFixtures.Clean turns the census linters ON via set_option;
    -- its consumers are the LintKitTests pins). Same class as the
    -- planted-violator exclusions in the header.
  { dir := "Gates", srcDir := "gates", roots := #[`Gates] },
  { dir := "GatesTestsLib", srcDir := "gates",
    -- Config: the C4 dogfood's teeth (the knobs' config-face pins + its
    -- `#print axioms` pin) — a lakefile root, so a swept root (the
    -- UNGATEDROOT face refuses the tree until the row mirrors it).
    roots := #[`GatesTests.Main, `GatesTests.Axioms, `GatesTests.Config,
               `GatesTests.Baselines] },
  -- ── C1 domain cores ──
  { dir := "SchemaCore", srcDir := "schemacore",
    roots := #[`SchemaCore, `SchemaCore.Slice] },
    -- `Slice` is the registered fixture module (the drivers replay it)
    -- SchemaTestsLib: row LANDED — the keyless-case fix in the preset
    -- (SchemaCore.EntityMachine emits `<m>Keys` as an `abbrev` when no
    -- `key:` clause — the dupDefBodies transparent-alias case), so no
    -- generated duplicate bodies remain (ex-SchemaTestsLib's
    -- expectedUngated exclusion, remediated).
  { dir := "SchemaTestsLib", srcDir := "schemacore",
    roots := #[`SchemaTests.Main, `SchemaTests.Axioms,
               `SchemaTests.EntityMachine, `SchemaTests.Witness] },
  { dir := "WasmCore", srcDir := "wasmcore", roots := #[`WasmCore] },
  { dir := "WasmCoreTestsLib", srcDir := "wasmcore",
    roots := #[`WasmCoreTests.Main, `WasmCoreTests.Axioms] },
  { dir := "Wit", srcDir := "wit", roots := #[`Wit] },
  { dir := "Machines", srcDir := "machines", roots := #[`Machines] },
  { dir := "MachinesTestsLib", srcDir := "machines",
    roots := #[`MachinesTests.Main, `MachinesTests.Axioms] },
  { dir := "ZSet", srcDir := "zset", roots := #[`ZSet] },
  { dir := "ZSetTestsLib", srcDir := "zset",
    roots := #[`ZSetTests.Main, `ZSetTests.Axioms,
               `ZSetTests.Circuit, `ZSetTests.CircuitAxioms,
               `ZSetTests.Optimizer] },
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
    roots := #[`ContractsTests.Main, `ContractsTests.Axioms,
               -- the feasibility discipline's teeth (B2: the spec-sanity
               -- row) — a swept root so the axiom + census sweeps see it
               -- (the SchemaCore.Slice deliberate-addition convention)
               `ContractsTests.Feasibility] },
  { dir := "Analysis", srcDir := "analysis", roots := #[`Analysis] },
  { dir := "AnalysisTestsLib", srcDir := "analysis",
    roots := #[`AnalysisTests.Main, `AnalysisTests.Axioms] },
  { dir := "Query", srcDir := "query", roots := #[`Query] },
  { dir := "QueryTestsLib", srcDir := "query",
    roots := #[`QueryTests.Main, `QueryTests.Axioms, `QueryTests.ExplainSpecs,
    `QueryTests.Bridge, `QueryTests.QLangSpecs, `QueryTests.Optimize] },
  { dir := "Vortex", srcDir := "vortex", roots := #[`Vortex] },
  { dir := "VortexTestsLib", srcDir := "vortex",
    roots := #[`VortexTests.Main, `VortexTests.Axioms] },
  -- Substrait: the substrait port's seed (notes/v3/14-build-map.md's
  -- substrait row): the wire Proto types + the typed layer RETARGETED
  -- onto SchemaCore's closed Ty + the text tables. C1 (the cone rule;
  -- imports SchemaCore + TextKit).
  { dir := "Substrait", srcDir := "substrait", roots := #[`Substrait] },
  { dir := "SubstraitTestsLib", srcDir := "substrait",
    roots := #[`SubstraitTests.Main, `SubstraitTests.Axioms] },
  -- ── C2 host lanes ──
  { dir := "Inspector", srcDir := "inspector", roots := #[`Inspector] },
  { dir := "InspectorTestsLib", srcDir := "inspector",
    roots := #[`InspectorTests.Main, `InspectorTests.Axioms,
               `InspectorTests.ExplainSpecs] },
  { dir := "Scaffold", srcDir := "scaffold", roots := #[`Scaffold] },
  { dir := "ScaffoldTestsLib", srcDir := "scaffold",
    roots := #[`ScaffoldTests.Main, `ScaffoldTests.Axioms] },
  { dir := "Guest", srcDir := "guest", roots := #[`Guest] },
  { dir := "GuestTestsLib", srcDir := "guest",
    roots := #[`GuestTests.Main, `GuestTests.Fixture, `GuestTests.Axioms,
               `GuestTests.Deriv, `GuestTests.StdSpecs, `GuestTests.StdAxioms,
               `GuestTests.StdFixture, `GuestTests.EdgeSpecs] },
    -- the ex-GuestStdTests roots joined (the P2 merge: StdSpecs' groups
    -- run under Main's runner; StdFixture is the runtime-imported
    -- fixture the LCNF re-run replays)
    -- `Deriv` mirrors the lakefile root (the effects lane's integration
    -- pins — Main imports it; the packages-check UNGATEDROOT face
    -- enforces the mirror)
  { dir := "ComponentTestsLib", srcDir := "guest",
    roots := #[`ComponentTests.Main, `ComponentTests.Fixture,
               `ComponentTests.Axioms, `ComponentTests.StringFixture,
               `ComponentTests.EdgeFixture, `ComponentTests.FaultFixture,
               `ComponentTests.ImportFixture, `ComponentTests.AsyncFixture,
               `ComponentTests.StreamFixture,
               `ComponentTests.Pipeline, `ComponentTests.Gen,
               `ComponentTests.GenFixture, `ComponentTests.WitFixture] },
    -- the component lane's battery + its fixtures: one lib, one row
  -- Repr: the representation-independence lane (the reviews' §2
  -- discipline — the relation + the preservation construction gate +
  -- the generic client theorem; the zset canonical-rep discipline
  -- generalized). Core-only (imports Kit — the cone rule).
  { dir := "Repr", srcDir := "repr", roots := #[`Repr] },
  { dir := "ReprTestsLib", srcDir := "repr",
    roots := #[`ReprTests.Main, `ReprTests.Axioms] },
  -- ── C3 apps ──
  { dir := "ScaffoldDemo", srcDir := ".",
    roots := #[`DemoApp.Reg, `DemoApp.App, `DemoApp.Flow, `DemoApp.Tests] },
  { dir := "ScaffoldLedger", srcDir := ".",
    roots := #[`LedgerApp.Reg, `LedgerApp.App, `LedgerApp.Flow, `LedgerApp.Tests] },
  -- Faults: the faults lane (the E-code discipline's consumer — 05 §4's
  -- allocation from the persisted registry + 12 §8's declared error
  -- surface). Imports Kit + SchemaCore (READ-ONLY — the cone rule).
  { dir := "Faults", srcDir := "faults", roots := #[`Faults] },
  { dir := "FaultsTestsLib", srcDir := "faults",
    roots := #[`FaultsTests.Main, `FaultsTests.Axioms, `FaultsTests.Reg] }
]

end Gates

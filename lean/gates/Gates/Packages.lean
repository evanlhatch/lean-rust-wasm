/-
# Gates.Packages — the gated package set, as data

One table + the shared per-package env loader, consumed by the axiom
report (Gates.Axioms), the kernel double-check (Gates.KernelCheck), and
any future per-package gate — the `lean-axioms` recipe's package list
lifted out of shell. Same dirs and root modules as the old recipe's
`run` lines (`Tests.Main` included where the package has a test driver;
std/ledger/feature-flags have none — std's gap was recorded then).

`loadPkgEnv` is the ONE import-preamble the loading gates share (the
Axioms/NativePolicy/Audit replay, deduped).

Pure Lean core — the cheapest module in the package.
-/
import Lean

namespace Gates

/-- One gated package: its `lean/` dir + the root modules whose code the
    per-package gates cover. The `Option` fields are the MONOLITH
    overrides (notes/single-lake-migration.md): a package absorbed into
    the root lakefile keeps `dir` as its report-section key, but its
    oleans live in the ROOT package's build dir and its sources stay at
    the old `lean/<dir>` paths (the root's per-lib `srcDir` mounts).
    Defaults preserve the pre-monolith layout. -/
structure PkgSpec where
  dir : String
  roots : Array Lean.Name
  /-- Overrides the olean dir (`../<dir>/.lake/build/lib/lean`),
  relative to the gates package dir. -/
  oleanDir : Option String := none
  /-- Overrides the package source dir (`../<dir>`), used by the
  kernel-check's source scans + lean4lean cwd. -/
  srcDir : Option String := none
  /-- Overrides the package's own LEAN_PATH entry for the lean4lean
  spawn (normally `<srcDir>/.lake/build/lib/lean`; an absorbed package
  has no lakefile to `lake env` against — its oleans sit in the ROOT
  build dir, which carries its whole dep closure). -/
  leanPath : Option String := none

/-- The olean dir a per-package gate reads (pre-monolith default or the
    override). -/
def PkgSpec.oleanDirOf (pkg : PkgSpec) : System.FilePath :=
  match pkg.oleanDir with
  | some d => d
  | none => s!"../{pkg.dir}/.lake/build/lib/lean"

/-- The package source dir (pre-monolith default or the override). -/
def PkgSpec.srcDirOf (pkg : PkgSpec) : System.FilePath :=
  match pkg.srcDir with
  | some d => d
  | none => s!"../{pkg.dir}"

/-- Load one gated package's environment: its olean dir prepended to the
    search path (so its `Tests.Main` wins over same-named dep modules),
    initializers executed, its root modules `importModules`'d at the
    per-package gate trust level. The loading gates (Axioms, NativePolicy,
    Audit) own only their per-package post-processing after this. -/
unsafe def loadPkgEnv (base : Lean.SearchPath) (pkg : PkgSpec) :
    IO (Except String Lean.Environment) := do
  Lean.searchPathRef.set (pkg.oleanDirOf :: base)
  try
    Lean.enableInitializersExecution
    let env ← Lean.importModules (pkg.roots.map ({ module := · })) {}
      (trustLevel := 1024) (loadExts := true)
    return .ok env
  catch e =>
    return .error (toString e)

/-- The gated set. -/
def gatedPackages : Array PkgSpec := #[
  -- ABSORBED (cluster B): LintKit's lakefile is dead; same overrides shape.
  { dir := "LintKit",       roots := #[`LintKit],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/LintKit",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "TextKit",       roots := #[`TextKit, `TextKitTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/TextKit",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "TestKit",       roots := #[`TestKit, `TestKitTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/TestKit",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "Machines",      roots := #[`Machines, `MachinesTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/Machines",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "codegen-core",  roots := #[`CodegenCore, `CodegenCoreTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/codegen-core",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "substrait",     roots := #[`Substrait, `SubstraitTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/substrait",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "qlang",         roots := #[`QLang, `QLangTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/qlang",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "proofkit",      roots := #[`Proofkit, `ProofkitTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/proofkit",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "schema-lang",   roots := #[`SchemaLang, `Demo, `SchemaLangTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/schema-lang",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "faults",        roots := #[`Faults, `Faults.Spec.Demo, `Faults.Spec.Host, `FaultsTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/faults",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "dbsp",          roots := #[`Dbsp, `DbspTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/dbsp",
    leanPath := some "../../.lake/build/lib/lean" },
  -- std gained its Tests (a review fix) after the old
  -- recipe's package list was written; the global report covers them.
  { dir := "std",           roots := #[`GuestlangStd, `GuestlangStdTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/std",
    leanPath := some "../../.lake/build/lib/lean" },
  -- ABSORBED: ledger's lakefile is dead; its modules build
  -- under the root lakefile. `dir` stays the report-section key; the
  -- paths point at the root build (notes/single-lake-migration.md §4).
  { dir := "ledger",        roots := #[`Ledger, `LedgerFn, `LedgerES],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/ledger",
    leanPath := some "../../.lake/build/lib/lean" },
  -- ABSORBED: feature-flags' lakefile is dead; same overrides
  -- shape as ledger above.
  { dir := "feature-flags", roots := #[`FeatureFlags, `FeatureFlagsFn],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/feature-flags",
    leanPath := some "../../.lake/build/lib/lean" },
  { dir := "wasm-backend",  roots := #[`WasmBackend, `DemoFn, `Oracle, `WasmBackendTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/wasm-backend",
    leanPath := some "../../.lake/build/lib/lean" },
  -- ABSORBED (pilot): edgepython's lakefile is dead; its modules build
  -- under the root lakefile (srcDir mounts — notes/single-lake-migration.md).
  -- `dir` stays the report-section key; the paths point at the root build.
  { dir := "edgepython",    roots := #[`EdgePython, `EdgePythonTests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/edgepython",
    leanPath := some "../../.lake/build/lib/lean" },
  -- Self-gating verdict: the gates package is EXEMPT from
  -- the sweeps by role — it is a host-side driver, not a proof
  -- artifact, and its import closure IS the whole tree: loading its
  -- modules in the sweep re-monoliths the memory profile (26.5GB,
  -- OOM-killed on a 29GB box; the sharded per-package runs peak ~2-4GB).
  -- Its decls' cones were verified core-triple-only once at landing
  -- (`gates axioms --package gates`, 331 decls). If the driver ever
  -- grows PROOF obligations, that changes and it re-enters the list.
]

end Gates

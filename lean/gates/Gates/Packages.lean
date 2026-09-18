/-
# Gates.Packages — the gated package set, as data

One table, consumed by the axiom report (Gates.Axioms), the kernel
double-check (Gates.KernelCheck), and any future per-package gate —
the `lean-axioms` recipe's package list lifted out of shell. Mirrors
the old recipe's `run` lines exactly: same dirs, same root modules
(`Tests.Main` included where the package has a test driver; std/ledger/
feature-flags have none — review-2026-09-16 F5 records std's gap).

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

/-- The gated set. -/
def gatedPackages : Array PkgSpec := #[
  { dir := "LintKit",       roots := #[`LintKit] },
  { dir := "TestKit",       roots := #[`TestKit, `Tests.Main] },
  { dir := "Machines",      roots := #[`Machines, `Tests.Main] },
  { dir := "codegen-core",  roots := #[`CodegenCore, `Tests.Main] },
  { dir := "substrait",     roots := #[`Substrait, `Tests.Main] },
  { dir := "qlang",         roots := #[`QLang, `Tests.Main] },
  { dir := "proofkit",      roots := #[`Proofkit, `Tests.Main] },
  { dir := "schema-lang",   roots := #[`SchemaLang, `Demo, `Tests.Main] },
  { dir := "faults",        roots := #[`Faults, `Faults.Spec.Demo, `Faults.Spec.Host, `Tests.Main] },
  { dir := "dbsp",          roots := #[`Dbsp, `Tests.Main] },
  -- std gained its Tests (review-2026-09-16 F5's fix) after the old
  -- recipe's package list was written; the global report covers them.
  { dir := "std",           roots := #[`GuestlangStd, `Tests.Main] },
  { dir := "ledger",        roots := #[`Ledger, `LedgerFn] },
  { dir := "feature-flags", roots := #[`FeatureFlags, `FeatureFlagsFn] },
  { dir := "wasm-backend",  roots := #[`WasmBackend, `DemoFn, `Oracle, `Tests.Main] },
  -- ABSORBED (pilot): edgepython's lakefile is dead; its modules build
  -- under the root lakefile (srcDir mounts — notes/single-lake-migration.md).
  -- `dir` stays the report-section key; the paths point at the root build.
  { dir := "edgepython",    roots := #[`EdgePython, `Tests.Main],
    oleanDir := some "../../.lake/build/lib/lean",
    srcDir := some "../../lean/edgepython",
    leanPath := some "../../.lake/build/lib/lean" },
  -- Self-gating verdict (2026-09-18): the gates package is EXEMPT from
  -- the sweeps by role — it is a host-side driver, not a proof
  -- artifact, and its import closure IS the whole tree: loading its
  -- modules in the sweep re-monoliths the memory profile (26.5GB,
  -- OOM-killed on a 29GB box; the sharded per-package runs peak ~2-4GB).
  -- Its decls' cones were verified core-triple-only once at landing
  -- (`gates axioms --package gates`, 331 decls). If the driver ever
  -- grows PROOF obligations, that changes and it re-enters the list.
]

end Gates

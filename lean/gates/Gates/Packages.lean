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
    per-package gates cover. -/
structure PkgSpec where
  dir : String
  roots : Array Lean.Name

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
  { dir := "edgepython",    roots := #[`EdgePython, `Tests.Main] }
]

end Gates

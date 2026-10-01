/-
Gates.Axioms — the per-library axiom sweep (`gates axioms [--write]`;
mined from legacy/lean/gates/Gates/Axioms.lean, simplified to the fresh
tree's scale).

For each gated package (Gates.Packages), its root modules are
`importModules`'d (oleans built by `lake build` — this gate never
builds), every declaration defined in those modules gets its axiom cone
from the kernel's own `Lean.collectAxioms` (the `#print axioms`
machinery), and the cone is checked against the allowlist by CONSUMING
`LintKit.runLintersOnDecls` with every non-axiom linter disabled (the
allowlist itself — `LintKit.isAllowedAxiom` — lives in
LintKit.AxiomAllowlist and is never re-encoded here). `@[nolint]` and
`set_option` snapshots are honored exactly as in the lint runner (the
same runner code path).

The committed baseline is ONE file (notes/axiom-report.md), one
`## <dir>` section per package; without `--write`, a diff against it IS
the CI gate (a silent axiom-surface change fails).

Re-baseline discipline (the loud re-baseline): `--write` REFUSES a
non-empty diff unless `--accept-drift` is also passed — a re-baseline
must not pre-authorize future taint; it is a deliberate act. Writing an
IN-SYNC report is always allowed (a no-op). Violations and load failures
exit 1 regardless of `--write`.

The two-face shape vs the legacy module's FULL shard fleet: the
LIBRARY rows fold in-process against the one warm env (the legacy
sharding's ~26.5GB peak — libgc's conservative stack scan retaining
each dropped env — is the warm load's gone root); the TESTS-LIB rows
keep the sharded protocol (one child per row, `Gates.testLibPool`) —
the root-`main` collision bars them from the warm env, and their
per-package env loads pay in processes that die.

The five questions (notes/v3/01-core.md):
- root: none — the gate over the tree's axiom surface.
- carrier grade: none — the axiom cone is kernel-collected, not a
presentation crossing.
- spine reading: the interpretation stage (gated envs → decls → cones
→ the committed baseline's diff).
- ladder rung: the ENFORCEMENT of 01 §7's ladder — the allowlist
accepts the core triple + the disclosed native_decide trust base,
nothing else.
- gate row: the axiom-gate row itself (`gates axioms`).
-/
import Lean
import LintKit
import Gates.Baselines
import Gates.Packages
import Gates.Common

open Lean

namespace Gates.Axioms

open Gates (PkgSpec gatedPackages pkgIsTestLib testLibPackages)

structure PkgReport where
  dir : String
  decls : Nat := 0
  /-- The distinct axiom set the package's decls depend on, sorted. -/
  axioms : Array Name := #[]
  violations : Array LintKit.LintFinding := #[]
  loadError : Option String := none

/-- Axiom-only lint config: every non-axiom linter whole-disabled at the
    CLI-override level (the runner skips the pass entirely); the axiom
    allowlist keeps its default-on + per-decl snapshot/nolint semantics. -/
def axiomOnlyConfig : LintKit.DriverConfig :=
  { overrides := ({} : NameMap Bool)
      |>.insert `linter.guestlang.dupDefBodies false
      |>.insert `linter.guestlang.packageNamespace false }

/-- Per-package analysis over its imported environment: the allowlist
    violations (LintKit's runner, unmodified) + the distinct axiom union
    (LintKit.axiomUnion — the kernel's CollectAxioms fold, ONE copy). -/
def analyzeEnv (roots : Array Name) :
    CoreM (Array Name × Array LintKit.LintFinding × Array Name) := do
  let decls ← LintKit.packageDecls (← getEnv) roots
  let findings ← LintKit.runLintersOnDecls decls axiomOnlyConfig
  let axs := (← LintKit.axiomUnion decls).toArray.qsort Name.quickLt
  return (decls, findings, axs)

/-- Import one package's roots via the shared sweep preamble
    (Gates.analyzePkg — the NativePolicy twin's ONE copy) and analyze.
    The package's EXACT roots (no getRoot widening): the fixture-rig
    namespaces' planted violators must stay out of the decl-level
    sweep (the lint driver's lintModulesExact discipline, same reason). -/
unsafe def analyzePkg (base : SearchPath) (pkg : PkgSpec) : IO PkgReport := do
  match ← Gates.analyzePkg "axioms" (·.roots) analyzeEnv base pkg with
  | .inl e => return { dir := pkg.dir, loadError := some e }
  | .inr (decls, findings, axs) =>
    return { dir := pkg.dir, decls := decls.size, axioms := axs, violations := findings }

/-- The committed report this gate diffs against. -/
def reportPath : System.FilePath := "notes/axiom-report.md"

/-- One package's block DATA (the grammar value's face; the line
    spellings are the codec's encode — `Gates.Baselines`). The
    LOAD-FAILED face never enters the grammar layer: a load failure
    sets the gate's failed flag and exits 1 before any baseline is
    trusted (the render covers the CLEAN face only). -/
def blockOf (r : PkgReport) : Gates.Baselines.AxiomBlock :=
  { dir := r.dir, decls := r.decls
    axTail := if r.axioms.isEmpty then "(none — fully constructive)"
              else String.intercalate ", " (r.axioms.map toString).toList
    violTail := if r.violations.isEmpty then "none"
                else toString r.violations.size ++ " (see gate output)" }

/-- One package's result line + violation messages, on STDERR (the
    shard's human face; stdout is the report block). Returns whether it
    failed (load error or allowlist violations). -/
def printReportStderr (r : PkgReport) : IO Bool := do
  match r.loadError with
  | some e =>
      IO.eprintln s!"{r.dir}: LOAD FAILED — {e}"
      return true
  | none =>
      IO.eprintln s!"{r.dir}: {r.decls} decls, axioms [{String.intercalate ", " (r.axioms.map toString).toList}], {r.violations.size} violation(s)"
      for v in r.violations do
        IO.eprintln v.message
      return !r.violations.isEmpty

/-- ONE package's shard (the per-package process — the memory
    discipline: libgc's conservative stack scan retains each dropped
    env, and 37 gated packages folded in one process peaked past the
    OOM line, observed): the report BLOCK on stdout (the parent
    assembles the baseline from the shards' blocks), the human line +
    violations on stderr, exit 1 on violations or a load failure. -/
unsafe def runPkg (pkg : PkgSpec) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  let r ← analyzePkg base pkg
  -- the shard's stdout block: THE GRAMMAR'S DERIVED PRINTER at this
  -- package's block (the parent assembles the baseline from the
  -- shards' blocks; the print's line discipline = the block's bytes).
  -- the shard's stdout block: THE GRAMMAR'S DERIVED PRINTER at this
  -- package's block (the parent assembles the baseline from the
  -- shards' blocks; the print's line discipline = the block's bytes).
  IO.println (Gates.Baselines.printAxiomBlock (blockOf r))
  let failed ← printReportStderr r
  return if failed then 1 else 0

/-- The WARM face, TWO LEGS (the redesign's completed shape): the
    LIBRARY rows fold against the shared warm env (ONE Core state,
    per-package root scopes via `packageDecls`'s prefix filter — the
    axiom cone is per-decl kernel data, so the fold's report is the
    shards' byte for byte), their blocks assembled DIRECTLY from the
    data; the TESTS-LIB rows ride `Gates.testLibPool` (one child shard
    per row — the root-`main` collision bars them from the warm env),
    their stdout blocks re-parsed through the block grammar (the shard
    path's own discipline: the same `printAxiom` canonical render the
    re-parse produces) and merged in `gatedPackages` order. A failed
    shard poisons the run: its block stays OUT (the pre-redesign
    loadError face — the baseline diff fails too), its stderr line
    already streamed live. -/
unsafe def runWarm (write acceptDrift : Bool) (env : Environment) : IO UInt32 := do
  let ctx : Lean.Core.Context := { fileName := "<gates-axioms>", fileMap := default }
  let mut failed := false
  let mut libBlocks : Array (String × Gates.Baselines.AxiomBlock) := #[]
  for pkg in gatedPackages do
    unless pkgIsTestLib pkg do
      -- no per-package load face on the warm leg: the warm env is
      -- all-or-nothing upstream (the loud WARM LOAD FAILED line), the
      -- analysis itself is the fold's total body
      let ((decls, findings, axs), _) ← (analyzeEnv pkg.roots).toIO ctx { env }
      let r : PkgReport :=
        { dir := pkg.dir, decls := decls.size, axioms := axs,
          violations := findings }
      let rowFailed ← printReportStderr r
      failed := failed || rowFailed
      libBlocks := libBlocks.push (pkg.dir, blockOf r)
  let mut shardBlocks : Array (String × Gates.Baselines.AxiomBlock) := #[]
  for (i, code, out) in ← Gates.testLibPool "axioms" do
    let pkg := testLibPackages[i]!
    if code != 0 then
      -- the child's stderr carried the loud line (LOAD FAILED /
      -- violations); the block stays out
      failed := true
    else
      -- the shard's stdout is the block's bytes + `println`'s LF;
      -- the grammar's full-consumption run wants the block exactly
      match TextKit.Grammar.run Gates.Baselines.axiomBlockG
          (out.dropEnd 1).toString with
      | .ok raw =>
          match Gates.Baselines.axBlockClimb raw with
          | some b => shardBlocks := shardBlocks.push (pkg.dir, b)
          | none =>
              IO.eprintln s!"axioms: {pkg.dir}: the shard's block failed the \
                prefix climb (the grammar's hand-edit tooth, at the gate's own pipe)"
              failed := true
      | .error _ =>
          IO.eprintln s!"axioms: {pkg.dir}: the shard's block did not parse \
            (the gate's own pipe carried non-block bytes)"
          failed := true
  let mut blocks : Array Gates.Baselines.AxiomBlock := #[]
  for pkg in gatedPackages do
    let pool := if pkgIsTestLib pkg then shardBlocks else libBlocks
    match pool.find? fun (d, _) => d == pkg.dir with
    | some (_, b) => blocks := blocks.push b
    | none => pure ()
  let text := Gates.Baselines.printAxiom blocks.toList
  Driver.reportGate "axioms" reportPath text write acceptDrift failed
    "axioms: clean — every decl's cone inside the allowlist, report in sync"
    (Driver.diffCheck "axioms" "report" "the axiom surface changed" reportPath text)

/-- `gates axioms [--package=<dir>]` — the warm-server dispatch (the
    shared `Gates.gateDispatch`): without the flag, the WARM fold (the
    tree's env loaded once, every package's axiom sweep in-process);
    with it, ONE package's shard face in-process (the debug face, its
    report block on stdout — the child shape the cache and cold paths
    keep). -/
unsafe def run (write acceptDrift : Bool) (package : Option String) : IO UInt32 :=
  Gates.gateDispatch "axioms" package runPkg
    (Gates.withWarmEnv "axioms" (runWarm write acceptDrift))

end Gates.Axioms

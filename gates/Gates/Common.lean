/-
Gates.Common — the shared registry-replay preamble + the gate-tail
combinators (mined from legacy/lean/gates/Gates/Common.lean's
`Gates.Driver` tails).

`Gates.withPkgEnv`: the single-package env-load prelude (sysroot init +
loadPkgEnv + the LOAD FAILED exit) shared by the gates that load ONE
package environment and hand it to their body. Gates whose load failure
is a report row rather than a gate exit (Axioms' per-package loadError,
DocsCheck's collected loadErrors) keep their own prelude — the combinator
absorbs only the first-failure-exit shape.

`Gates.Driver.reportGate`: the write-or-diff baseline tail shared by the
baseline-report gates. `--write` writes `fresh ++ "\n"` and prints
`wrote <path>` — EXCEPT a non-empty diff (a drifted baseline) is REFUSED
unless `acceptDrift` (a re-baseline must not pre-authorize future taint;
in-sync writes and the absent-file bootstrap stay free); the refusal
names `--write --accept-drift`. Otherwise the committed file is diffed
and the gate's drift/absent line printed. Returns the exit code: 1 on
drift/absent, else 0 after the gate's clean line.

`Gates.poolEngine` + the RSS admission discipline: the kernel-check
leaf pool runs children at bounded parallelism, and the bound is
MEASURED, not guessed — `rssAdmits` projects the pool's peak RSS
(per-lane cost × in-flight + margin) against a budget derived from the
box's own MemAvailable at run time; a pool over budget QUEUES its
tasks (never drops, never OOMs). The pool's ONE remaining consumer is
the genuinely-parallel compute (the kernel-check replays): the
env-consuming rows are the WARM SERVER's in-process folds now
(`Gates.loadWarmEnv` below — one environment per process, never a
per-shard child fleet), and the per-gate child footprint table died
with its last consumer (the old `runAll` admission).

`Gates.loadWarmEnv`: the warm-server discipline's ONE load — every
LIBRARY package's roots imported into ONE environment, once per
process. The env-consuming gate rows fold their library packages
against it as pure Env → Verdict folds; the TESTS-LIB packages
CANNOT ride it (the verified wall: each tests-lib's root modules
define a root-namespace `main` — two `main` constants cannot coexist
in one `importModules`, empirically confirmed) — their shards stay
CHILD PROCESSES (`testLibPool`, the RSS discipline's remaining
tenant, one child per tests-lib per row). The library warm load is
the docs-check OOM's root, removed: one env, loaded once, retained
once — libgc has nothing to misplace. FUTURE OPTION (named, not
taken): namespacing the tests' `main`s (`<Lib>Tests.main` + the
lakefiles' entry overrides) would let the tests-libs ride the warm
env too — the cost is every test exe's entry point plus ~20 lanes'
files in one commit; the shard fleet is the honest shape until
someone pays it.

Deliberate exclusion: the legacy `selectPackages` shard filter — the
fresh tree's `--package=<dir>` flag runs ONE package's shard body
in-process (the debug face); the unflagged face is the warm fold.

The five questions (notes/v3/01-core.md):
- root: none — the baseline-tail combinator (write-or-diff + the loud
re-baseline discipline).
- carrier grade: none — driver machinery over rendered reports.
- spine reading: the artifact stage's check face (committed baseline
vs fresh render).
- ladder rung: n/a.
- gate row: the shared tail of the report gates (the axiom report's
baseline discipline is its first consumer).
-/
import Lean
import Kit.Emit
import Gates.Packages
import SchemaCore.Config
import TextKit.ConfigFormat

namespace Gates

open SchemaCore

/-! ## THE DOGFOOD (C4/N8): the tree's own knobs as the FIRST config schema

The gates' concurrency/budget knobs are a CONFIG: the schema record
below (the SchemaCore.Config discipline), the config FILE as the base
layer (typed + validated at load — the mis-typed value refuses with
the curated CF Diag), the env vars as the OVERRIDE source with the
envNat semantics preserved byte-for-byte (absent/unparsable/zero →
the default — the legacy face never changed), the record's values as
the layer between. `envNat` stays for the env-only knobs (ElabWatch's
floor, the pool's own count) — the dogfood's six ride the face.

-/

/-- The gates' config schema record (the knobs' one schema; the
    fields' names are the env spellings' lower-camel roots). -/
def gatesItem : SchemaCore.Item :=
  { name := "Gates.Knobs"
    fields :=
      [ { name := "all_jobs", ty := .u64 }
      , { name := "kernel_jobs", ty := .u64 }
      , { name := "pool_jobs", ty := .u64 }
      , { name := "rss_budget_mb", ty := .u64 }
      , { name := "rss_margin_mb", ty := .u64 }
      , { name := "kernel_budget_secs", ty := .u64 } ] }

/-- The knobs' check rows: every CONCURRENCY knob is positive (the RSS
    faces are free — `0` means "derive from MemAvailable", the
    legacy semantics). -/
def gatesChecks : List (Pred gatesItem.fields) :=
  [ Pred.u64GtLit "all_jobs" 0
  , Pred.u64GtLit "kernel_jobs" 0
  , Pred.u64GtLit "pool_jobs" 0
  , Pred.u64GtLit "kernel_budget_secs" 0 ]

/-- The knobs' config schema (the record + its validation). -/
def gatesSchema : SchemaCore.ConfigSchema :=
  { item := gatesItem, checks := gatesChecks }

/-- The env var's spelling for a knob (the adapter's ONE mapping). -/
def knobEnvName (name : String) : String := "GATES_" ++ name.toUpper

/-- The typed record's knob read (the file layer's value; `0` = unset
    → the default — the envNat fallback, at the record's face). -/
def typedNat (kr : RowVals gatesItem.fields) (name : String) (dflt : Nat) : Nat :=
  match readNat gatesItem.fields kr name with
  | some n => if n == 0 then dflt else n
  | none => dflt

/-- THE KNOB READ (the pure core): the file layer's value `fileV`
    beneath the env override — the envNat semantics preserved
    byte-for-byte (absent/unparsable/zero env → the default; the file
    layer speaks only when the env layer is ABSENT). -/
def knobOf (fileV : Nat) (env : Option String) (dflt : Nat) : Nat :=
  match env with
  | some v =>
      match v.trimAscii.toString.toNat? with
      | some n => if n == 0 then dflt else n
      | none => dflt
  | none => if fileV == 0 then dflt else fileV

/-- The knobs' load, PURE core: the config text parsed through the
    file grammar (TextKit.ConfigFormat), lowered against the schema
    (the curated CF refusals), the file layer validated by the check
    rows RESTRICTED to the file's own keys (an absent knob carries no
    constraint — the default row is not a violation). -/
def knobsOfText (text : String) :
    Except Kit.Diag (RowVals gatesItem.fields) :=
  match TextKit.ConfigFormat.fileGrammar.run text with
  | .error _ =>
      .error (configDiag SchemaCore.eCF0002
        "the config file does not parse (the format is `key=value` rows)")
  | .ok pairs =>
      match lowerPairs gatesItem.fields pairs with
      | .error d => .error d
      | .ok clauses =>
          match initialRow gatesItem.fields with
          | none => .error (configDiag SchemaCore.eCF0002 "no default row")
          | some base =>
              let rFile := applySources base
                [{ src := ConfigSource.file, overrides := clauses }]
              let keys := pairs.map (·.1)
              let fileChecks : List (Pred gatesItem.fields) :=
                gatesChecks.filter fun p => p.reads.any (· ∈ keys)
              if fileChecks.all (fun p => p.check rFile) then .ok rFile
              else .error (configDiag SchemaCore.eCF0003
                "a knob's value violates the declared checks")

/-- The knobs' config path (`GATES_CONFIG` overrides the default; the
    exe runs from the repo root — the registry's path precedent). -/
def gatesConfigPath : IO System.FilePath := do
  match ← IO.getEnv "GATES_CONFIG" with
  | some p => pure p
  | none => pure "gates/gates.cfg"

/-- The knobs' load (the IO face: the file's text — an ABSENT file is
    NO base layer, the behavior-identical degenerate case). -/
def loadKnobs : IO (Except Kit.Diag (RowVals gatesItem.fields)) := do
  let path ← gatesConfigPath
  let text ← match (← IO.FS.readFile path |>.toBaseIO) with
    | .ok t => pure t
    | .error _ => pure ""
  pure (knobsOfText text)

/-- The knob read, IO face (the dogfood's ONE entry): the loaded
    record beneath the env var. -/
def knobNat (kr : RowVals gatesItem.fields) (name : String) (dflt : Nat) :
    IO Nat := do
  match ← IO.getEnv (knobEnvName name) with
  | some v => pure (knobOf 0 (some v) dflt)
  | none => pure (typedNat kr name dflt)

/-! ## The gates' finding envelope (B1 — the one-envelope discipline, 05 §4)

Every gate failure is a Diag — the ONE envelope (elaboration errors,
parse failures, lint findings, GATE VERDICTS: one code space, one
shape, one rendering). The GT family: registry-allocated in
`notes/code-registry.txt` (the code-registry-check gate's coverage
tooth refuses any hand-strung GT spelling outside it — the tooth now
covers the gates' own messages). One row per FINDING KIND, never per
site; the family grows when a new gate row lands its kinds. -/

/-- The gates' E-codes (the GT family's spellings — live rows of the
persisted registry). -/
def eGT0001 : Kit.ECode := ⟨"GT0001"⟩  -- the regen failed

def eGT0002 : Kit.ECode := ⟨"GT0002"⟩  -- a declared artifact is absent

def eGT0003 : Kit.ECode := ⟨"GT0003"⟩  -- an artifact drifted its regen

def eGT0004 : Kit.ECode := ⟨"GT0004"⟩  -- the gate's own machinery is broken (fail closed)

def eGT0005 : Kit.ECode := ⟨"GT0005"⟩  -- an orphan artifact (no emitter declares it)

def eGT0006 : Kit.ECode := ⟨"GT0006"⟩  -- a declared output is missing on disk

def eGT0007 : Kit.ECode := ⟨"GT0007"⟩  -- a cross-emitter output collision

def eGT0008 : Kit.ECode := ⟨"GT0008"⟩  -- an unclosed lean fence in notes

def eGT0009 : Kit.ECode := ⟨"GT0009"⟩  -- a fence's decl name does not resolve

def eGT0010 : Kit.ECode := ⟨"GT0010"⟩  -- a stale gate-row honesty claim

def eGT0011 : Kit.ECode := ⟨"GT0011"⟩  -- a package env load failed

def eGT0012 : Kit.ECode := ⟨"GT0012"⟩  -- a scan/walk could not complete

def eGT0013 : Kit.ECode := ⟨"GT0013"⟩  -- the lint row's findings-present verdict

/-- THE gate finding's constructor: severity `.gate` (the closed five's
own verdict severity), the code a live GT row, the message curated at
the call site (the context, the construct, the fix). -/
def GateDiag (code : Kit.ECode) (message : String) : Kit.Diag :=
  { code := code, message := message, severity := .gate }

/-- An integer env knob with a default (absent, unparsable, or zero
    falls back — `0` is never a meaningful concurrency/budget value). -/
def envNat (name : String) (dflt : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | some v =>
    match v.trimAscii.toString.toNat? with
    | some n => if n == 0 then pure dflt else pure n
    | none => pure dflt
  | none => pure dflt

/-! ## The RSS-bounded admission discipline (the OOM lesson, made arithmetic) -/

/-- MemAvailable (MB) from /proc/meminfo — the budget's runtime base.
    Fail-closed: an unreadable meminfo yields 8192 MB (a CONSERVATIVE
    guess — the pools then run nearly serial rather than over-committing). -/
def memAvailableMb : IO Nat := do
  match (← IO.FS.readFile "/proc/meminfo" |>.toBaseIO) with
  | .error _ => pure 8192
  | .ok text =>
    let avail : Option Nat :=
      (text.splitOn "\n" |>.filterMap fun l =>
        if l.startsWith "MemAvailable:" then
          (l.splitOn " " |>.filter (· != ""))[1]? |>.bind (·.toNat?)
        else none).head?
    match avail with
    | some kb => pure (kb / 1024)
    | none => pure 8192

/-- The RSS budget (MB): GATES_RSS_BUDGET_MB if set, else 90% of the
    box's MemAvailable at run time. The headroom story is IN THE PER-
    LANE COSTS, not here twice: every per-lane constant is rounded UP
    from its measured peak (2GB vs 1.7, 1.3GB vs 1.2), and the margin
    knob adds the driver's slack — a 90% budget ON TOP of rounded-up
    lanes projects peaks with ≥2.5GB physical free on the 29GB box.
    (The RETUNE lesson, two battery runs: a 70-80% budget ON TOP of
    8-lane pools' 16GB-class footprints SERIALIZED the heavy gates —
    the battery ran 4:34 against the before-run's 2:38. Round-ups +
    fat headroom + big lanes double-margin into false exclusivity.)
    (Measured base, wave-30: 29GB box, ~26GB available fresh →
    ~23.4GB budget.) -/
def rssBudgetMb (kr : RowVals gatesItem.fields) : IO Nat := do
  let v ← knobNat kr "rss_budget_mb" 0
  if v == 0 then (· * 9 / 10) <$> memAvailableMb else pure v

/-- The admission margin (MB): GATES_RSS_MARGIN_MB, default 1024 —
    the slack for a pool's own driver process + measurement error. -/
def rssMarginMb (kr : RowVals gatesItem.fields) : IO Nat :=
  knobNat kr "rss_margin_mb" 1024

/-- The admission predicate: the PROJECTED peak — the in-flight lanes'
    worst concurrent sum + the margin — must stay under the budget.
    The homogeneous pools project `perLaneMb × (live + 1)`; the
    heterogeneous driver (runAll) projects the sum of the live gates'
    footprints + the candidate's. A pool refuses to spawn while it
    fails — the tasks QUEUE, they are never dropped. The first lane is
    always admitted at the call sites (`live.isEmpty` guard): a single
    over-budget lane is the inner-node hazard, handled by exclusivity,
    not by refusal. -/
def rssAdmits (budgetMb marginMb projected : Nat) : Bool :=
  projected + marginMb ≤ budgetMb

/-! ## The warm env (the warm-server discipline's ONE load) -/

/-- THE PARTITION (the adapted warm-server shape's data): the gated
    rows split by the tests' `main` collision — a row whose dir ends
    `TestsLib` carries root modules defining a root-namespace `main`
    (the test exes' entry), and two `main` constants cannot coexist in
    one `importModules` (empirically confirmed). Libraries ride the
    warm env; tests-libs keep the child shards. -/
def pkgIsTestLib (pkg : PkgSpec) : Bool := pkg.dir.endsWith "TestsLib"

/-- The LIBRARY rows: the warm env's packages (verified: the full set
    imports clean in one process). -/
def libPackages : Array PkgSpec :=
  gatedPackages.filter (fun p => !pkgIsTestLib p)

/-- The TESTS-LIB rows: the child shards' packages (the collision's
    honest remainder). -/
def testLibPackages : Array PkgSpec :=
  gatedPackages.filter pkgIsTestLib

/-- THE WARM ENV: every LIBRARY package's roots imported into ONE
    environment, ONCE per process (the roots deduped — a root shared by
    two rows imports once). The env-consuming gate rows fold their
    LIBRARY packages against it as pure Env → Verdict folds. The env
    is PINNED at load: a mid-run edit to the tree's sources or oleans
    is invisible until the next run — the warm face's honest staleness
    note; the gates read the committed-then-built state, and
    `lake build` before the battery is the caller's discipline
    (`just gates` rides `lake exe`, which builds the exe, never the
    gated oleans).

    Verdict equivalence to the shard discipline (the byte-identical
    teeth): every per-package analysis scopes its decls by module
    prefix (`LintKit.packageDecls`) and its env-wide data by the same
    scope (the citation census's `withCensusScope`), so the fold's
    findings over the warm env are exactly the shards' findings over
    their closure envs — a package's shard env contained that package
    + dependencies, and dependencies never cite dependents. -/
unsafe def loadWarmEnv : IO (Except String Lean.Environment) := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  Lean.searchPathRef.set (".lake/build/lib/lean" :: base)
  let mut roots : Array Lean.Name := #[]
  let mut seen : Lean.NameSet := {}
  for pkg in libPackages do
    for r in pkg.roots do
      unless seen.contains r do
        seen := seen.insert r
        roots := roots.push r
  try
    Lean.enableInitializersExecution
    -- `importAll := true`: the gates' whole job is the tree's
    -- INTERNALS — the module system's privacy (the 80/20 conversion)
    -- hides non-public decls from a plain import; the gates are the
    -- same package, so the private scope is theirs by right (the
    -- hidden-declaration blind spot was measured: GatesTestsLib read
    -- as 0 decls under the plain import).
    let env ← Lean.importModules (roots.map ({ module := ·, importAll := true })) {}
      (trustLevel := 1024) (loadExts := true)
    return .ok env
  catch e =>
    return .error (toString e)

/-- The warm load's loud refusal (the ONE shape the env rows share): a
    failed warm load exits 1 with the `just build` hint — an unloadable
    tree verifies nothing (docs-check's honest-partiality rule, at the
    warm face). -/
unsafe def withWarmEnv (gate : String) (k : Lean.Environment → IO UInt32) :
    IO UInt32 := do
  match ← loadWarmEnv with
  | .error e => do
    IO.eprintln <| toString (GateDiag eGT0011
      s!"{gate}: WARM LOAD FAILED — {e} (run `just build` first)")
    return 1
  | .ok env => k env

/-! ## The bounded compute pool (the kernel-check replays' spine) -/

/-- The bounded pool's ENGINE, generalized over the task, the live
    child's state, and the harvested result (pkgPool's loop and
    KernelCheck.sweep's budgeted leaf pool are the same spine): `spawn`
    starts a task's child + its live state; `poll` resolves one live
    child — `.inl s'` keeps it live with new state (the budget-kill
    face), `.inr r` harvests it. The RSS admission + the 50ms rounds
    are HERE, one copy. `tick` runs each round BEFORE admission (the
    sweep's fuel check; the shard pool passes `pure ()`). Results in
    COMPLETION order, paired with the task index — the callers own
    their report order. `partial` (the written reason, the totality
    rule 09 §1): the wait is GENUINELY UNBOUNDED for the shard face —
    no honest fuel exists there; the sweep's total face rides `tick`.
    The allowance row (LintKit.partialAllowance) names this file; the
    ratchet only tightens. -/
partial def poolEngine {T S R : Type} [Inhabited T] {cfg : IO.Process.StdioConfig}
    (tasks : Array T) (spawn : T → IO (IO.Process.Child cfg × S))
    (poll : T → IO.Process.Child cfg → S → IO (Sum S R))
    (jobs perLaneMb budgetMb marginMb : Nat) (tick : IO Unit) :
    IO (Array (Nat × R)) := do
  let mut results : Array (Nat × R) := #[]
  let mut live : Array (Nat × IO.Process.Child cfg × S) := #[]
  let mut next := 0
  while next < tasks.size || !live.isEmpty do
    tick
    while next < tasks.size && live.size < jobs &&
        (live.isEmpty ||
          rssAdmits budgetMb marginMb (perLaneMb * (live.size + 1))) do
      let (child, s) ← spawn tasks[next]!
      live := live.push (next, child, s)
      next := next + 1
    IO.sleep 50
    let mut still : Array (Nat × IO.Process.Child cfg × S) := #[]
    for (i, child, s) in live do
      match ← poll tasks[i]! child s with
      | .inl s' => still := still.push (i, child, s')
      | .inr r => results := results.push (i, r)
    live := still
  return results

/-! ## The tests-lib shard fleet (the warm face's second leg) -/

/-- THE TESTS-LIB LEG (the two-face discipline's second face — the
    redesign's adapted shape for the root-`main` collision): ONE child
    process per tests-lib row — `lake exe gates <gate> --package=<dir>`
    (the per-package in-process face, run as a CHILD: the collision bars
    the tests-libs from the warm env, and seventeen closure envs
    retained in the driver's process is the docs-check OOM's shape —
    the per-package env load is the honest cost, paid in a process that
    DIES). The fleet rides `poolEngine`'s RSS admission (per-lane
    2048MB — the env-replay shard's measured ≤1.7GB peak rounded up,
    the justfile's table), the knobs' `pool_jobs` count cap. Stdout is
    PIPED (the report rows' blocks are the machine face; the verdict
    rows' findings are re-printed by the caller — batched per package,
    the bytes unchanged); stderr inherits (the human face streams
    live). Returns (task index, exit, stdout) in COMPLETION order —
    the callers own their report order (the baselines' section order
    is `gatedPackages`'s). A config-file refusal degrades to the
    env-only knobs (the fleet's bounds are a convenience, never a
    verdict input). -/
unsafe def testLibPool (gate : String) : IO (Array (Nat × UInt32 × String)) := do
  let (jobs, budgetMb, marginMb) ← match ← loadKnobs with
    | .ok kr => pure (← knobNat kr "pool_jobs" 3, ← rssBudgetMb kr,
        ← rssMarginMb kr)
    | .error _ => pure (← envNat "GATES_POOL_JOBS" 3,
        (← memAvailableMb) * 9 / 10, 1024)
  let results ← poolEngine (T := PkgSpec) (S := Unit) (R := UInt32 × String)
    testLibPackages
    (fun pkg => do
      let child ← IO.Process.spawn
        { cmd := "lake", args := #["exe", "gates", gate, s!"--package={pkg.dir}"]
        , stdin := .inherit, stdout := .piped, stderr := .inherit }
      return (child, ()))
    (fun _ child _ => do
      match ← child.tryWait with
      | none => return .inl ()
      | some code => return .inr (code, ← child.stdout.readToEnd))
    jobs 2048 budgetMb marginMb (pure ())
  return results.map fun (i, (code, out)) => (i, code, out)

/-! ## The artifact-walk combinator (the computed artifact gates' face) -/

/-- The declared-artifact walk (the audit / artifact-headers / gen-check
text lanes' ONE copy): for every declared file — the ABSENT check (the
gate-named loud line + the failure) else the committed bytes handed to
`verdict` (true = the file is clean). Returns (present-count,
clean-count, any-failed). The gates keep their own verdict fns; the
walk owns the skeleton. -/
def forDeclared (gate absentWhy : String) (files : List Kit.Emit.GeneratedFile)
    (verdict : Kit.Emit.GeneratedFile → String → IO Bool) :
    IO (Nat × Nat × Bool) := do
  let mut present := 0
  let mut clean := 0
  let mut failed := false
  for f in files do
    let path : System.FilePath := f.path
    unless ← path.pathExists do
      IO.eprintln <| toString (GateDiag eGT0002
        s!"{gate}: {f.path} ABSENT — {absentWhy}")
      failed := true
      continue
    present := present + 1
    let committed ← IO.FS.readFile path
    if ← verdict f committed then clean := clean + 1
    else failed := true
  return (present, clean, failed)

/-- The binary lane's walk (forDeclared's ByteArray face — gen-check's
    `.wasm`/`.hdr` lanes): the ABSENT check else the committed bytes
    handed to `verdict`. Same return shape as `forDeclared`. -/
def forDeclaredBin (gate absentWhy : String) (files : List Kit.Emit.BinaryFile)
    (verdict : Kit.Emit.BinaryFile → ByteArray → IO Bool) :
    IO (Nat × Nat × Bool) := do
  let mut present := 0
  let mut clean := 0
  let mut failed := false
  for f in files do
    let path : System.FilePath := f.path
    unless ← path.pathExists do
      IO.eprintln <| toString (GateDiag eGT0002
        s!"{gate}: {f.path} ABSENT — {absentWhy}")
      failed := true
      continue
    present := present + 1
    let committed ← IO.FS.readBinFile path
    if ← verdict f committed then clean := clean + 1
    else failed := true
  return (present, clean, failed)

/-- The per-package sweep preamble (Axioms/NativePolicy's twin): load
the package's env, on failure the LOUD loadError payload; on success
run the CoreM analysis over the caller's roots. `label` names the
replay in the Core context (the failure face keeps its gate's name). -/
unsafe def analyzePkg (label : String) (getRoots : PkgSpec → Array Name)
    (analyze : Array Name → Lean.CoreM α) (base : Lean.SearchPath) (pkg : PkgSpec) :
    IO (Sum String α) := do
  match ← loadPkgEnv base pkg with
  | .error e => return .inl e
  | .ok env =>
    let ctx : Lean.Core.Context := { fileName := s!"<gates-{label}>", fileMap := default }
    let (res, _) ← (analyze (getRoots pkg)).toIO ctx { env := env }
    return .inr res

/-- The gate rows' dispatch spine (the warm-server topology's ONE
copy): `--package=<dir>` runs ONE package's shard face in-process (the
debug face — one env, no fleet); without the flag, the WARM face —
the tree's environment loaded once (`withWarmEnv`), the fold over
every gated package. The old `shardDispatch`'s pooled child fleet is
gone; the two faces are verdict-equivalent by the scoping discipline
(`loadWarmEnv`'s header). -/
unsafe def gateDispatch (gate : String) (package : Option String)
    (shard : PkgSpec → IO UInt32) (warm : IO UInt32) : IO UInt32 := do
  match package with
  | some dir =>
      match gatedPackages.toList.find? fun p => p.dir == dir with
      | none =>
          IO.eprintln s!"{gate}: --package={dir} names no Gates.Packages row"
          return 1
      | some pkg => shard pkg
  | none => warm

/-- The single-package env-load prelude: init the search path from the
    sysroot, `loadPkgEnv`, and on failure print the gate-named LOAD
    FAILED line to stderr and exit 1; on success hand the environment to
    `k`. (Unsafe: `loadPkgEnv` runs initializers.) Deliberately NOT for
    the gates that fold several packages with per-package load-error
    rows — Axioms/DocsCheck keep their own prelude (the honest-partiality
    rule: absorb only the sites that fit). -/
unsafe def withPkgEnv (gate : String) (pkg : PkgSpec)
    (k : Lean.Environment → IO UInt32) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  match ← loadPkgEnv base pkg with
  | .error e => do
    IO.eprintln <| toString (GateDiag eGT0011
      s!"{gate}: LOAD FAILED — {e}")
    return 1
  | .ok env => k env

namespace Driver

/-- Verdict of comparing the fresh render against the committed
    baseline (the on-disk contract is `render ++ "\n"` — the final
    newline is the file's, not the render's). -/
inductive Baseline where
  | inSync | drifted | absent

def diffBaseline (path : System.FilePath) (fresh : String) : IO Baseline := do
  unless ← path.pathExists do return .absent
  let committed ← IO.FS.readFile path
  return if committed == fresh ++ "\n" then .inSync else .drifted

/-- The write-or-diff baseline tail shared by the baseline-report gates.
    Without `--write` the gate's own failure face is `check` (IO Bool —
    true = failed): the baseline-diff gates pass `Driver.diffCheck`'s
    shape, a gate with live findings passes its printer (ElabWatch's
    hand write-tail is gone). -/
def reportGate (gate : String) (baseline : System.FilePath)
    (fresh : String) (write acceptDrift failed : Bool) (cleanMsg : String)
    (check : IO Bool) : IO UInt32 := do
  let mut failed := failed
  if write then
    match ← diffBaseline baseline fresh with
    | .drifted =>
      unless acceptDrift do
        IO.println s!"{gate}: --write REFUSED — non-empty diff against {baseline} \
          (a re-baseline is a deliberate act; review the diff, then rerun with --write --accept-drift)"
        return 1
      IO.FS.writeFile baseline (fresh ++ "\n")
      IO.println s!"wrote {baseline} (re-baseline accepted)"
    | _ =>
      IO.FS.writeFile baseline (fresh ++ "\n")
      IO.println s!"wrote {baseline}"
  else
    if ← check then failed := true
  if failed then return 1
  IO.println cleanMsg
  return 0

/-- The baseline-diff gates' no-write face (reportGate's `check` for
    the gates whose only findings ARE the baseline diff): the committed
    file's drift/absent lines. `what` names the artifact ("report" /
    "matrix"), `why` is the gate's reason fragment. -/
def diffCheck (gate what why : String) (baseline : System.FilePath)
    (fresh : String) : IO Bool := do
  match ← diffBaseline baseline fresh with
  | .inSync => return false
  | .drifted =>
    IO.println s!"{gate}: {what} DRIFTED from {baseline} — {why}; \
      run `lake exe gates {gate} --write` and commit"
    return true
  | .absent =>
    IO.println s!"{gate}: {baseline} absent — run `lake exe gates {gate} --write` and commit"
    return true

/-- The write-or-diff core of the byte-tie gates whose committed file IS
    the artifact (SnapshotCheck, CodeRegistryCheck): an exact-bytes
    compare — unlike `reportGate`, no `fresh ++ "\\n"` newline convention
    and no accept-drift gate, because the `--write` here re-renders the
    SAME data (there is no rendered-report baseline being re-baselined).
    In sync: optionally announce the in-sync write (`inSyncWrite`; an
    in-sync write is free) then the clean line, exit 0. Drifted: with
    `--write` the deliberate, commit-visible re-render (`driftWriteMsg`,
    then the clean line too when `cleanAfterWrite` — CodeRegistryCheck
    canonicalizes and still reports clean, SnapshotCheck's re-baseline
    ends at the write line), exit 0; without, `driftMsg`, exit 1. The
    callers keep their pre-tie teeth (SnapshotCheck's parse refusal, the
    absent-file bootstraps) — they do not fit the core. -/
def byteTieGate (committed fresh : String) (write : Bool)
    (writeFile : String → IO Unit) (inSyncWrite : Option String)
    (driftWriteMsg : String) (cleanAfterWrite : Bool)
    (cleanMsg : String) (driftMsg : String) : IO UInt32 := do
  if committed == fresh then
    if write then
      if let some m := inSyncWrite then IO.println m
    IO.println cleanMsg
    return 0
  if write then
    writeFile fresh
    IO.println driftWriteMsg
    if cleanAfterWrite then IO.println cleanMsg
    return 0
  IO.println driftMsg
  return 1

end Driver

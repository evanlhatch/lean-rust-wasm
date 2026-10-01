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

`Gates.pkgPool` + the RSS admission discipline: the shard pools run
children at bounded parallelism, and the bound is MEASURED, not guessed —
`rssAdmits` projects the pool's peak RSS (per-lane cost × in-flight +
margin) against a budget derived from the box's own MemAvailable at run
time; a pool over budget QUEUES its tasks (never drops, never OOMs).
The measured per-lane costs live with their consumers (Common's shard
constant, KernelCheck's leaf constant, Gates' per-gate footprint table).

Deliberate exclusion: the legacy `selectPackages` shard filter — the
fresh tree's gates have no `--package` sharding yet (one environment per
gate run; the shard/child machinery arrives with the first gated package
heavy enough to need it — the legacy lesson: peak RSS).

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

/-- The MEASURED per-shard RSS cost of the env-replay shard children
    (the pkgPool lanes): peak RSS over every gated package's
    `--package=<dir>` shard, wave-30 (Kit 1.63GB, WasmCore 1.64GB,
    Guest 1.65GB, SchemaCore 1.66GB, Machines 1.62GB, ZSet 0.52GB —
    rounded up to 2GB). The env-load is the cost: a shard replays the
    full dependency closure. -/
def shardCostMb : Nat := 2048

/-! ## The bounded package pool (the shard-replay speedup) -/

/-- The pooled child's shape: stdout piped (the shard's block), the
    human faces inherited (they stream live, interleaved). -/
abbrev PkgChild :=
  IO.Process.Child { stdin := .inherit, stdout := .piped, stderr := .inherit :
    IO.Process.StdioConfig }

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

/-- The bounded package pool: each package's child process (the shard
dispatch — the per-package env load is the memory discipline, KEPT)
runs at `jobs`-way concurrency (GATES_POOL_JOBS, default 3 —
the retune lesson: 8 lanes made a gate's worst-case footprint
16GB-class and the heavy gates could not co-run; 3 lanes × 2GB =
6.2GB per gate lets BOTH shard pools + the kernel leaf pool share
the budget, the full battery overlapped)
AND under the RSS admission predicate — a spawn
happens only while the projected peak (shardCostMb × (live + 1) +
the margin) stays under `budgetMb`; over budget the shards QUEUE
(never dropped, never OOM). `mkCmd` is the child executable (the
teeth spawn `sleep` — a synthetic over-budget case must queue, not
fail). The (exit, stdout-block) pairs return in the INPUT order —
the deterministic report's order — whatever the completion order.
`partial` (the written reason, the totality rule 09 §1): the loop is
a GENUINELY UNBOUNDED wait — the RSS budget bounds ADMISSION, not
completion; there is NO per-child wall-clock budget (a hung shard
child hangs the pool: queueing, never dropping, never killing), so
no honest fuel exists. The allowance row (LintKit.partialAllowance)
names the ENGINE — the adapter is a total fold over its results (one
`partial def` per file; the ratchet only tightens). The engine is
`poolEngine`'s — KernelCheck's budgeted leaf pool rides the same
spine. -/
def pkgPool (mkCmd : PkgSpec → String) (mkArgs : PkgSpec → Array String)
    (pkgs : Array PkgSpec) (jobs perLaneMb budgetMb marginMb : Nat) :
    IO (Array (UInt32 × String)) := do
  let outs ← poolEngine (T := PkgSpec) (S := Unit) (R := UInt32 × String)
    pkgs
    (fun pkg => do
      let child : PkgChild ← IO.Process.spawn
        { cmd := mkCmd pkg, args := mkArgs pkg
        , stdin := .inherit, stdout := .piped, stderr := .inherit }
      pure (child, ()))
    (fun _ child _ => do
      match ← child.tryWait with
      | some code => return .inr (code, ← child.stdout.readToEnd)
      | none => return .inl ())
    jobs perLaneMb budgetMb marginMb (pure ())
  -- the INPUT order (the deterministic report's order — whatever the
  -- completion order the engine harvested in)
  let mut results : Array (UInt32 × String) :=
    Array.replicate pkgs.size (0, "")
  for (i, r) in outs do
    results := results.set! i r
  return results

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

/-- The sharded gate dispatch (Axioms/NativePolicy's twin): with
`--package=<dir>`, ONE package's shard body (the child's own face);
without, one child process per gated package at the pooled
concurrency + the RSS admission (the same memory discipline as
`pkgPool`), the (exit, stdout) pairs handed to the caller's fold. -/
unsafe def shardDispatch (gate : String) (package : Option String)
    (shard : PkgSpec → IO UInt32) (fold : Array (UInt32 × String) → IO UInt32) :
    IO UInt32 := do
  match package with
  | some dir =>
      match gatedPackages.toList.find? fun p => p.dir == dir with
      | none =>
          IO.eprintln s!"{gate}: --package={dir} names no Gates.Packages row"
          return 1
      | some pkg => shard pkg
  | none =>
      -- the pool's knobs ride the config face too (the loud CF exit on
      -- a mis-typed config file)
      let kr ← match ← loadKnobs with
        | .ok kr => pure kr
        | .error d => IO.eprintln (Kit.Diag.toString d); return 1
      let jobs ← knobNat kr "pool_jobs" 3
      let budgetMb ← rssBudgetMb kr
      let marginMb ← rssMarginMb kr
      let outs ← pkgPool (fun _ => "lake")
        (fun pkg => #["exe", "gates", gate, s!"--package={pkg.dir}"])
        gatedPackages jobs shardCostMb budgetMb marginMb
      fold outs

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

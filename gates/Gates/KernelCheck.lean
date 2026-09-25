/-
Gates.KernelCheck — the lean4lean double-check
(`gates kernel-check`; mined from
legacy/lean/gates/Gates/KernelCheck.lean, ported fresh at the fresh
tree's layout: ONE lake package, all libraries' oleans in the root
build dir).

Replays every gated module's own declarations through lean4lean
(github.com/digama0/lean4lean — a Lean 4 kernel written in pure Lean 4;
the tree's pinned rev, notes/v3/09-gates-ops.md §3's kernel-check row).
NON-fresh mode: imported decls are trusted (Cli is NOT re-checked) and
only the target modules' own declarations are kernel-checked.

The caveats this gate ships with (read before trusting a green run):

(a) reduceBool GAP: lean4lean does NOT support `reduceBool`, the kernel
    extension `native_decide`'s trust base reduces through. A proof that
    NEEDS the reduction is expected to fail or be silently accepted here
    (observed on this tree: a planted `by native_decide` theorem replays
    clean — the minted axiom is trusted, the danger invisible); the
    native-policy gate owns the trust base's enforcement (disclosure +
    the allowlist ratchet). The known-gap list lives in
    `knownGaps` — additive only when a NEW disclosed
    native_decide use lands. (b) SHARED LINEAGE: lean4lean shares design
    lineage with the C++ kernel (same author circle, same algorithmic
    shape). A green run is a bug-catching DOUBLE-CHECK, not independence
    from the C++ kernel's failure modes. (c) THE PIN: lean4lean master @
    the pinned rev builds under the v4.33.0 RELEASE toolchain with
    batteries v4.33.0 (the root lakefile's batteries require overrides
    lean4lean's own rc2 pin; probe-verified in the legacy tree,
    re-verified on this tree's landing). (d) BLIND SPOTS — what a green
    run does NOT prove: 1. `example`s — they create no constants, so NO
    env-based sweep sees them (a sorry inside an `example` is caught
    only by the build's warning). 2. structure-field defaults —
    elaborated at declaration time, never replayed as standalone
    constants. 3. anything OUTSIDE the root build dir's modules (the
    sweep covers the gated set; gates itself is exempt by role). Pair
    this gate with the other lanes; a green kernel sweep means exactly
    the checked surface, never more.

Mechanics (the wave-29 rewrite — the batch mode's removal is the
recorded root cause):

* WHY THE OLD BATCH MODE HUNG: lean4lean's CLI expands every module
  argument by PREFIX (`target.isPrefixOf m`) and replays each matched
  module as a CONCURRENT task (`IO.asTask`) in ONE process. The batch
  passed all ~300 module names at once → ~300 concurrent kernel
  replays → peak RSS 20GB+ (measured), systemd-oomd SIGTERMs the
  process mid-run → no verdict, no output, minutes of crawl: the
  reported hang. One invocation PER MODULE from the start — the
  prefix expansion makes an inner-node arg (e.g. `SchemaCore`) replay
  its whole subtree concurrently, so inner nodes run EXCLUSIVELY
  (one at a time; measured peak 24GB for SchemaCore alone) while the
  leaves — the overwhelming majority — run in a small worker pool
  (measured: ≤2GB each, 1-2s each).
* THE BUDGET DISCIPLINE (the honest trichotomy): each invocation has a
  wall-clock budget (GATES_KERNEL_BUDGET_SECS, default 300). A module
  exceeding it (or dying by signal — oomd included) is an UNKNOWN:
  reported by name, never a hang, never a silent skip. A budget kill
  is NOT a kernel verdict; the gate exits 0 on UNKNOWN but prints the
  loud coverage line so the number of unchecked modules is always
  visible.
* STALE OLEANS: an olean whose source is gone (a deleted module's
  build residue) is DELETED with a loud report before the sweep. The
  residue poisons the prefix expansion — an inner arg replays its
  stale descendants too, and a stale module's decls fail with a FALSE
  rejection (observed: `ZSet.Weighted.olean` left by the ZSet split,
  failing every `ZSet` replay with `unknown constant 'ZSet.ZSet.rep'`).
* (wave-30, the RSS ceiling, measured on the 29GB box): the leaf
  pool's lane count is RSS-BOUNDED, not just counted — `rssAdmits`
  projects leafCostMb × (live + 1) + the margin against the
  MemAvailable-derived budget before every spawn; over budget the
  leaves QUEUE. The knobs: GATES_KERNEL_JOBS (default 6 — the count
  cap; 6 × the 1.3GB leaf keeps the leaf phase co-runnable beside
  BOTH shard pools under the 90% budget — the inner nodes, not the
  lanes, bound this gate's wall), GATES_RSS_BUDGET_MB /
  GATES_RSS_MARGIN_MB (the budget's faces).
* The lean4lean exe builds on demand (`lake build lean4lean:exe` —
  the package's exe facet: its ONLY exe target) into
  `.lake/packages/lean4lean/.lake/build/bin/`.
* Modules are enumerated from the root `.lake/build/lib/lean`
  (`*.olean`, exact suffix — the module system also writes
  `.olean.private`/`.olean.server` parts). A module is OURS iff its
  source sits in the tree (checked across the srcDirs). A module whose
  source declares nothing (column-0 scan, fail-closed) is skipped with
  the precondition verified. An EMPTY build dir errors (a skipped sweep
  is NOT a checked sweep).

Pure Lean core + Gates.Packages + Gates.Common (the env knob).
-/
import Lean
import Gates.Common
import Gates.Packages

open Lean

namespace Gates.KernelCheck

/-- Modules whose expected lean4lean failure is a DISCLOSED gap —
    each entry names its module + the class: the reduceBool gap
    (lean4lean does not support it) or the replay-budget timeout
    (the giant golden theorems' full-bytes rfl reductions exceed the
    replay budget; the real kernel accepts them at build).
    (caveat (a)): the tree's disclosed native_decide sites. The
    native-policy gate owns their enforcement; a failure HERE for any
    OTHER module is a real finding. -/
def knownGaps : List (String × Name) :=
  [("replay-budget", `SchemaCore.Goldens)]

/-- The tree's srcDirs — DERIVED from Gates.Packages' table (the single
    source; the hand-copied list this replaces had drifted: the newest
    lanes' modules were skipped silently as "not ours"). A module is
    OURS iff its source file exists under one of the table's srcDirs. -/
def srcDirs : Array System.FilePath := Id.run do
  let dirs : List System.FilePath :=
    Gates.gatedPackages.toList.map (·.srcDir)
  -- dedup, order-preserving (the cone order)
  let mut acc : List System.FilePath := []
  for d in dirs do
    if !(acc.contains d) then acc := d :: acc
  acc.reverse.toArray

/-- The lean4lean exe, built on demand (only the exe target — its
    Theory/Verify libs are lean4lean's own proof lane, not the
    checker's runtime). -/
def ensureExe : IO System.FilePath := do
  let exe : System.FilePath := ".lake/packages/lean4lean/.lake/build/bin/lean4lean"
  unless ← exe.pathExists do
    IO.println "kernel-check: building the lean4lean exe (one-time; only the exe target)"
    let out ← IO.Process.output { cmd := "lake", args := #["build", "lean4lean:exe"] }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"kernel-check: `lake build lean4lean:exe` failed:\n{out.stdout}\n{out.stderr}"
  return exe

/-- Recursive olean walk (filesystem depth — `partial`, termination is
    the dir tree's finiteness, not a structural measure). -/
partial def walkOleans (dir : System.FilePath) (acc : Array System.FilePath) :
    IO (Array System.FilePath) := do
  let mut acc := acc
  for e in ← dir.readDir do
    if ← e.path.isDir then
      acc ← walkOleans e.path acc
    else if e.path.extension == some "olean" then
      acc := acc.push e.path
  return acc

/-- All (module, olean path) pairs of the root build dir (`Foo/Bar.olean`
    → `Foo.Bar`; `.olean.private`/`.olean.server`/`.ir`/`.ilean`
    siblings excluded by the exact-suffix test). -/
def modulesWithPaths (libDir : System.FilePath) :
    IO (Array (Name × System.FilePath)) := do
  let files ← walkOleans libDir #[]
  let pre := libDir.toString ++ "/"
  return files.map fun p =>
    let rel := match p.toString.dropPrefix? pre with
      | some r => r.toString | none => p.toString
    let stem := match rel.dropSuffix? ".olean" with
      | some s => s.toString | none => rel
    (String.intercalate "." (stem.splitOn "/") |>.toName, p)

/-- Column-0 declaration openers. An import-only root aggregate is
    `module` + `import` lines only — none of these at column 0. -/
def declOpeners : Array String := #[
  "@[", "def ", "theorem ", "instance", "abbrev ", "inductive ",
  "structure ", "class ", "opaque ", "axiom ", "example", "initialize",
  "macro ", "syntax ", "elab ", "export ", "noncomputable", "unsafe "]

/-- Does a source file declare anything? Fail-closed: any column-0
    declaration opener (even inside a comment — the tree's headers never
    put one there) counts as declarations, and then the module is
    CHECKED, not skipped. -/
def sourceHasDecls (path : System.FilePath) : IO Bool := do
  let text ← IO.FS.readFile path
  return text.splitOn "\n" |>.any fun l =>
    !l.isEmpty && !l.startsWith " " && !l.startsWith "\t" &&
      declOpeners.any (l.startsWith ·)

/-- The module's source path if it is OURS (a source file exists under
    one of the tree's srcDirs), else none. -/
def ourSource (m : Name) : IO (Option System.FilePath) := do
  for d in srcDirs do
    let p := modToFilePath d m "lean"
    if ← p.pathExists then return some p
  return none

/-! ## The per-module sweep -/

/-- The MEASURED per-leaf RSS cost (wave-30, peak RSS per lean4lean
    leaf invocation, /usr/bin/time over the heaviest leaves:
    GuestTests.Main 1.20GB, Guest.Lower 1.19GB, SchemaCore.EntityMachine
    1.19GB, KitTests.Main 1.19GB; the light faces 0.4-1.2GB; the leaf
    wall time 0.4-1.6s) — 1.3GB. The RSS admission's per-lane cost.
    The INNER nodes are the hazard this does NOT bound (SchemaCore's
    subtree replay alone peaks ~24GB — inherent to lean4lean's
    concurrent prefix expansion): they run EXCLUSIVELY, one at a time,
    after the leaves. -/
def leafCostMb : Nat := 1300

/-- One module's replay verdict. `ok`/`gap` are kernel verdicts;
    `rejected` is a kernel verdict OUTSIDE the disclosed gaps (the gate
    fails); `unknown` is NO kernel verdict (budget kill or signal —
    the gate passes with the loud coverage report, never hangs). -/
inductive Verdict where
  | ok | gap | rejected (msg : String) | unknown (why : String)

/-- The verdict's render — the word plus its evidence tail (the linter's
    compliant shape: a verdict renderer, `Impact.Verdict.render`'s
    precedent). -/
def Verdict.render : Verdict → String
  | .ok => "ok"
  | .gap => "GAP (disclosed)"
  | .rejected msg => s!"REJECTED\n{msg}"
  | .unknown why => s!"UNKNOWN ({why})"

/-- One completed module. -/
structure RunResult where
  mod : Name
  verdict : Verdict
  ms : Nat

/-- The piped child shape the sweep spawns (stdin nulled — lean4lean
    reads no input; stdout/stderr piped for the rejection message). -/
abbrev KChild :=
  IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped :
    IO.Process.StdioConfig }

/-- The sweep's one spawn (the typed face of `IO.Process.spawn` — the
    child type is the args' `toStdioConfig`, pinned to `KChild`). -/
def spawnK (absExe leanPath : String) (m : Name) : IO KChild := do
  let a : IO.Process.SpawnArgs :=
    { cmd := absExe, args := #[m.toString]
    , env := #[("LEAN_PATH", some leanPath)]
    , stdin := .null, stdout := .piped, stderr := .piped }
  IO.Process.spawn a

/-- The verdict from an exit code + captured output. -/
def classify (m : Name) (code : UInt32) (budgeted : Bool) (budgetMs : Nat)
    (out : String) : Verdict :=
  if code == 0 then .ok
  else if budgeted then
    .unknown s!"budget {budgetMs}s exceeded — killed (no kernel verdict)"
  else if code >= 128 then
    .unknown s!"signal exit {code} (no kernel verdict — oomd/kill, NOT a rejection)"
  else if out.contains "found a problem" then
    if knownGaps.any fun (_, gm) => gm == m then .gap
    else .rejected <|
      (out.splitOn "\n" |>.reverse.take 6 |>.reverse) |> String.intercalate "\n"
  else .unknown s!"exit {code}"

/-- Read a finished child's captured streams. -/
def readOut (child : KChild) : IO String := do
  let o ← child.stdout.readToEnd
  let e ← child.stderr.readToEnd
  return o ++ "\n" ++ e

/-- The worker pool: `mods` replayed at `jobs`-way concurrency, one
    invocation PER MODULE (the batch mode's ~300-concurrent-tasks
    process is the recorded hang — never again), each invocation under
    the wall-clock budget AND the RSS admission (perLaneMb × (live + 1)
    + the margin ≤ the budget — over budget the leaves QUEUE, never
    OOM). A progress line prints as each module lands (the driver
    never goes silent). `idx0`/`total` keep the progress counter
    continuous across the sweep's phases.
    TOTAL (the totality rule's explicit-bound face, 09 §1 — not
    `partial`): the poll loop's fuel is the sweep's OWN budget
    discipline made explicit. Every child resolves within
    ⌈budgetMs/50⌉ + 2 poll rounds of its spawn (the budget kill fires
    the round after the deadline; the reaped kill lands the round
    after that), and each round is ≥50ms of sleep, so
    `(mods.size + 1) × (budgetMs/50 + 3)` rounds bound the whole
    sweep. Exhaustion is NOT a skip and NOT a hang: the loud error
    says the bound's reasoning failed — the gate fails named (the
    budget discipline's answer is never an unbounded loop when a
    budget exists). -/
def sweep (absExe leanPath : String) (mods : Array Name)
    (jobs budgetMs idx0 total perLaneMb budgetMb marginMb : Nat) :
    IO (Array RunResult) := do
  -- the poll fuel (TOTAL, the totality rule's explicit-bound face, 09
  -- §1 — the engine's tick runs it each round): every child resolves
  -- within ⌈budgetMs/50⌉ + 2 poll rounds of its spawn (the budget kill
  -- fires the round after the deadline; the reaped kill lands the round
  -- after that), and each round is ≥50ms of sleep, so
  -- `(mods.size + 1) × (budgetMs/50 + 3)` rounds bound the whole
  -- sweep. Exhaustion is NOT a skip and NOT a hang: the loud error
  -- says the bound's reasoning failed — the gate fails named.
  let fuel ← IO.mkRef ((mods.size + 1) * (budgetMs / 50 + 3))
  let doneRef ← IO.mkRef 0
  -- the bounded leaf pool IS Gates.poolEngine (the shard pools' spine):
  -- one invocation PER MODULE (the batch mode's ~300-concurrent-tasks
  -- process is the recorded hang — never again), each under the
  -- wall-clock budget AND the RSS admission; the live state is the
  -- (start-ms, budget-killed?) pair the budget-kill face updates.
  let outs ← Gates.poolEngine (T := Name) (S := Nat × Bool) (R := RunResult)
    mods
    (fun m => do
      let child ← spawnK absExe leanPath m
      return (child, (← IO.monoMsNow, false)))
    (fun m child s => do
      match ← child.tryWait with
      | some code =>
        let (t0, wasKilled) := s
        let ms := (← IO.monoMsNow) - t0
        let out ← readOut child
        let v := classify m code wasKilled budgetMs out
        let done ← doneRef.get
        doneRef.set (done + 1)
        IO.println s!"kernel-check: [{idx0 + done}/{total}] {m} \
          — {ms / 1000}.{ms % 1000 / 100}s {Verdict.render v}"
        return .inr { mod := m, verdict := v, ms := ms }
      | none =>
        let (t0, wasKilled) := s
        let now ← IO.monoMsNow
        if now > t0 + budgetMs then
          child.kill  -- reaped on a later poll, classified budgeted
          return .inl (t0, true)
        else
          return .inl (t0, wasKilled))
    jobs perLaneMb budgetMb marginMb do
      let f ← fuel.get
      if f = 0 then
        throw <| IO.userError "kernel-check: POLL FUEL EXHAUSTED — the poll-round \
          bound ((modules + 1) × (budget/50 + 3)) proved insufficient; the bound's \
          reasoning failed (a child outlived its budget-kill + reap by more than \
          two poll rounds). The sweep refuses named — never a hang, never a silent skip."
      fuel.set (f - 1)
  return outs.map (·.2)

/-! ## The gate -/

/-- `gates kernel-check` — replay every gated module through the
    pure-Lean kernel. Exit 0 iff no module was REJECTED outside the
    disclosed gaps (an UNKNOWN is the budget discipline's honest
    skip-with-report: it is named in the report, never a hang). -/
unsafe def run : IO UInt32 := do
  let mut failures : Array (Name × String) := #[]
  let mut unknowns : Array (Name × String) := #[]
  let mut gaps : Array Name := #[]
  let mut skipped : Array Name := #[]
  let mut stale : Array Name := #[]
  let mut checked : Nat := 0
  try
    let exe ← ensureExe
    let libDir : System.FilePath := ".lake/build/lib/lean"
    unless ← libDir.pathExists do
      throw <| IO.userError "no oleans at .lake/build/lib/lean — run `just build` first"
    let rootOut ← IO.Process.output
      { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"] }
    unless rootOut.exitCode == 0 do
      throw <| IO.userError s!"`lake env printenv LEAN_PATH` failed:\n{rootOut.stderr}"
    let leanPath := s!"{libDir}:{rootOut.stdout.trimAscii}"
    let budgetMs := (← Gates.envNat "GATES_KERNEL_BUDGET_SECS" 300) * 1000
    let jobs ← Gates.envNat "GATES_KERNEL_JOBS" 6
    let budgetMb ← Gates.rssBudgetMb
    let marginMb ← Gates.rssMarginMb
    -- partition: ours-with-declarations are checked; stale oleans are
    -- deleted with a report; declaration-free sources are skipped
    let mut checkMods : Array Name := #[]
    for (m, path) in ← modulesWithPaths libDir do
      match ← ourSource m with
      | none =>
        -- a build residue: the source is gone but the olean remains.
        -- DELETED (build output, not committed state): the residue
        -- poisons the prefix expansion — an inner arg replays its
        -- stale descendants too, and the stale decls fail with a
        -- FALSE rejection (the ZSet.Weighted lesson).
        stale := stale.push m
        try IO.FS.removeFile path catch _ => pure ()
      | some src =>
        if !(← sourceHasDecls src) then
          skipped := skipped.push m
        else
          checkMods := checkMods.push m
    if checkMods.isEmpty then
      throw <| IO.userError "no gated modules found — the sweep checked nothing"
    -- inner nodes (a proper prefix of another checked module): their
    -- arg replays the whole SUBTREE as concurrent tasks inside one
    -- process (lean4lean's prefix expansion) — the memory hog
    -- (measured: SchemaCore alone peaks at 24GB). They run EXCLUSIVELY,
    -- one at a time, after the leaves; the leaves' pool is RSS-bounded
    -- (leafCostMb/lane against the MemAvailable-derived budget;
    -- measured: <=1.2GB, 0.4-1.6s each).
    let isInner (m : Name) : Bool :=
      checkMods.any fun n => n != m && n.toString.startsWith (m.toString ++ ".")
    let leaves := checkMods.filter fun m => !(isInner m)
    let inners := checkMods.filter isInner
    let total := checkMods.size
    let leafRes ← sweep exe.toString leanPath leaves jobs budgetMs 0 total
      leafCostMb budgetMb marginMb
    let innerRes ← sweep exe.toString leanPath inners 1 budgetMs leaves.size total
      leafCostMb budgetMb marginMb
    for r in leafRes ++ innerRes do
      match r.verdict with
      | .ok => checked := checked + 1
      | .gap => gaps := gaps.push r.mod
      | .rejected msg => failures := failures.push (r.mod, msg)
      | .unknown why => unknowns := unknowns.push (r.mod, why)
  catch e =>
    IO.eprintln s!"kernel-check: {toString e}"
    return 1
  unless stale.isEmpty do
    IO.println "kernel-check: STALE OLEANS deleted (source gone — the build \
      residue poisoned the prefix expansion; `just build` regenerates what \
      is real):"
    for m in stale do IO.println s!"  {m}"
  unless skipped.isEmpty do
    IO.println "kernel-check: declaration-free sources skipped (zero own \
      declarations — their imports are trusted, their subtrees' own decls \
      are replayed by the checked modules):"
    for m in skipped do IO.println s!"  {m}"
  unless gaps.isEmpty do
    IO.println "kernel-check: disclosed gaps (the class per entry: reduceBool \
      — native-policy owns; replay-budget — the real kernel accepts at build):"
    for m in gaps do IO.println s!"  {m}"
  unless unknowns.isEmpty do
    IO.println "kernel-check: UNKNOWN — NO kernel verdict (the budget \
      discipline's honest skip: named, never hung; the coverage is \
      INCOMPLETE by these):"
    for (m, why) in unknowns do IO.println s!"  {m}: {why}"
  if failures.isEmpty then
    if unknowns.isEmpty then
      IO.println s!"kernel-check: clean — {checked} module(s) replayed by the \
        pure-Lean kernel (caveats (a)-(d) in Gates/KernelCheck.lean's header)"
      return 0
    IO.println s!"kernel-check: no rejections — {checked} module(s) replayed, \
      {unknowns.size} UNKNOWN (above; the budget discipline's honest skip). \
      Re-run the named modules with a wider GATES_KERNEL_BUDGET_SECS to \
      close the gap."
    return 0
  IO.eprintln "kernel-check: REJECTIONS outside the known gaps \
    (divergence candidates):"
  for (m, msg) in failures do IO.eprintln s!"  {m}:\n{msg}"
  return 1

end Gates.KernelCheck

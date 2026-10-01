/-
Gates — the Lean-side gates driver (the pipeline-as-machine row,
notes/v3/09-gates-ops.md §3). The root aggregate of the thin skeleton.

- `Gates.Packages`   — the gated package set + the shared env loader
- `Gates.PackagesCheck` — the gated-table drift guard (the table ×
                       lakefile agreement both directions + every row
                       root's source file — a new library without its
                       gates row fails CI)
- `Gates.Common`     — the report-gate combinator (the write-or-diff
                       baseline tail with the loud re-baseline discipline)
- `Gates.Axioms`     — the per-library axiom sweep (kernel CollectAxioms,
                       LintKit's allowlist consumed, notes/axiom-report.md)
- `Gates.DocsCheck`  — the notes excerpt-drift gate (non-sketch lean
                       fences' decl names resolve in the gated envs)
- `Gates.GenCheck`   — the byte-tie gate (committed artifact bytes vs a
                       fresh `SchemaCore.regen`; volatile header exempt)
- `Gates.CodeRegistryCheck` — the persisted E-code registry gate
                       (notes/code-registry.txt: parse + well-formedness
                       + the allocation replay + self-stability + the
                       canonical bytes; notes/v3/05-codegen.md §4)
- `Gates.SnapshotCheck` — the universe-snapshot gate
                       (notes/universe.snapshot: the committed baseline
                       vs the fresh canonical render of the replayed
                       registry; notes/v3/03-bidirectional.md §7)
- `Gates.Audit`         — the artifact self-audit (09 §5: the AuditRule
                       list over every committed generated artifact)
- `Gates.ArtifactHeaders` — the 2-line GENERATED header presence +
                       shape over the artifact surface (the one-writer
                       rule's detection face)
- `Gates.NativePolicy`  — the native_decide grandfathering gate (the
                       committed allowlist set + the staleness ratchet)
- `Gates.Coverage`      — the Ty-ctor × emitter coverage matrix
                       (probe-differential; baseline notes/coverage-matrix.md)
- `Gates.KernelCheck`   — the lean4lean pure-kernel replay of every
                       gated module (the independent double-check)
- `Gates.Ownership`   — the artifact-ownership gate (D15: the
                       declared-vs-actual agreement both directions + the
                       cross-emitter disjointness over the REAL emitter set)
- `Gates.Breaking`    — the breaking gate (the committed universe snapshot
                       vs the replayed registry: the diff + the three-way
                       verdict + the exit-code discipline — unremedied = 2)
- `Gates.Impact`      — the impact-aware gating core (09 §6: the change
                       set → affected modules → artifacts → gates; the
                       conservatism theorems; the `impacted` driver)
- `Gates.ElabWatch`  — the elaboration-time regression watch (09 §7:
                       per-module elaboration re-timed against the
                       committed baseline notes/elab-baseline.tsv; a
                       >2× delta flags, the normal drift passes)
- `Gates.Lint`       — the lint gate row (the enforcement wave's
                       headline: the env/text linters' CI teeth — the
                       lintkit exe's OWN shard fold per gated package,
                       the row fails when any package has findings; the
                       sabotage teeth live in GatesTests.Main)
- `Gates.Census`     — the proof-hygiene censuses promoted to
                       baselined report-gates at 09 §8's trigger (the
                       first adjudicated nonempty run):
                       decide-first-census + zero-citation-census + the
                       evidence-redundancy census (B6; D37's teeth),
                       the findings as DATA, drift flagged
- `Gates.NolintCensus` — the nolint census gate (the opt-out rows'
                       per-(linter, file) counts, baselined in
                       notes/nolint-census.tsv; a new silenced site
                       lands as a deliberate re-baseline diff)
- `Gates.Feasibility` — the spec-sanity gate row (B2; 04 §5 + D21):
                       the registered specs' feasibility census (the
                       proof-carrying witnesses / the declared
                       emptiness / the unchecked warnings), baselined
                       in notes/feasibility-census.md

The five questions (notes/v3/01-core.md): the registry answers none
directly — it is the gates machine's data row (09 §3): root = Universe
(the closed gate set, below), carrier = none, spine = the gate fold
(`all` runs the registry in order, first failure stops), ladder rung
n/a. Gate row: this IS the gate-row surface (the subcommands are the
rows).

The `all` driver runs each gate as a CHILD `lake exe gates <name>`
process, not in-process: the env-loading gates (axioms, native-policy,
coverage) each import every gated package's environment, and libgc's
conservative stack scan RETAINS a dropped env — in-process accumulation
peaked ~16GB RSS and earlyoom SIGTERM'd the whole run under memory
pressure (the legacy tree's sharded-mode lesson, arrived again at six
gated packages). One child per gate bounds the peak at the heaviest
single gate; `lake` is the in-tree spawn precedent (KernelCheck), the
subcommand interface is the justfile's rows verbatim.

The composition discipline CHANGED at wave 29 (the speed wave): the
sequential first-failure-stops was the OOM era's shape — the env-replay
gates now run as bounded-parallel child processes (GATES_ALL_JOBS,
default 4 — the count cap), the gates being independent (read-only over
committed state; every `--write` is a manual mode), and ALL verdicts
are collected: the failures do not stop the battery, the ordered report
at the end names every row's verdict + wall time (the dev loop's fast
feedback AND the full battery's completeness). A gate that must stay
sequential for a real reason would carry its own child serialization;
none does today.

AND at wave 30 the parallelism got its honest bound — the RSS
admission (`Gates.rssAdmits` in Common): a gate spawns only while the
PROJECTED peak (the sum of the live gates' `gateFootprintMb` + the
candidate's + the margin) stays under the MemAvailable-derived budget
(~23.4GB on the 29GB box, 90% of MemAvailable — the per-lane costs
are rounded UP from measured peaks, so the round-up IS the headroom).
The footprints are MEASURED (the derivations live at their
definitions). The RETUNE lesson (two battery runs): fat lane counts
made each heavy gate's worst-case footprint 16GB-class, and the
heavy gates SERIALIZED — 4:34 against the before-run's 2:38. The
landed shape (3-lane shard pools = 6.2GB/gate, 6-lane kernel leaves
= 7.8GB, ~2GB loaders) fits ALL of them under the budget at once:
the full battery overlaps, every projected peak under budget, and
over budget a gate QUEUES — never dropped, never OOM. The 24GB
inner-node hazard stays exclusive (its sweep's own discipline).
-/
import Gates.Packages
import Gates.PackagesCheck
import Gates.Common
import Gates.ObligationView  -- B7: the gates' rows AS obligation values
import Gates.Axioms
import Gates.DocsCheck
import Gates.GenCheck
import Gates.CodeRegistryCheck
import Gates.SnapshotCheck
import Gates.Audit
import Gates.ArtifactHeaders
import Gates.NativePolicy
import Gates.Coverage
import Gates.KernelCheck
import Gates.Ownership
import Gates.Breaking
import Gates.Impact
import Gates.ElabWatch
import Gates.Lint
import Gates.Census
import Gates.NolintCensus
import Gates.LegacyHash
import Gates.Feasibility

open Gates

/-- The closed gate set, in run order (the `all` driver's data — one
driver over the set, notes/v3/09-gates-ops.md §3). The dispatch lives
in GatesMain (the exe); this list is the single source of WHAT runs.
-/
def Gates.gateNames : List String :=
  ["packages-check", "lint", "axioms", "docs-check", "gen-check",
   "code-registry-check", "snapshot-check", "audit", "artifact-headers",
   "native-policy", "coverage", "kernel-check", "ownership", "breaking",
   "decide-first-census", "zero-citation-census",
   "evidence-redundancy-census", "nolint-census",
   "legacy-hash", "feasibility", "elab-watch"]

/-- The MEASURED per-gate worst-concurrent footprint (MB) — the runAll
    admission's per-lane cost (wave-30 /usr/bin/time over each gate;
    the env-replay rows' footprints INCLUDE their internal pools'
    worst concurrent sum, since those children are separate processes
    the driver's own RSS does not show):
  * kernel-check: `kernelJobs × 1300` — the leaf pool's worst sum
    (leaves ≤1.2GB measured, 1.3GB budgeted; the 24GB inner node is
    EXCLUSIVE within its sweep — the footprint here covers the leaf
    phase, the phase that overlaps co-running gates).
  * axioms / native-policy: `poolJobs × 2048` — the shard pools' worst
    sum (an env-replay shard peaks ≤2GB measured: Kit 1.63-1.72GB,
    SchemaCore 1.66GB). At the 3-lane default: 6.2GB/gate — both
    pools + the kernel leaf pool co-run under the budget (the 8-lane
    first cut made it 16GB/gate and SERIALIZED the battery: the
    retune lesson).
  * docs-check: `poolJobs × 2048` — the shard pool's worst sum (the
    per-package env loads moved to child processes — the libgc
    retention made the in-process fold peak 27GB + earlyoom; the
    shards are the axioms class, ≤2GB each measured).
  * coverage: 2048 — the env-replay row's safe face (0.14GB measured
    standalone; budgeted like a loader).
  * everything else: 1024 — the light artifact/report drivers
    (packages-check, gen-check, code-registry-check, snapshot-check,
    audit, artifact-headers, ownership, breaking — sub-1GB measured,
    `lake exe` startup included).
-/
def gateFootprintMb (kernelJobs poolJobs : Nat) : String → Nat
  | "kernel-check" => kernelJobs * Gates.KernelCheck.leafCostMb
  | "axioms" => poolJobs * shardCostMb
  | "native-policy" => poolJobs * shardCostMb
  | "docs-check" => poolJobs * shardCostMb
  | "coverage" => 2048
  | "elab-watch" => 2048  -- one `lake env lean` replay at a time
                          -- (a root's re-elaboration peaks 1-2GB)
  | "lint" => poolJobs * shardCostMb  -- the shard class: one package
                          -- env replay per child (the pkgPool lanes')
  | "decide-first-census" => poolJobs * shardCostMb  -- the shard class
  | "zero-citation-census" => poolJobs * shardCostMb  -- the shard class
  | "nolint-census" => 1024  -- the text scan (no env replays)
  | _ => 1024

/-- The gates that must run ALONE — no co-running gate, either way
    (the candidate waits for an empty `live`; nothing spawns while the
    gate is live): the WALL-TIME measurement gate. elab-watch times
    `lake env lean` replays; under the battery's parallel load the
    measured times inflate NONUNIFORMLY (the big roots inflate past
    2× their committed ratio while the reference calibration divides
    out only uniform slowdown) — the observed `gates all` FAIL that
    passes standalone. The battery's one serialization: measurement
    drift is a lie the report would commit, so the timing row measures
    on a quiet box even inside `all`. -/
def gateExclusive : String → Bool
  | "elab-watch" => true
  | _ => false

/-- The inherited-stdio child (the report streams live). -/
abbrev AllChild :=
  IO.Process.Child { stdin := .inherit, stdout := .inherit, stderr := .inherit :
    IO.Process.StdioConfig }

/-- `gates all` — every registered gate in one run, at bounded
    parallelism (GATES_ALL_JOBS, default 6 — the count cap; the RSS
    admission is the real bound) under the
    RSS admission (the projected peak of the live gates' footprints +
    the candidate's + the margin stays under the MemAvailable-derived
    budget; over budget a gate QUEUES — never dropped, never OOM; the
    first lane always admits — a single over-budget gate is the inner
    node's class, exclusivity is its discipline, refusal never a
    deadlock) AND the measurement exclusivity (`gateExclusive`: the
    timing row runs ALONE — its deltas must measure the modules, not
    the battery's own load): START printed at spawn, a PASS/FAIL
    completion line
    with the wall time as each gate lands, the ordered verdict report
    at the end (the registry's run order, not completion order). ALL
    gates run — the failures collect, they do not stop the battery
    (the parallel-collection discipline; the first-failure-stop was
    the OOM era's shape). Exit code: the FIRST registry-ordered
    failure's code, else 0. -/
unsafe def Gates.runAll : IO UInt32 := do
  -- the knobs ride the config face (C4's dogfood): the config file is
  -- the validated base layer, the env vars the override source; a
  -- refusal (mis-typed file value, violated check row) is the LOUD exit
  match ← Gates.loadKnobs with
  | .error d => IO.eprintln (Kit.Diag.toString d); return 1
  | .ok kr =>
  let jobs ← Gates.knobNat kr "all_jobs" 6
  let budgetMb ← Gates.rssBudgetMb kr
  let marginMb ← Gates.rssMarginMb kr
  let kernelJobs ← Gates.knobNat kr "kernel_jobs" 6
  let poolJobs ← Gates.knobNat kr "pool_jobs" 3
  let footprint := gateFootprintMb kernelJobs poolJobs
  let names : Array String := Gates.gateNames.toArray
  IO.println (s!"gates all: {names.size} gate(s), {jobs} at a time, " ++
    s!"RSS budget {budgetMb}MB (GATES_ALL_JOBS + the {marginMb}MB margin; " ++
    "every gate runs, the failures collect)")
  let mut results : Array (String × UInt32 × Nat) := #[]
  let mut live : Array (String × AllChild × Nat) := #[]
  let mut next := 0
  try
    while results.size < names.size do
      -- fill: the count cap AND the RSS admission, in registry order
      -- (a gate that does not fit WAITS for a live gate to land — the
      -- gates queue; `live.isEmpty` admits the first lane
      -- unconditionally, so a single over-budget gate cannot deadlock
      -- the driver)
      let mut admitted := true
      while admitted && next < names.size && live.size < jobs do
        let cost := live.foldl (fun acc (n, _, _) => acc + footprint n) 0
        let fp := footprint names[next]!
        -- the exclusivity discipline on top of the RSS admission: an
        -- exclusive candidate admits only into an empty `live`, and
        -- nothing admits while an exclusive gate is live
        let candExcl := gateExclusive names[next]!
        let liveExcl := live.any fun (n, _, _) => gateExclusive n
        let fits := if candExcl then live.isEmpty else !liveExcl
        if fits && (live.isEmpty || rssAdmits budgetMb marginMb (cost + fp)) then
          let name := names[next]!
          IO.println s!"══ gates all: {name} — START ══"
          let child : AllChild ← IO.Process.spawn
            { cmd := "lake", args := #["exe", "gates", name]
            , stdin := .inherit, stdout := .inherit, stderr := .inherit }
          live := live.push (name, child, ← IO.monoMsNow)
          next := next + 1
        else
          admitted := false
      IO.sleep 100
      let mut still : Array (String × AllChild × Nat) := #[]
      for (name, child, t0) in live do
        match ← child.tryWait with
        | some code =>
          let ms := (← IO.monoMsNow) - t0
          let word := if code == 0 then "PASS" else "FAIL"
          IO.println s!"══ gates all: {name} — {word} ({ms / 1000}s) ══"
          results := results.push (name, code, ms)
        | none => still := still.push (name, child, t0)
      live := still
  catch e =>
    IO.eprintln s!"gates all: driver error: {toString e}"
    return 1
  -- the ordered report (the registry's run order, not completion order)
  IO.println s!"gates all: the verdicts (registry order):"
  for name in Gates.gateNames do
    match results.find? fun (n, _, _) => n == name with
    | some (_, code, ms) =>
      let word := if code == 0 then "PASS" else "FAIL"
      IO.println s!"  {name}: {word} ({ms / 1000}s)"
    | none => pure ()
  for name in Gates.gateNames do
    match results.find? fun (n, _, _) => n == name with
    | some (_, code, _) =>
      if code != 0 then
        IO.eprintln s!"gates all: {name} FAILED (exit {code})"
        return code
    | none => pure ()
  IO.println "gates all: clean"
  return 0

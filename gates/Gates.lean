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
- `Gates.Nanoda`       — the kernel-check row's SECOND lane
                       (`--nanoda`, wave cadence: lean4export → nanoda,
                       the external kernel's agreement face; the pins,
                       the teeth, the honest skip)
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

The composition discipline is the WARM SERVER (this redesign): the
gates exe is ONE process over the tree's ONE environment. Three row
classes:

- THE WARM ROWS (lint, axioms, docs-check, native-policy, coverage,
  the three censuses): the tree's LIBRARY env loaded ONCE per process
  (`Gates.loadWarmEnv` in Common — the O(gates × env-load) time and
  O(gates × env-size) memory of the per-shard child fleets are GONE;
  the docs-check 27GB peak was the per-shard retention libgc's
  conservative scan never released), and each row runs as a pure
  Env → Verdict fold against it, per-package scopes making the
  verdicts byte-equivalent to the old shards (the scoping notes at
  `loadWarmEnv` and LintKit.Citations' census scope). The TESTS-LIB
  rows CANNOT ride the warm env (their root modules each define a
  root-namespace `main`; two `main` constants cannot coexist in one
  `importModules`): the per-package env-consuming rows compose a
  SECOND leg — one child shard per tests-lib row
  (`Gates.testLibPool`, the RSS admission's pool), the per-package
  env load paid in processes that die.
- THE ARTIFACT ROWS (packages-check, gen-check, code-registry-check,
  snapshot-check, audit, artifact-headers, ownership, breaking,
  nolint-census, legacy-hash, feasibility): they read committed bytes
  and registered emitters, never a module env — they skip the env
  entirely and run in-process.
- THE CHILD ROWS (kernel-check, elab-watch): compute that must NOT
  share the driver's process — the kernel-check's lean4lean replay
  pool (its own RSS admission inside) and the elab-watch's
  `lake env lean` re-timings (a measurement gate: it runs LAST,
  ALONE, on a quiet box — the exclusivity discipline kept, structural
  now instead of a co-run check). They run as SEPARATE child
  processes, SEQUENTIALLY, and — the recorded failure this ordering
  answers — the kernel-check child runs BEFORE the warm env loads:
  its replay pool's RSS budget is derived from MemAvailable at ITS
  start and is blind to the driver's concurrently-growing env (the
  first redesign spawned it concurrent with the load; the combined
  demand — 6 × 1.3GB leaves + the ~24GB inner-node replays + the
  multi-GB warm load — blew the box, earlyoom SIGTERMed the driver
  mid-load, and the slow face was a 47-minute swap-thrash crawl).
  On the thin pre-load driver the child's box is byte-identical to
  its standalone run (measured: 2m25s both faces).

The env is PINNED at load: a mid-run edit is invisible until the next
run - the warm face's honest staleness note. `--cold=<gate>` (the
`all` row's flag, repeatable) runs the named rows as child
`lake exe gates <gate>` processes instead — the release/debug parity
path (each child then loads its own warm env) — ONE AT A TIME, after
the in-process rows: concurrent cold children each loading a warm env
beside the driver's own would rebuild the exact contention this
driver's sequencing exists to prevent.

The wave-29/30 shard+pool+admission machinery (per-gate child fleets,
`shardDispatch`, `pkgPool`, the per-gate footprint table) died with
its root: one env, loaded once, retained once — libgc has nothing to
misplace. `poolEngine` survives ONLY as the kernel-check leaf pool's
spine (the genuinely-parallel compute). The verdicts' determinism
discipline is unchanged: every row runs read-only over committed
state (every `--write` is a manual mode), all verdicts collect, the
ordered report names every row's verdict + wall time.

THE VERDICT CACHE (the demand-set discipline one layer up): a warm
row's verdict is memoized under a CONTENT-ADDRESSED key — the env's
olean-surface digest (path + size + lake trace hash per module, the
incremental-build discipline's own hash files) + the gate's name +
the gate's code version + the committed baseline's digest. The
conservative-invalidation rule (09 §4's demand-set correction): the
key records every input class the verdict reads — a change to ANY of
them yields a new key, never a stale hit; a cache hit replays the
fold's own stored output + exit (the fold's bytes, provably — the
key's content-addressing), and a corrupt/unparseable cache entry is a
MISS (refusal), never a wrong verdict. The cache is a LOCAL file
(`.gates-warm-cache/`), never committed: CI runs cold; the dev loop
hits.
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
import Gates.Nanoda
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

/-- The WARM ROWS: the env-consuming gate rows — one shared
    environment (`loadWarmEnv`), each a pure Env → Verdict fold. -/
def Gates.warmGateNames : List String :=
  ["lint", "axioms", "docs-check", "native-policy", "coverage",
   "decide-first-census", "zero-citation-census",
   "evidence-redundancy-census"]

/-- The CHILD ROWS: compute that must not share the driver's process —
    the kernel-check's lean4lean replay pool and the elab-watch's
    re-timings (the measurement gate runs LAST, ALONE). -/
def Gates.childGateNames : List String := ["kernel-check", "elab-watch"]

/-- The ARTIFACT ROWS: everything else — committed-bytes reads, no env.
    Defined as the registry minus the other two classes (the closed
    set's complement; the GatesTests coherence pin demands the three
    classes partition `gateNames` exactly). -/
def Gates.artifactGateNames : List String :=
  gateNames.filter fun n =>
    !(Gates.warmGateNames.contains n || Gates.childGateNames.contains n)

/-- The row classes' coherence (the dispatch's closed world): every
    registry row is warm, artifact, or child — exactly one. Pure, so
    the battery pins it (a row landing in no class would SILENTLY skip
    in `all`). -/
def Gates.gateClassified (name : String) : Bool :=
  (Gates.warmGateNames.contains name || Gates.artifactGateNames.contains name
    || Gates.childGateNames.contains name)
  && !(Gates.warmGateNames.contains name && Gates.artifactGateNames.contains name)
  && !(Gates.warmGateNames.contains name && Gates.childGateNames.contains name)
  && !(Gates.artifactGateNames.contains name && Gates.childGateNames.contains name)

/-- The `--cold` list's validation (PURE — the closed-world refusal the
    `all` driver makes loud; the teeth pin it): an unknown name, or a
    child row (already a child — nothing to fall back), refuses. -/
def Gates.coldRefusal? : List String → Option String
  | [] => none
  | c :: rest =>
      if !gateNames.contains c then
        some s!"--cold={c} names no gate row"
      else if Gates.childGateNames.contains c then
        some s!"--cold={c} is already a child row"
      else Gates.coldRefusal? rest

/-! ## The verdict cache (the demand-set discipline, one layer up) -/

/-- The cache's root (LOCAL — never committed; CI runs cold, the dev
    loop hits). One file per verdict, named by the key's digest; the
    file's whole content is the fold's exit code. -/
def Gates.warmCacheDir : System.FilePath := ".gates-warm-cache"

/-- FNV-1a 64-bit over a string (the ONE digest — content-addressing
    for the cache keys; a hash is a discipline device, not a claim). -/
def Gates.fnv1a (s : String) : Nat :=
  let fold := fun (h : Nat) (c : Char) =>
    ((h * 0x100000001b3) ^^^ c.toNat) % 0x10000000000000000
  s.toList.foldl fold 0xcbf29ce484222325

/-- Hex render of a digest (the cache file's name face). Fuel 16
    nibbles (a 64-bit digest's bound) — the digit loop's structured
    face, no termination hazard. -/
def Gates.hexOf (n : Nat) : String :=
  let digits := "0123456789abcdef".toList
  if n == 0 then "0"
  else Id.run do
    let mut acc := ""
    let mut x := n
    for _ in [0:16] do
      if x == 0 then break
      acc := String.singleton (digits.getD (x % 16) '0') ++ acc
      x := x / 16
    return acc

/-- The ENV digest: the olean surface's content-address — per module,
    the olean's (name, size, lake trace hash) triple; the trace hash is
    the incremental-build discipline's OWN content hash
    (`<mod>.olean.hash`), so a rebuilt module changes the digest and a
    rebuilt importer does too (the traces cascade). A MISSING trace
    hash contributes (name, size) only — the conservative face: the
    digest stays sensitive to the surface it saw. -/
def Gates.envDigestOf (surface : Array (String × Nat × String)) : Nat :=
  Gates.fnv1a (String.intercalate ""
    (surface.toList.map fun (p, sz, h) => s!"{p}:{sz}:{h}\n"))

/-- The gate's CODE VERSION — bump when the row's analysis changes
    (the key must move when the fold does; a version bump is the
    cache's own re-baseline, never the baselines'). v2: the tests-lib
    coverage restoration (the two-leg warm faces — `testLibPool`'s
    shard leg changed every env-consuming row's verdict surface). -/
def Gates.gateCacheVersion (_gate : String) : Nat := 2

/-- A warm row's cache key: env digest + gate + version + the
    baseline's digest (the committed baseline is a verdict input — the
    diff gates' verdicts are OVER it). `baselineDigest = 0` for the
    baseline-free rows (native-policy). The env digest is passed in
    (computed ONCE per warm run, shared by every row). -/
def Gates.warmCacheKey (envDigest : Nat) (gate : String)
    (baselineDigest : Nat) : Nat :=
  Gates.fnv1a s!"{Gates.hexOf envDigest}|{gate}|{Gates.gateCacheVersion gate}|{baselineDigest}"

/-- The cache READ: a hit returns the stored exit code; a missing OR
    UNPARSEABLE entry is `none` (the refusal face: a corrupt cache is
    a miss, never a wrong verdict — the stale-cache refusal tooth). -/
def Gates.warmCacheRead (key : Nat) : IO (Option UInt32) := do
  let path := Gates.warmCacheDir / s!"{Gates.hexOf key}"
  match ← (IO.FS.readFile path |>.toBaseIO) with
  | .error _ => return none
  | .ok text =>
      match (text.trimAscii.toString.dropPrefix? "exit ") with
      | some digits =>
          match digits.toNat? with
          | some n => return some (n % 256).toUInt32
          | none => return none
      | none => return none

/-- The cache WRITE (the fold's verdict, stored under its key). -/
def Gates.warmCacheWrite (key : Nat) (code : UInt32) : IO Unit := do
  let _ ← (IO.FS.createDirAll Gates.warmCacheDir |>.toBaseIO)
  IO.FS.writeFile (Gates.warmCacheDir / s!"{Gates.hexOf key}") s!"exit {code % 256}\n"

/-- A cached hit's replay: the provenance line (the verdict IS the
    fold's — the key's content-addressing), the stored exit returned. -/
def Gates.warmCacheReplay (gate : String) (code : UInt32) : IO UInt32 := do
  IO.println s!"{gate}: CACHED VERDICT (the warm cache's content-addressed \
    replay of the fold's exit — `GATES_WARM_CACHE=0` runs the fold)"
  return code

/-- The cache knob (env-only — the config schema's fields are the
    concurrency knobs' dogfood; the cache rides the override source):
    `GATES_WARM_CACHE=0` disables. -/
def Gates.warmCacheOn : IO Bool := do
  return (← Gates.envNat "GATES_WARM_CACHE" 1) != 0

/-- The olean surface (the env digest's input): every .olean + its
    trace hash under the root build dir. FUEL-BOUNDED walk (the
    leanFilesUnder precedent): exhaustion is the honest NO-CACHE face
    (`Gates.oleanSurface` returns none — a walk that could not complete
    never feeds a cache key). -/
def Gates.oleanSurface : IO (Option (Array (String × Nat × String))) := do
  let libDir : System.FilePath := ".lake/build/lib/lean"
  unless ← libDir.pathExists do return none
  let rec walk : Nat → System.FilePath →
      IO (Array (String × Nat × String) × Bool)
    | 0, _ => return (#[], true)
    | fuel + 1, dir => do
      let mut out : Array (String × Nat × String) := #[]
      let mut exhausted := false
      for e in ← dir.readDir do
        if ← e.path.isDir then
          let (sub, ex) ← walk fuel e.path
          out := out ++ sub
          exhausted := exhausted || ex
        else if e.path.extension == some "olean" then
          let mt ← e.path.metadata
          let h ← match ← (IO.FS.readFile (e.path.withExtension "olean.hash")
              |>.toBaseIO) with
            | .ok t => pure t.trimAscii.toString
            | .error _ => pure ""
          out := out.push (e.path.toString, mt.byteSize.toNat, h)
      return (out, exhausted)
  let (surface, exhausted) ← walk 64 libDir
  if exhausted then return none
  return (some surface)

/-- The baseline digest (a verdict input for the diff gates): the
    committed file's bytes, hashed; an absent baseline digests to 0
    (the bootstrap face — its verdict differs from an in-sync one). -/
def Gates.baselineDigestOf (path : System.FilePath) : IO Nat := do
  match ← (IO.FS.readFile path |>.toBaseIO) with
  | .error _ => return 0
  | .ok text => return Gates.fnv1a text

/-- The diff gates' baseline paths (the cache key's baseline input —
    the ONE mapping; a row with no baseline here is baseline-free). -/
def Gates.gateBaselinePath (gate : String) : Option System.FilePath :=
  match gate with
  | "axioms" => some "notes/axiom-report.md"
  | "coverage" => some "notes/coverage-matrix.md"
  | "decide-first-census" => some "notes/decide-first-census.md"
  | "zero-citation-census" => some "notes/zero-citation-census.md"
  | "evidence-redundancy-census" => some "notes/evidence-redundancy-census.md"
  | _ => none

/-- A warm row's guarded run: the cache consulted (default faces only —
    `all` runs no `--write`/`--strict` mode; manual modes are
    deliberate acts, never cached), a hit replays the stored verdict,
    a miss runs the fold and stores. -/
unsafe def runWarmCached (gate : String) (envDigest : Nat)
    (k : IO UInt32) : IO UInt32 := do
  unless ← Gates.warmCacheOn do
    return ← k
  let bd ← match Gates.gateBaselinePath gate with
    | some p => Gates.baselineDigestOf p
    | none => pure 0
  let key := Gates.warmCacheKey envDigest gate bd
  match ← Gates.warmCacheRead key with
  | some code => Gates.warmCacheReplay gate code
  | none =>
      let code ← k
      let _ ← Gates.warmCacheWrite key code
      return code

/-! ## The `all` driver (the warm-server shape) -/

/-- The inherited-stdio child (the report streams live). -/
abbrev AllChild :=
  IO.Process.Child { stdin := .inherit, stdout := .inherit, stderr := .inherit :
    IO.Process.StdioConfig }

/-- The dispatch's warm fold: the named row's WARM face in-process
    against the shared env (the class coherence pin in GatesTests
    guarantees the name is a warm row). The census rows' titles/descrs
    are the census module's OWN constants (the baseline header's
    inputs — one source, the same bytes the standalone rows render). -/
unsafe def runWarmGate (env : Lean.Environment) (name : String) : IO UInt32 := do
  match name with
  | "lint" => Gates.Lint.runWarm env
  | "axioms" => Gates.Axioms.runWarm false false env
  | "docs-check" => Gates.DocsCheck.runWarm env
  | "native-policy" => Gates.NativePolicy.runWarm env
  | "coverage" => Gates.Coverage.runWarm false false false env
  | "decide-first-census" =>
      (Gates.Census.runWarm Gates.Census.decideFirst
        Gates.Census.decideFirstTitle Gates.Census.decideFirstDescr
        false false env)
  | "zero-citation-census" =>
      (Gates.Census.runWarm Gates.Census.zeroCitation
        Gates.Census.zeroCitationTitle Gates.Census.zeroCitationDescr
        false false env)
  | "evidence-redundancy-census" =>
      (Gates.Census.runWarm Gates.Census.evidenceRedundancy
        Gates.Census.evidenceRedundancyTitle Gates.Census.evidenceRedundancyDescr
        false false env)
  | n =>
      -- unreachable by the class coherence pin; fail closed anyway
      IO.eprintln s!"gates all: {n} is not a warm row (the class discipline)"
      return 1

/-- The artifact rows' in-process dispatch (the env-free rows' faces —
    the committed-bytes reads; the same subcommand bodies GatesMain's
    table runs, at their default no-write faces). -/
unsafe def runArtifactGate (name : String) : IO UInt32 := do
  match name with
  | "packages-check" => Gates.PackagesCheck.run
  | "gen-check" => Gates.GenCheck.run
  | "code-registry-check" => Gates.CodeRegistryCheck.run false
  | "snapshot-check" => Gates.SnapshotCheck.run false
  | "audit" => Gates.Audit.run
  | "artifact-headers" => Gates.ArtifactHeaders.run
  | "ownership" => Gates.Ownership.run
  | "breaking" => Gates.Breaking.run
  | "nolint-census" => Gates.NolintCensus.run false false
  | "legacy-hash" => Gates.LegacyHash.run false false
  | "feasibility" => Gates.Feasibility.run false false
  | n =>
      -- unreachable by the class coherence pin; fail closed anyway
      IO.eprintln s!"gates all: {n} is not an artifact row (the class discipline)"
      return 1

/-- `gates all` — every registered gate in ONE warm run, in FOUR
    phases (the wall order is the process-state discipline; the
    REPORT order is the registry):
    1. the CHILD rows as sequential child processes (the kernel-check
       row on the thin pre-load driver — a quiet box, byte-identical
       to its standalone run; see the CHILD ROWS note in the module
       header for the recorded failure the concurrency caused);
    2. the ARTIFACT rows in-process on the FRESH process (env-free
       committed-bytes reads — but the regen faces' whnf budgets are
       process-state-sensitive: measured, after the heavy warm folds
       ran first, gen-check/audit hit the heartbeat cap where the
       standalone process passes; before the load + folds the
       driver's state IS the standalone run's);
    3. the tree's env loaded ONCE, the warm rows folded in registry
       order against it (cache-guarded);
    4. the `--cold=<gate>` children one at a time, then elab-watch
       LAST, ALONE (the measurement gate; the driver's env is
       resident but idle — the re-timings are CPU-bound, the box is
       otherwise quiet).
    An unknown cold name REFUSES (the closed world). The report is
    the registry-ordered verdict table (every row's verdict + wall
    time); exit = the first registry-ordered failure's code. -/
unsafe def Gates.runAll (cold : List String) : IO UInt32 := do
  -- the cold names are closed-world (the pure validator's refusal made
  -- loud — an unknown name is never a silently-skipped row;
  -- Gates.coldRefusal? is PURE — the battery pins it)
  match Gates.coldRefusal? cold with
  | some why =>
      IO.eprintln ("gates all: " ++ why ++ " (the registry: "
        ++ String.intercalate ", " gateNames ++ ")")
      return 1
  | none => pure ()
  match ← Gates.loadKnobs with
  | .error d => IO.eprintln (Kit.Diag.toString d); return 1
  | .ok _kr =>
  let names : Array String := gateNames.toArray
  let t0 ← IO.monoMsNow
  IO.println s!"gates all: {names.size} gate(s) — the warm server: the child \
    rows first (the pre-load quiet box), ONE env load, the warm rows \
    in-process (the env pinned at load; a mid-run edit is the next run's input)"
  let mut results : Array (String × UInt32 × Nat) := #[]
  -- THE CHILD ROWS FIRST (the pre-load quiet box): every child row
  -- except elab-watch — the kernel-check row — runs as a waited child
  -- process BEFORE the warm env loads, so its replay pool's budget
  -- faces the same fresh box its standalone run does (the recorded
  -- failure: the concurrent-spawn shape let the pool's MemAvailable
  -- budget go blind to the driver's growing env — earlyoom killed the
  -- driver mid-load, or the box swap-thrashed for 47+ minutes).
  -- elab-watch stays LAST (below) — the measurement gate's discipline.
  try
    for name in Gates.childGateNames do
      if name == "elab-watch" then continue
      IO.println s!"══ gates all: {name} — START (child, pre-load quiet box) ══"
      let st ← IO.monoMsNow
      let child : AllChild ← IO.Process.spawn
        { cmd := "lake", args := #["exe", "gates", name]
        , stdin := .inherit, stdout := .inherit, stderr := .inherit }
      let code ← child.wait
      let ms := (← IO.monoMsNow) - st
      let word := if code == 0 then "PASS" else "FAIL"
      IO.println s!"══ gates all: {name} — {word} ({ms / 1000}s) ══"
      results := results.push (name, code, ms)
  catch e =>
    IO.eprintln s!"gates all: child spawn failed: {toString e}"
    return 1
  -- THE ARTIFACT ROWS FIRST (the fresh-process face): the env-free
  -- rows run BEFORE the warm load and any fold — the regen faces'
  -- whnf budgets proved process-state-sensitive (the cold run's
  -- recorded flip: gen-check/audit heartbeat-faulted after the heavy
  -- folds; standalone, both pass). No cost: they read committed bytes,
  -- never the env. The cold rows' names skip to their phase (below).
  for name in gateNames do
    if Gates.warmGateNames.contains name then continue
    if Gates.childGateNames.contains name then continue  -- ran above (child, pre-load)
    if cold.contains name then continue            -- the cold child's row (below)
    let start ← IO.monoMsNow
    IO.println s!"══ gates all: {name} — START ══"
    let code ← runArtifactGate name
    let ms := (← IO.monoMsNow) - start
    let word := if code == 0 then "PASS" else "FAIL"
    IO.println s!"══ gates all: {name} — {word} ({ms / 1000}s) ══"
    results := results.push (name, code, ms)
  -- THE WARM LOAD (once — the battery's one env cost)
  let warmT0 ← IO.monoMsNow
  let env ← match ← Gates.loadWarmEnv with
    | .error e =>
        IO.eprintln s!"gates all: WARM LOAD FAILED — {e} (run `just build` first)"
        return 1
    | .ok env => pure env
  IO.println s!"gates all: warm env loaded ({(← IO.monoMsNow) - warmT0}ms — \
    every gated package's roots, ONE environment)"
  -- the env digest (once, shared by every row's cache key); an
  -- exhausted walk = the honest no-cache face (digest 0 never stored)
  let cacheOn ← Gates.warmCacheOn
  let envDigest ←
    if cacheOn then
      match ← Gates.oleanSurface with
      | some surface => pure (Gates.envDigestOf surface)
      | none => pure 0
    else pure 0
  -- the WARM rows, registry order, cache-guarded (the ONE env cost
  -- buys every fold below; the cold rows' names skip to their phase)
  for name in gateNames do
    if !Gates.warmGateNames.contains name then continue
    if cold.contains name then continue            -- the cold child's row (below)
    let start ← IO.monoMsNow
    IO.println s!"══ gates all: {name} — START ══"
    let code ← runWarmCached name envDigest (runWarmGate env name)
    let ms := (← IO.monoMsNow) - start
    let word := if code == 0 then "PASS" else "FAIL"
    IO.println s!"══ gates all: {name} — {word} ({ms / 1000}s) ══"
    results := results.push (name, code, ms)
  -- the COLD children: ONE AT A TIME, after the in-process rows (each
  -- loads its own warm env — the release/debug parity path; the
  -- concurrency this replaces is the recorded contention)
  try
    for name in cold do
      IO.println s!"══ gates all: {name} — START (cold child) ══"
      let st ← IO.monoMsNow
      let child : AllChild ← IO.Process.spawn
        { cmd := "lake", args := #["exe", "gates", name]
        , stdin := .inherit, stdout := .inherit, stderr := .inherit }
      let code ← child.wait
      let ms := (← IO.monoMsNow) - st
      let word := if code == 0 then "PASS" else "FAIL"
      IO.println s!"══ gates all: {name} — {word} ({ms / 1000}s) ══"
      results := results.push (name, code, ms)
  catch e =>
    IO.eprintln s!"gates all: driver error: {toString e}"
    return 1
  -- elab-watch LAST, ALONE (the measurement gate; the driver's env is
  -- resident but idle — the re-timings are CPU-bound on a quiet box)
  let start ← IO.monoMsNow
  IO.println "══ gates all: elab-watch — START ══"
  try
    let child : AllChild ← IO.Process.spawn
      { cmd := "lake", args := #["exe", "gates", "elab-watch"]
      , stdin := .inherit, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    let ms := (← IO.monoMsNow) - start
    let word := if code == 0 then "PASS" else "FAIL"
    IO.println s!"══ gates all: elab-watch — {word} ({ms / 1000}s) ══"
    results := results.push ("elab-watch", code, ms)
  catch e =>
    IO.eprintln s!"gates all: elab-watch spawn failed: {toString e}"
    return 1
  -- the ordered report (the REGISTRY's order, not the wall order —
  -- the child rows ran first, the quiet-box discipline)
  IO.println "gates all: the verdicts (registry order):"
  for name in gateNames do
    match results.find? fun (n, _, _) => n == name with
    | some (_, code, ms) =>
        let word := if code == 0 then "PASS" else "FAIL"
        IO.println s!"  {name}: {word} ({ms / 1000}s)"
    | none => IO.println s!"  {name}: MISSING (the dispatch's coherence broke — a bug)"
  for name in gateNames do
    match results.find? fun (n, _, _) => n == name with
    | some (_, code, _) =>
        if code != 0 then
          IO.eprintln s!"gates all: {name} FAILED (exit {code})"
          return code
    | none =>
        IO.eprintln s!"gates all: {name} NEVER RAN (the dispatch's coherence broke)"
        return 1
  IO.println s!"gates all: clean ({((← IO.monoMsNow) - t0) / 1000}s total — the warm env paid ONCE)"
  return 0

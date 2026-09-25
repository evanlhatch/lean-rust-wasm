/-
# GatesTests — the impact-aware gating core's test battery
(Kit.Gates.Impact, notes/v3/09-gates-ops.md §6)

Positive pins + the MANDATORY negative controls (15-patterns #5); the
runner is TestingKit's (`mainOfSuites`). All faces here are PURE over
fixture scans + fixture ledgers (the IO driver's shell-outs are
exercised by `just impacted` itself, not by this battery). Suites:

1. `the module closure walks the import graph` — a change to the
   deepest fixture module propagates through TWO import steps
   (Core ← Util ← Main), the affected artifacts ride the ledger's
   forward query over the AFFECTED names (the rows face AND the
   collection-enumeration face), the gate face selects the env-replay
   gates + the artifact gates; the negative controls are the full-run
   degeneration and the unrelated module swept in.
2. `the widening teeth` — EVERY gap widens to the safe full run: the
   failed scan, the unknown ledger, the changed source outside the
   scanned graph, the untracked non-module path, the dangling project
   import; the notes face stays narrow and runs docs-check; the
   negative controls are a clean module widening and the widen reason
   going silent.
3. `the conservatism theorems' computed teeth` — the fuel honesty (a
   zero-fuel sweep under-reports the importer — the premise is REAL,
   which is why the caller pins N = |modules|), the fuel-2 sweep
   reaching the two-step importer; the negative controls reverse both.
4. `the artifact face's composed conservatism` — Kit.Ledger's proved
   faces lifted over the name fold: the rows face, the collection-
   growth face; the negative controls are the missed reader/enumerator.
5. `the gate coverage data is pinned to the registry` — every coverage
   row names a REGISTERED gate (drift fails the battery), the gated-
   root test consumes Gates.Packages' table (a gated module yes, an
   ungated one no); the negative controls are the unregistered gate
   tolerated and the ungated module gated.
6. `the RSS-bounded pool's teeth` (the wave-30 admission discipline) —
   the budget arithmetic's pins (first lane admits, the 13-lane
   projection refuses, the heavy pairs don't co-run) + the LIVE
   synthetic over-budget pool: 4 sleep-tasks under a one-lane budget
   QUEUE (serial wall, all complete, exit 0 — queued, never dropped,
   never OOM); the negative control runs the same tasks tiny-per-lane
   (parallel wall).
7. `the lint gate's sabotage teeth` (the enforcement wave) — the shard
   verdict over the PLANTED violator (`LintKitFixtures.Violations`)
   MUST fail, the compliant module (`LintKitFixtures.Clean`) MUST pass:
   a gate without its own sabotage row is the finding; plus the nolint
   census scan's pure pins (a planted row MUST count, the row-free
   channel MUST not).

Axiom self-check: `Axioms.lean` (imported below) pins #print axioms
over the pure faces — the core triple or zero, or the build fails.
-/

import Gates
import Gates.Impact
import Gates.Lint
import Gates.LegacyHash
import Gates.NolintCensus
import Gates.Feasibility
import LintKitFixtures.Violations
import LintKitFixtures.Clean
import Kit.Ledger
import TestingKit.Harness
import GatesTests.Axioms

open TestingKit

/-! ## The fixtures -/

/-- One scanned source row, registered under BOTH module-name
    spellings (the scan's own convention — see moduleNamesOfPath). -/
def scanRow (path : String) (imports : List String) : List (String × List String) :=
  (Gates.Impact.moduleNamesOfPath path).map fun m => (m, imports)

/-- The fixture import scan: Core ← Util ← Main (two import steps),
    an unrelated module, and an external ghost import. -/
def fixtureScan : Gates.Impact.ImportScan :=
  { graph :=
      scanRow "zset/ZSet/Core.lean" [] ++
      scanRow "app/App/Util.lean" ["ZSet.Core"] ++
      scanRow "app/App/Main.lean" ["App.Util"] ++
      scanRow "other/Unrelated.lean" [] ++
      scanRow "app/App/Lib.lean" ["Ext.Ghost"]
  , dangling := [] }

/-- The fixture ledger: one row DEMANDING `App.Util` (the rows face),
    one row merely ENUMERATING `ZSet.Core` (the collection face). -/
def fixtureLedger : List Kit.Ledger.LedgerRow :=
  [ { path := "gen/util.rs", emitter := "fixture-emitter"
      demand := { rows := [Kit.Ledger.namesOf "App.Util"]
                , collections := [], emitterRev := "r1" }
      contentHash := 1, obligations := [] }
  , { path := "gen/core-coll.rs", emitter := "fixture-emitter"
      demand := { rows := []
                , collections := [Kit.Ledger.namesOf "ZSet.Core"], emitterRev := "r1" }
      contentHash := 2, obligations := [] } ]

/-- The full-run reason, if the verdict widened. -/
def verdictFull? : Gates.Impact.Verdict → Option String
  | .full why => some why
  | .affected _ _ _ => none

/-! ## 1. The module closure's pins -/

def closureSpecs : List Spec :=
  [ Spec.ofList "the module closure walks the import graph"
      (fun _ => do
        let v := Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
          ["zset/ZSet/Core.lean"]
        match v with
        | .full why =>
            assert false s!"the known change widened to the full run: {why}"
        | .affected mods arts gates => do
            -- the two-step import walk
            assert (mods.contains "ZSet.Core") "the changed module itself is missing"
            assert (mods.contains "App.Util")
              "the one-step importer is missing"
            assert (mods.contains "App.Main")
              "the TWO-step importer is missing — the closure stopped early"
            assert (!(mods.contains "Unrelated"))
              "the unrelated module was swept in (over-widening)"
            -- the artifact face: the forward query over the AFFECTED names
            assert (arts.contains "gen/util.rs")
              "the artifact demanding an AFFECTED module is missing (the rows face)"
            assert (arts.contains "gen/core-coll.rs")
              "the artifact enumerating a CHANGED collection is missing (the growth face)"
            -- the gate face
            assert (gates.contains "axioms") "the env-replay gates are missing"
            assert (gates.contains "gen-check") "the artifact gates are missing")
      [ ("the closure must degenerate to the full run", fun _ =>
          match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
              ["zset/ZSet/Core.lean"] with
          | .full _ => assert true ""
          | .affected _ _ _ => assert false "the closure stayed narrow")
      , ("the unrelated module must be swept in", fun _ =>
          match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
              ["zset/ZSet/Core.lean"] with
          | .affected mods _ _ =>
              assert (mods.contains "Unrelated") "the unrelated module stayed out"
          | .full _ => assert false "the verdict widened")
      ] 1 42
  , Spec.ofList "the empty change set moves nothing (the honest vacuity)"
      (fun _ => do
        let v := Gates.Impact.analyze (some fixtureScan) (some fixtureLedger) []
        match v with
        | .affected mods arts gates => do
            assertEq "affected modules" mods.length 0
            assertEq "affected artifacts" arts.length 0
            assertEq "affected gates" gates.length 0
        | .full why => assert false s!"the empty change set widened: {why}")
      [ ("the empty change set must widen", fun _ =>
          match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger) [] with
          | .full _ => assert true ""
          | .affected _ _ _ => assert false "the verdict stayed narrow")
      , ("the empty change set must select gates", fun _ =>
          match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger) [] with
          | .affected _ _ gates => assertEq "gate count" gates.length 1
          | .full _ => assert false "the verdict widened")
      ] 1 42 ]

/-! ## 2. The widening teeth -/

def widenSpecs : List Spec :=
  [ Spec.ofList "every gap widens to the safe full run"
      (fun _ => do
        -- the failed scan
        match Gates.Impact.analyze none (some fixtureLedger)
            ["zset/ZSet/Core.lean"] with
        | .full why =>
            assert (why.contains "unreadable") s!"the failed-scan reason: {why}"
        | .affected _ _ _ =>
            assert false "the failed scan did NOT widen"
        -- the unknown ledger (absent or refused)
        match Gates.Impact.analyze (some fixtureScan) none
            ["zset/ZSet/Core.lean"] with
        | .full why =>
            assert (why.contains "ledger") s!"the unknown-ledger reason: {why}"
        | .affected _ _ _ =>
            assert false "the unknown ledger did NOT widen"
        -- a changed source outside the scanned graph
        match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
            ["nowhere/Nowhere.lean"] with
        | .full why =>
            assert (why.contains "not a scanned module vertex")
              s!"the unvertexed-source reason: {why}"
        | .affected _ _ _ =>
            assert false "the unvertexed source did NOT widen"
        -- an untracked non-module path (no ledger row, no handler face)
        match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
            ["justfile"] with
        | .full why =>
            assert (why.contains "justfile") s!"the untracked-path reason: {why}"
        | .affected _ _ _ =>
            assert false "the untracked path did NOT widen"
        -- the dangling project import (the graph's naming gap)
        let gappy : Gates.Impact.ImportScan := { fixtureScan with dangling := ["App.Ghost"] }
        match Gates.Impact.analyze (some gappy) (some fixtureLedger)
            ["zset/ZSet/Core.lean"] with
        | .full why =>
            assert (why.contains "naming gap") s!"the dangling-import reason: {why}"
        | .affected _ _ _ =>
            assert false "the dangling import did NOT widen")
      [ ("a known module must widen too", fun _ =>
          match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
              ["zset/ZSet/Core.lean"] with
          | .full _ => assert true ""
          | .affected _ _ _ => assert false "the verdict widened")
      , ("the widen reasons must go silent", fun _ =>
          match Gates.Impact.analyze none (some fixtureLedger)
              ["zset/ZSet/Core.lean"] with
          | .full why => assert (why == "") "the reason was rendered"
          | .affected _ _ _ => assert false "the verdict stayed narrow")
      ] 1 42
  , Spec.ofList "the notes face stays narrow and runs docs-check"
      (fun _ => do
        let v := Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
          ["notes/design-something.md"]
        match v with
        | .full why => assert false s!"the notes change widened: {why}"
        | .affected _ _ gates =>
            assertEq "gates" gates ["docs-check"])
      [ ("the notes face must widen", fun _ =>
          match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
              ["notes/design-something.md"] with
          | .full _ => assert true ""
          | .affected _ _ _ => assert false "the verdict stayed narrow")
      , ("the notes face must run every gate", fun _ =>
          match Gates.Impact.analyze (some fixtureScan) (some fixtureLedger)
              ["notes/design-something.md"] with
          | .affected _ _ gates => assertEq "gate count" gates.length 3
          | .full _ => assert false "the verdict widened")
      ] 1 42 ]

/-! ## 3. The module face's computed teeth (the fuel honesty) -/

/-- The fixture's reverse graph (the specs' shared value). -/
def revOfFixture : ZSet.Graph Bool Nat :=
  Gates.Impact.revGraphOf fixtureScan

def fuelSpecs : List Spec :=
  [ Spec.ofList "the closure's fuel honesty (the conservatism premise is REAL)"
      (fun _ => do
        let rev := Gates.Impact.revGraphOf fixtureScan
        let verts := Gates.Impact.vertTable fixtureScan
        match Gates.Impact.indexOf? verts "ZSet.Core",
              Gates.Impact.indexOf? verts "App.Util",
              Gates.Impact.indexOf? verts "App.Main" with
        | some iCore, some iUtil, some iMain => do
            -- fuel 0: only the changed vertex itself
            assert (!(Gates.Impact.closureIdxs rev 0 [iCore]).contains iUtil)
              "fuel 0 reached the importer — the fuel premise is fiction"
            assert ((Gates.Impact.closureIdxs rev 0 [iCore]).contains iCore)
              "fuel 0 dropped the changed vertex itself"
            -- fuel 2: the two-step importer
            assert ((Gates.Impact.closureIdxs rev 2 [iCore]).contains iUtil)
              "fuel 2 missed the one-step importer"
            assert ((Gates.Impact.closureIdxs rev 2 [iCore]).contains iMain)
              "fuel 2 missed the TWO-step importer"
        | _, _, _ => assert false "the fixture vertices are missing")
      [ ("fuel 0 must reach the importer", fun _ =>
          match Gates.Impact.indexOf? (Gates.Impact.vertTable fixtureScan) "ZSet.Core",
                Gates.Impact.indexOf? (Gates.Impact.vertTable fixtureScan) "App.Util" with
          | some iCore, some iUtil =>
              assert ((Gates.Impact.closureIdxs revOfFixture 0 [iCore]).contains iUtil)
                "fuel 0 did not reach the importer"
          | _, _ => assert false "the fixture vertices are missing")
      , ("the closure must drop its own changed vertex", fun _ =>
          match Gates.Impact.indexOf? (Gates.Impact.vertTable fixtureScan) "ZSet.Core" with
          | some iCore =>
              assert (!(Gates.Impact.closureIdxs revOfFixture 2 [iCore]).contains iCore)
                "the changed vertex stayed in"
          | none => assert false "the fixture vertex is missing")
      ] 1 42 ]

/-! ## 4. The artifact face's composed conservatism -/

def artifactSpecs : List Spec :=
  [ Spec.ofList "the ledger's forward faces, lifted over the name fold"
      (fun _ => do
        -- the rows face: the artifact DEMANDING the changed name
        let rowsFace := Gates.Impact.affectedArtifacts fixtureLedger
          [Kit.Ledger.namesOf "App.Util"] [Kit.Ledger.namesOf "App.Util"]
        assert (rowsFace.any fun a => a.path == "gen/util.rs")
          "the rows face missed its reader"
        -- the collection-growth face: the artifact ENUMERATING the changed name
        let growthFace := Gates.Impact.affectedArtifacts fixtureLedger
          [Kit.Ledger.namesOf "ZSet.Core"] [Kit.Ledger.namesOf "ZSet.Core"]
        assert (growthFace.any fun a => a.path == "gen/core-coll.rs")
          "the growth face missed its enumerator"
        -- an unrelated name moves nothing
        let quiet := Gates.Impact.affectedArtifacts fixtureLedger
          [Kit.Ledger.namesOf "No.Relation"] [Kit.Ledger.namesOf "No.Relation"]
        assert (quiet.isEmpty) "an unrelated name moved artifacts")
      [ ("the rows face must miss its reader", fun _ =>
          assert (!(Gates.Impact.affectedArtifacts fixtureLedger
              [Kit.Ledger.namesOf "App.Util"] [Kit.Ledger.namesOf "App.Util"]).any
              fun a => a.path == "gen/util.rs")
            "the rows face caught its reader")
      , ("the growth face must miss its enumerator", fun _ =>
          assert (!(Gates.Impact.affectedArtifacts fixtureLedger
              [Kit.Ledger.namesOf "ZSet.Core"] [Kit.Ledger.namesOf "ZSet.Core"]).any
              fun a => a.path == "gen/core-coll.rs")
            "the growth face caught its enumerator")
      ] 1 42 ]

/-! ## 5. The gate coverage data, pinned to the registry -/

def coverageSpecs : List Spec :=
  [ Spec.ofList "the gate coverage data is pinned to the registry"
      (fun _ => do
        assert (Gates.Impact.moduleGates.all (· ∈ Gates.gateNames))
          "a module-coverage gate is not a registered row"
        assert (Gates.Impact.artifactGates.all (· ∈ Gates.gateNames))
          "an artifact-coverage gate is not a registered row"
        assert (Gates.Impact.notesGates.all (· ∈ Gates.gateNames))
          "a notes-coverage gate is not a registered row"
        -- the gated-root test consumes Gates.Packages' table
        assert (Gates.Impact.moduleIsGated "ZSet.Core")
          "a ZSet module is under a gated root"
        assert (Gates.Impact.moduleIsGated "ZSet") "the ZSet root itself is gated"
        -- the completed table gates the NEWEST lanes too (the re-audit's
        -- single-source finding): the inspector was once the ungated
        -- witness — now a synthetic name is the only honest ungated face
        assert (Gates.Impact.moduleIsGated "Inspector.Main")
          "the inspector IS a gated package now (the completed table)"
        assert (!(Gates.Impact.moduleIsGated "Ghost.Root"))
          "a synthetic root stays ungated")
      [ ("an unregistered gate name must be tolerated", fun _ =>
          assert (!Gates.Impact.moduleGates.all (· ∈ Gates.gateNames))
            "every coverage name is registered")
      , ("the gated module must read ungated (the sabotage)", fun _ =>
          assert (!(Gates.Impact.moduleIsGated "Inspector.Main"))
            "the gated module read ungated")
      ] 1 42 ]

/-! ## The gate-row honesty scan's teeth (the D33 durable fix) -/

/-- The gated-name set as the scanner consumes it (two real rows;
    `Ghost` stays OUT — the true-claim control's ungated witness). -/
def gateRowDirs : Array String := #["Kit", "ZSet"]

def gateRowSpecs : List Spec :=
  [ Spec.ofList "the planted false gate-row claim fires"
      (fun _ => do
        -- THE PLANT: a header claiming a GATED library is outside the
        -- set — the exact class the header-corrections wave remediated.
        -- The parts are `++`-split SO THE SOURCE TEXT ITSELF does not
        -- contain the claim pattern — this file is inside the scan's
        -- file set, and a lint must not fire on its own teeth.
        let planted := "- gate row: none yet — Kit is " ++
          "outside Gates.Packages' gated set;"
        let found := Gates.DocsCheck.gateRowClaims gateRowDirs planted
        assert (found.size == 1) s!"the plant must fire once, got {found.size}"
        match found[0]? with
        | some (ln, lib) =>
            assertEq "the claimed lib" lib "Kit"
            assertEq "the claim's line" ln 1
        | none => assert false "the plant did not fire"
        -- the honest controls (the true-claim + prose forms must pass):
        let ghost := Gates.DocsCheck.gateRowClaims gateRowDirs
          "Ghost is not in Gates.Packages' gated set"
        assert ghost.isEmpty "the true claim fired"
        let frag := Gates.DocsCheck.gateRowClaims gateRowDirs
          "the field type is outside the supported fragment"
        assert frag.isEmpty "the fragment prose fired"
        let cone := Gates.DocsCheck.gateRowClaims gateRowDirs
          "the root `root` is not in the cone table"
        assert cone.isEmpty "the cone-table prose fired"
        -- the remaining covered forms (multi-line + not-yet + itself):
        let multi := Gates.DocsCheck.gateRowClaims gateRowDirs
          ("Gate row: none — ZSet\n   is " ++ "not in Gates.Packages' gated set")
        assert (multi.size == 1) s!"the multi-line claim: {multi.size} fires"
        assert (multi.all (fun p => p.2 == "ZSet")) "the multi-line: wrong lib"
        let itself := Gates.DocsCheck.gateRowClaims gateRowDirs
          ("none directly — Kit itself is " ++
            "not yet in Gates.Packages' gated set")
        assert (itself.size == 1) s!"the itself-backstep: {itself.size} fires"
        assert (itself.all (fun p => p.2 == "Kit")) "the itself-backstep: wrong lib")
      [ ("the plant must NOT fire (the sabotage)", fun _ => do
          let planted := "- gate row: none yet — Kit is " ++
            "outside Gates.Packages' gated set;"
          let found := Gates.DocsCheck.gateRowClaims gateRowDirs planted
          assert found.isEmpty "the plant fired (it must not)")
      , ("the plant's subject is misread (the sabotage)", fun _ => do
          let planted := "- gate row: none yet — Kit is " ++
            "outside Gates.Packages' gated set;"
          let found := Gates.DocsCheck.gateRowClaims gateRowDirs planted
          assert (found.all (fun p => p.2 == "ZSet"))
            "the subject read as Kit (it must read as ZSet)")
      , ("the prose controls fire too (the sabotage)", fun _ => do
          let frag := Gates.DocsCheck.gateRowClaims gateRowDirs
            "the field type is outside the supported fragment"
          assert (!frag.isEmpty) "the fragment prose did NOT fire")
      ] 1 42 ]

/-! ## The kernel-check verdict classifier's teeth -/

/-- The planted rejection (a "found a problem" output outside the
    known gaps) MUST classify REJECTED — the gate's failure face; the
    negative control is the same output on a DISCLOSED gap module
    (classified gap, not a failure) and the clean/signal faces. -/
def classifySpecs : List Spec :=
  [ Spec.ofList "the kernel-check verdict classifier (the gate's teeth)"
      (fun _ => do
        let rejection := "lean4lean found a problem in Fake.Mod:\n  (kernel) deterministic timeout"
        -- the planted rejection: REJECTED (the gate fails on it)
        match Gates.KernelCheck.classify `Fake.Mod 1 false 300 rejection with
        | .rejected _ => assert true ""
        | v => assert false s!"the planted rejection classified {v.render}"
        -- the SAME output on a disclosed gap module: gap, not a failure
        match Gates.KernelCheck.classify `SchemaCore.Goldens 1 false 300 rejection with
        | .gap => assert true ""
        | v => assert false s!"the disclosed gap classified {v.render}"
        -- the clean face
        match Gates.KernelCheck.classify `Fake.Mod 0 false 300 "checked 3 declarations" with
        | .ok => assert true ""
        | v => assert false s!"the clean exit classified {v.render}"
        -- a signal exit / a budget kill: UNKNOWN (never a verdict, never silent)
        match Gates.KernelCheck.classify `Fake.Mod 143 false 300 "" with
        | .unknown _ => assert true ""
        | v => assert false s!"the signal exit classified {v.render}"
        match Gates.KernelCheck.classify `Fake.Mod 143 true 300 "" with
        | .unknown why => assert (why.contains "budget") s!"{why}"
        | v => assert false s!"the budget kill classified {v.render}")
      [ ("the planted rejection must NOT classify rejected (the sabotage)", fun _ => do
          match Gates.KernelCheck.classify `Fake.Mod 1 false 300
              "lean4lean found a problem in Fake.Mod: boom" with
          | .rejected _ => assert false "the rejection was caught"
          | _ => assert true "")
      , ("the clean exit must NOT classify ok (the sabotage)", fun _ => do
          match Gates.KernelCheck.classify `Fake.Mod 0 false 300 "checked 3 declarations" with
          | .ok => assert false "the clean face was caught"
          | _ => assert true "")
      ] 1 42 ]

/-! ## The RSS-bounded pool's teeth (the wave-30 admission discipline) -/

/-- The admission predicate's teeth (PURE — the budget's arithmetic).
    The LIVE over-budget queueing face is `livePoolTeeth` (below): the
    battery's faces are pure, and queueing needs a real child process. -/
def rssSpecs : List Spec :=
  [ Spec.ofList "the RSS admission predicate (the budget's arithmetic)"
      (fun _ => do
        -- a fresh pool always admits its first lane
        assert (Gates.rssAdmits 18000 1024 0)
          "the first lane was refused — pools would deadlock"
        -- the homogeneous projection: 2 lanes of 1.5GB + margin fits
        -- 18GB, 13 do not
        assert (Gates.rssAdmits 18000 1024 (1536 * 2))
          "two 1.5GB lanes must fit an 18GB budget"
        assert (!(Gates.rssAdmits 18000 1024 (1536 * 13)))
          "thirteen 1.5GB lanes must NOT fit an 18GB budget"
        -- the heterogeneous projection (runAll's shape): two heavy
        -- gates do not co-run, heavy + light does
        assert (!(Gates.rssAdmits 18000 1024 (16384 + 15360)))
          "the two 16GB-class gates must not co-run"
        assert (!(Gates.rssAdmits 18000 1024 (16384 + 2048)))
          "a 16GB gate + a 2GB gate must not co-run"
        assert (Gates.rssAdmits 18000 1024 (15360 + 1024))
          "kernel-check + one light gate must co-run")
    [ ("the first lane must be refuseable too (the sabotage)", fun _ =>
        assert (!Gates.rssAdmits 1 1 0) "the empty pool admitted under a 1MB budget")
    , ("the over-budget projection must slip through (the sabotage)", fun _ =>
        assert (Gates.rssAdmits 18000 1024 (1536 * 13))
          "the 13-lane projection was refused")
    ] 1 42 ]

/-- The LIVE pool teeth (the pure battery's ONE IO face — queueing
    needs a real child process): 4 sleep-tasks under a budget that
    admits ONE 4096MB lane must QUEUE — serial wall (≥ the sum of the
    sleeps), every task completes with exit 0 (queued, never dropped,
    never OOM'd); the control runs the same tasks at a tiny per-lane
    cost — the 8 count-cap lanes go parallel, wall strictly under the
    serial bound. Returns none on pass, the failure's evidence on
    fail. -/
def livePoolTeeth : IO (Option String) := do
  let tasks : Array Gates.PkgSpec :=
    Array.replicate 4 { dir := "t", srcDir := ".", roots := #[] }
  -- the over-budget run: one lane → serial
  let t0 ← IO.monoMsNow
  let outs ← Gates.pkgPool (fun _ => "sleep") (fun _ => #["0.3"])
    tasks 8 4096 5000 512
  let serialMs := (← IO.monoMsNow) - t0
  if outs.size != 4 then return some s!"task count {outs.size} ≠ 4 (a task dropped)"
  for (code, _) in outs do
    if code != 0 then return some s!"a queued task failed (exit {code})"
  if serialMs < 1100 then
    return some s!"the over-budget pool ran in parallel ({serialMs}ms) — no queueing, the OOM shape"
  -- the control: tiny per-lane cost → parallel
  let t1 ← IO.monoMsNow
  let outs ← Gates.pkgPool (fun _ => "sleep") (fun _ => #["0.3"])
    tasks 8 1 5000 512
  let parMs := (← IO.monoMsNow) - t1
  if outs.size != 4 then return some s!"control task count {outs.size} ≠ 4"
  for (code, _) in outs do
    if code != 0 then return some s!"a control task failed (exit {code})"
  if parMs ≥ 1100 then
    return some s!"the under-budget pool serialized ({parMs}ms) — the admission is fiction"
  IO.println s!"GatesTests: live pool teeth — over-budget serial {serialMs}ms, control parallel {parMs}ms (queueing verified)"
  return none

/-! ## The lint gate's sabotage teeth (the enforcement wave) -/

/-- The LINT gate's live sabotage: `Gates.Lint.runPkg` (the gate row's
own shard body) over the planted violator MUST exit 1 (a finding the
row cannot silence); the negative control is a REAL gated root — the
LintKit package, whose tree-lint cleanness the row itself demands —
MUST exit 0. (The `Clean` fixture is NOT the control: its own
`set_option` snapshots enable the census linters on its decls — the
LintKitTests fixture pins own that face.) Returns none on pass, the
evidence on fail. -/
unsafe def lintGateTeeth : IO (Option String) := do
  let violator : Gates.PkgSpec :=
    { dir := "LintKitFixtures", srcDir := "lintkit",
      roots := #[`LintKitFixtures.Violations] }
  let clean : Gates.PkgSpec :=
    { dir := "LintKit", srcDir := "lintkit", roots := #[`LintKit] }
  let vc ← Gates.Lint.runPkg violator
  if vc != 1 then
    return some s!"the planted violator PASSED the lint shard (exit {vc}) — the gate is fiction"
  let cc ← Gates.Lint.runPkg clean
  if cc != 0 then
    return some s!"the clean gated root FAILED the lint shard (exit {cc}) — the negative control is broken"
  IO.println "GatesTests: lint gate teeth — the violator fails, the clean root passes"
  return none

/-- The nolint census scan's pure pins: the planted rows count per
linter, the comment/string channels never count (the negative controls
are the sabotage rows). -/
def nolintScanSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList
      "the nolint census scan (the enforcement wave's drift teeth)"
      (fun _ => do
        -- a planted row counts, per linter
        assert (Gates.NolintCensus.fileNolints
          "@[nolint linter.guestlang.zeroCitation \"why\"]\ndef x := 1\n"
          == #[`linter.guestlang.zeroCitation])
          "the planted zeroCitation row did not count"
        -- the multi-linter row counts each
        assert (Gates.NolintCensus.fileNolints
          "@[nolint linter.guestlang.a linter.guestlang.b \"why\"]\n"
          == #[`linter.guestlang.a, `linter.guestlang.b])
          "the multi-linter row under-counted"
        -- the mount derivation rides the table row
        assert (Gates.Lint.srcRootsFor
          { dir := "Kit", srcDir := "kit", roots := #[`Kit] }
          == #[(Lean.Name.mkSimple "Kit", "kit")])
          "the mount derivation drifted from the table row")
      [ ("a comment row counts (the sabotage — the mutant scanner)", fun _ =>
          assert (Gates.NolintCensus.fileNolints
            "-- @[nolint linter.guestlang.a \"why\"]\ndef x := 1\n"
            == #[`linter.guestlang.a])
            "a comment row was NOT counted (the channels hold)")
      , ("a string-literal row counts (the sabotage — the mutant scanner)", fun _ =>
          assert (Gates.NolintCensus.fileNolints
            "def m := s!\"opt out with @[nolint linter.guestlang.a]\"\n"
            == #[`linter.guestlang.a])
            "a string-literal row was NOT counted (the channels hold)")
      ] 1 42 ]

/-! ## The gen-check tie's sabotage teeth (the enforcement wave's gap 6) -/

/-- The drifted face's ONE projection (ByteTie's ctor match — the verdict
vocabulary has no Bool face). -/
def driftedT : TestingKit.Golden.ByteTie → Bool
  | .drifted _ => true
  | .tied => false

/-- The BYTE-TIE verdict's sabotage: the gate's REAL compare functions
(`Kit.Emit.tieText`/`tieBytes` — the gen-check verdict's ONE copy) over
a planted tamper. A tampered body MUST drift; the tampered content-hash
sidecar MUST drift; the in-sync faces MUST tie (the mandatory negative
controls). The planted faces live in the defs above (the do block's
explicit `pure ()` tail — the spec prop's do needs the non-assert
terminator, the parser's honest shape). -/
def genTieBody : String := "body"

def genTieCommitted : String :=
  s!"// GENERATED by e DO NOT EDIT\n// content-hash {toString genTieBody.hash}\n{genTieBody}"

def genTieTampered : String := "tampered"

def genTieHeaderless : String := "no header here"

def b12 : ByteArray := ByteArray.mk #[1, 2]

def b13 : ByteArray := ByteArray.mk #[1, 3]

def genTieSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList
      "the byte-tie verdict's sabotage teeth (the gen-check gate)"
      (fun _ => do
        -- the positive controls: the in-sync faces tie
        assert (!(driftedT (Kit.Emit.tieText genTieCommitted genTieBody)))
          "an in-sync text tie drifted"
        assert (!(driftedT (Kit.Emit.tieBytes s!"// h {toString (Kit.Emit.bytesHash b12)}" b12 b12)))
          "an in-sync byte tie drifted"
        -- the sabotage: a TAMPERED BODY must drift (the byte-tie's whole
        -- point — a hand-edited artifact cannot pass)
        assert (driftedT (Kit.Emit.tieText genTieCommitted genTieTampered))
          "a tampered text body TIED — the byte-tie is fiction"
        assert (driftedT (Kit.Emit.tieBytes s!"// h {toString (Kit.Emit.bytesHash b12)}" b12 b13))
          "tampered bytes TIED — the binary tie is fiction"
        -- the sabotage: a STALE SIDECAR HASH must drift
        assert (driftedT (Kit.Emit.tieBytes "// h 999" b12 b12))
          "a stale sidecar hash TIED — the sidecar's own hash check is fiction"
        -- the sabotage: a HEADERLESS committed file must drift
        assert (driftedT (Kit.Emit.tieText genTieHeaderless genTieHeaderless))
          "a headerless artifact TIED — the one-writer rule's face is fiction"
        pure ())
      [ ("a tampered body must slip through (the sabotage)", fun _ => do
          assert (!(driftedT (Kit.Emit.tieText genTieCommitted genTieTampered)))
            "the tampered body drifted (the verdict holds)")
      , ("a stale sidecar hash must slip through (the sabotage)", fun _ => do
          assert (!(driftedT (Kit.Emit.tieBytes "// h 999" b12 b12)))
            "the stale sidecar drifted (the verdict holds)")
      ] 1 42 ]

/-! ## The legacy-hash row's sabotage teeth (B4: the read-only tooth) -/

/-- The legacy-immutability HASH's sensitivity: a content tamper, a
path rename, an added file and a dropped file each MUST change the
surface (the mutant hasher's controls); the row render is per-file
(the drift names its file). -/
def legacyHashSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList
      "the legacy-immutability hash's sabotage teeth (the B4 row)"
      (fun _ => do
        -- the positive control: the same file hashes identically
        assert (Gates.LegacyHash.rowOf "a.lean" "x"
            == Gates.LegacyHash.rowOf "a.lean" "x")
          "the identical file hashed differently (the hash is unstable)"
        -- the sabotage: a CONTENT tamper changes the row (the mutant
        -- hasher that ignores bytes is the fiction)
        assert (Gates.LegacyHash.rowOf "a.lean" "x"
            != Gates.LegacyHash.rowOf "a.lean" "y")
          "a content tamper did NOT change the row — the hash is fiction"
        -- the sabotage: a PATH rename changes the row (the mutant
        -- hasher that ignores paths misses a moved file)
        assert (Gates.LegacyHash.rowOf "a.lean" "x"
            != Gates.LegacyHash.rowOf "b.lean" "x")
          "a path rename did NOT change the row — the hash is fiction"
        -- the aggregate face: an ADDED file and a DROPPED file each
        -- change the surface
        let one := Gates.LegacyHash.renderSurface [("a", "x")]
        let two := Gates.LegacyHash.renderSurface [("a", "x"), ("b", "y")]
        let dropped := Gates.LegacyHash.renderSurface [("a", "x"), ("a2", "z")]
        assert (one != two)
          "an added file did NOT change the surface — the walk is fiction"
        assert (two != dropped)
          "a dropped file did NOT change the surface — the walk is fiction"
        -- the render is per-file rows (the drift NAMES its file)
        assert ((Gates.LegacyHash.renderSurface [("a", "x")]).endsWith
          (Gates.LegacyHash.rowOf "a" "x" ++ "\n"))
          "the render lost the per-file row shape"
        pure ())
      [ ("a content tamper must slip through (the sabotage)", fun _ =>
          assert (Gates.LegacyHash.rowOf "a.lean" "x"
              == Gates.LegacyHash.rowOf "a.lean" "y")
            "the content tamper changed the row (the verdict holds)")
      , ("a path rename must slip through (the sabotage)", fun _ =>
          assert (Gates.LegacyHash.rowOf "a.lean" "x"
              == Gates.LegacyHash.rowOf "b.lean" "x")
            "the path rename changed the row (the verdict holds)")
      , ("a dropped file must slip through (the sabotage)", fun _ =>
          assert (Gates.LegacyHash.renderSurface [("a", "x"), ("b", "y")] ==
              Gates.LegacyHash.renderSurface [("a", "x"), ("a2", "z")])
            "the dropped file changed the surface (the verdict holds)") ]
    1 42 ]

/-! ## The feasibility row's gate-level teeth (B2: the spec-sanity
    census) — the census DATA's pins over the gate's own surface (the
    full discipline suite — the verdict cells, the render drift, the
    unforgeability — lives on the discipline's own cone:
    ContractsTests.Feasibility; the GatesTests root is C0 machinery and
    stays import-clean of it, LintKit.Cone's table). -/

/-- The B2 gate-level teeth: the REAL census consumes the discipline —
the counts are pinned, no registered spec is unchecked, and the
planted vacuous contract's row is the VISIBLE declared-empty cell
(never a silent pass). All faces here are projections over
`Gates.Feasibility`'s own census — no direct import of the discipline
module (the cone table's C0 discipline). -/
def feasSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList
      "the feasibility row's gate-level teeth (the B2 row: the census consumes the discipline)"
      (fun _ => do
        -- the counts are pinned (6 registered specs: 4 feasible,
        -- 2 declared-empty, 0 unchecked)
        let (n, feas, decl, unch) := Gates.Feasibility.counts Gates.Feasibility.census
        assert (n == 6) s!"the feasibility census drifted: {n} rows"
        assert (feas == 4) s!"the feasibility census drifted: {feas} feasible rows"
        assert (decl == 2) s!"the feasibility census drifted: {decl} declared-empty rows"
        assert (unch == 0)
          "an UNCHECKED registered spec — the warning is data; re-adjudicate and re-baseline"
        -- THE PLANTED VACUOUS CONTRACT IS CAUGHT: its census row exists,
        -- is NOT a checked (passing) verdict, and renders the DECLARED
        -- cell — visible, never a silent pass
        match Gates.Feasibility.census.find? fun r => r.name.startsWith "vacuousC" with
        | none => assert false "the planted vacuous contract's row is missing from the census"
        | some r => do
            assert (!(r.verdict.render).startsWith "feasible")
              "the planted vacuous contract's row PASSED — the vacuous success is fiction"
            assert ((r.verdict.render).startsWith "vacuous (DECLARED")
              "the planted vacuous contract's row lost its DECLARED rendering"
            -- and the row's evidence names the no-witness theorem
            assert ((r.verdict.render).contains "vacuousC_no_witness")
              "the declared-empty cell lost its no-witness citation"
        pure ())
      [ ("the planted vacuous contract's row must pass (a LIE — caught)", fun _ =>
          match Gates.Feasibility.census.find? fun r => r.name.startsWith "vacuousC" with
          | none => assert false "the control demands the row be present"
          | some r =>
              assert ((r.verdict.render).startsWith "feasible")
                "the control demands the vacuous contract's row pass as feasible")
      , ("the unchecked WARNING must fire (a LIE — caught)", fun _ =>
          assert (Gates.Feasibility.census.any fun r =>
              (r.verdict.render).startsWith "WARNING")
            "the control demands an unchecked row be present")
      ]
    1 42 ]

/-! ## The audit gate's coverage-row teeth (wave-30 C1: the
    observability-inheritance rule, 09 §5 — generated host code without
    span coverage FAILS; the fault surface rides the error! face) -/

/-- The span-coverage row, pulled from the LIVE table (the teeth ride
    the real rules, never a fixture copy). -/
def spanRule? : Option Gates.Audit.AuditRule :=
  (Gates.Audit.coverageRules.find? fun (p, _) =>
    p == "crates/schema-generated/src/lib.rs").map (·.2)

def auditSpecs : List Spec :=
  [ Spec.ofList "the coverage rows are REQUIRED and targeted (the \
      observability-inheritance rule lands as data)"
      (fun _ => do
        match spanRule? with
        | none =>
            TestingKit.assert false
              "the span-coverage row must be in the live table"
        | some rule =>
            TestingKit.assert rule.required
              "the span-coverage row is a required rule"
            TestingKit.assertEq "the rule's name" rule.name "span-coverage"
            TestingKit.assertEq "the coverage table's rows"
              Gates.Audit.coverageRules.length 2
            -- the marker PRESENT is clean (the required rule's quiet face)
            TestingKit.assert
              ((Gates.Audit.auditFindings [rule]
                  "pub fn encode_scope() { fast_observe::scope!(S) }").isEmpty)
              "the marker present must yield no finding")
      [ ("the missing marker must pass (a LIE — caught)", fun _ => do
          match spanRule? with
          | none => pure ()
          | some rule =>
              TestingKit.assert
                ((Gates.Audit.auditFindings [rule] "no marker here").isEmpty)
                "the control demands the markerless artifact to pass")
      , ("the banned pattern must be tolerated (a LIE — caught)", fun _ =>
          TestingKit.assert
            ((Gates.Audit.auditFindings Gates.Audit.auditRules
                "let x = unwrap(y)").isEmpty)
            "the control demands the banned pattern to pass")
      ] 1 42 ]

/-! ## The driver -/

unsafe def main : IO UInt32 := do
  let code ← TestingKit.mainOfSuites
    [ ("the impact-aware gating core (09 §6)", closureSpecs ++ widenSpecs ++ fuelSpecs
        ++ artifactSpecs ++ coverageSpecs)
    , ("the gate-row honesty scan's teeth (the D33 durable fix)", gateRowSpecs)
    , ("the kernel-check verdict classifier's teeth (the budget discipline)", classifySpecs)
    , ("the RSS-bounded pool's teeth (the wave-30 admission discipline)", rssSpecs)
    , ("the lint gate's sabotage teeth (the enforcement wave)", nolintScanSpecs)
    , ("the gen-check tie's sabotage teeth (the enforcement wave's gap 6)", genTieSpecs)
    , ("the legacy-hash row's sabotage teeth (B4: the read-only tooth)", legacyHashSpecs)
    , ("the feasibility row's sabotage teeth (B2: the spec-sanity census)", feasSpecs)
    , ("the audit gate's coverage-row teeth (wave-30 C1)", auditSpecs) ]
  if code != 0 then return code
  -- the live pool teeth: the pure battery's one IO exception (above)
  match ← livePoolTeeth with
  | none => pure ()
  | some e =>
      IO.eprintln s!"GatesTests: the live pool teeth FAILED — {e}"
      return 1
  -- the lint gate's live sabotage (the enforcement wave)
  match ← lintGateTeeth with
  | none => return 0
  | some e =>
      IO.eprintln s!"GatesTests: the live pool teeth FAILED — {e}"
      return 1

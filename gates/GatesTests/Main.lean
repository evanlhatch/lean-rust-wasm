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

Axiom self-check: `Axioms.lean` (imported below) pins #print axioms
over the pure faces — the core triple or zero, or the build fails.
-/

import Gates
import Gates.Impact
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

/-! ## The driver -/

unsafe def main : IO UInt32 :=
  TestingKit.mainOfSuites
    [ ("the impact-aware gating core (09 §6)", closureSpecs ++ widenSpecs ++ fuelSpecs
        ++ artifactSpecs ++ coverageSpecs) ]

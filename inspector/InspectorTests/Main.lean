/-
# InspectorTests — the evidence-chain inspector's test battery

Positive pins + the MANDATORY negative controls (15-patterns #5); the
runner is TestingKit's (`mainOfSuites`). Suites:

1. `the replay collects the check lane's rows` — the LIVE replay pins:
   the check lane's two fixture rows, their labels/tiers/provenance/
   payloads exact; the negative controls are the wrong-count and
   wrong-tier expectations.
2. `the why-answer's shape` — the LIVE why-render of a real check-lane
   label: lane/provenance/tier/trust-axes/evidence blocks pinned, the
   LOUD GAP pinned (an undischarged obligation is never omitted); the
   negative controls are the renders that would LIE (a "universal
   proof" line on a per-table claim; a silent discharge).
3. `the trust axes are honest` — the per-tier axis renders over the
   closed tier set: an `oracleSwept` row's strength is a SAMPLED TEST
   and its evidence line says TESTED AGREEMENT — NEVER a proof; the
   negative controls are the lying renders (the pin demands they fail).
4. `the gap-flagging teeth` — the fabricated undischarged row FLAGS
   (GAP), the mis-wired row FLAGS (MISWIRED), the observer-less sweep
   row FLAGS (OBSERVER-MISSING), the honest decided row is clean, and
   the sweep report counts + renders all of it; the negative controls
   are the assertions that the bad rows are clean (the harness demands
   they FAIL — if the flagging broke, the suite goes VACUOUS, louder).
5. `the ledger reading` — the provenance ledger's queries over a
   fixture ledger (Kit.Ledger's data, parsed/printed): the BACKWARD
   demand surface (rows PLUS collections), the FORWARD query's proved
   conservatism (the collection-ENUMERATION artifact is affected by a
   change to the collection it merely enumerated — the demand-set
   correction's face), the ORPHANS (the on-disk squatter with no row),
   the ABSENT state's honest dormancy (never a fabricated clean), the
   selfStable round-trip (a hand-edit fails its own stability check);
   the negative controls are the rows-only under-report, the absent
   state rendering a clean orphan verdict, and the tampered bytes
   passing.
6. `the proof coverage` — who cites a theorem over a FABRICATED census
   (LintKit.Citations' graph shape, as data): the citers listed with
   their modules, the ZERO-citation verdict (the proof-level leftover
   rule), the test pin counting as the citation (the census's second
   medium), the unknown constant's loud miss, the per-library report;
   the negative controls are the same-module citation counting as a
   zero, the pin NOT counting, and the unknown answering as known.
7. `the trust report` — the honesty discipline over the closed tier
   set + the axiom classification: a fabricated `oracleSwept` row's
   distribution line says TESTED AGREEMENT and NEVER renders as a
   universal proof; the outside-allowlist axiom renders as the LOUD
   flag; the duel zero-state says NONE REGISTERED; the negative
   controls are the lying render, the lying classification, and the
   zero-state claiming agreement.
8. `the what-if inspector` — the rewind pin (the state as of
   occurrence t = the prefix's replay = the landed `runStates`), the
   worked what-if's divergence report (diverges at the modification
   point, outcomes pinned), the ORIGINAL-JOURNAL-UNTOUCHED pins (the
   report's original is the fixture byte for byte; the modified stream
   keeps the occurrence identity — the trichotomy's event-identity
   discipline), the net-zero what-if (none, outcomes equal), and the
   mandatory negative controls (an early divergence, a rewritten
   original, a fabricated divergence, a renumbering, an out-of-range
   fabrication).

Axiom self-check: `Axioms.lean` (imported below) pins #print axioms
over the pure rendering faces — zero axioms or the build fails.
-/

import Inspector.Replay
import Inspector.LedgerView
import Inspector.Cites
import Inspector.Trust
import Inspector.WhatIf
import Kit.Ledger
import TestingKit.Harness
import InspectorTests.Axioms

open Lean

open Inspector TestingKit

/-! ## The fabricated fixtures (the teeth's material) -/

/-- An honest closed-claim row: decidableNow + a true decide. -/
def honestDecided : InspRow :=
  { lane := "test"
    label := "test/honest-decided"
    tier := .decidableNow
    provenance := `InspectorTests
    payload := "the honest closed claim"
    observer := none
    eCode := none
    discharge := .discharged (.decided true) }

/-- An honest sweep row: oracleSwept + its observer + the oracle ref. -/
def honestOracle : InspRow :=
  { lane := "test"
    label := "test/honest-oracle"
    tier := .oracleSwept
    provenance := `InspectorTests
    payload := "the sweep's cases"
    observer := some "apiObs"
    eCode := none
    discharge := .discharged (.oracleRow "Duel/seed-42") }

/-- THE FABRICATED UNDISCHARGED ROW: the teeth's target — it must flag. -/
def gapRow : InspRow :=
  { lane := "test"
    label := "test/fabricated-gap"
    tier := .decidableNow
    provenance := `InspectorTests
    payload := "the fabricated gap"
    observer := none
    eCode := none
    discharge := .openGap "fabricated undischarged row (the teeth test)" }

/-- A MIS-WIRED row: decided evidence on an oracleSwept tier. -/
def miswiredRow : InspRow :=
  { honestOracle with discharge := .discharged (.decided true) }

/-- An observer-less sweep row: the 04 §4 flag's target. -/
def observerMissingRow : InspRow :=
  { honestOracle with observer := none }

/-! ## 1. The live replay's pins -/

def liveReplaySpecs (rows : List InspRow) : List Spec :=
  [ Spec.ofList "the replay collects the check lane's rows"
      (fun _ => do
        let ls := rows.map (·.label)
        assertEq "row count" rows.length 2
        assert (ls.contains "schema/Example/example-count-positive")
          s!"missing the passing fixture's row: {ls}"
        assert (ls.contains "schema/Example/example-count-zero")
          s!"missing the violated fixture's row: {ls}"
        for r in rows do
          assertEq "lane" r.lane "check"
          assertEq "tier" r.tier .decidableNow
          assertEq "provenance" r.provenance.toString "SchemaCore"
          assertEq "payload" r.payload
            "ready, count, delta, label, note, tags"
          assert (match r.discharge with | .openGap _ => true | .discharged _ => false)
            s!"the replayed row's discharge must be the honest open gap: {r.label}")
      [ ("wrong count", fun _ => assertEq "row count" rows.length 3)
      , ("wrong tier", fun _ =>
          assert (rows.any (fun r => r.tier == .oracleSwept))
            "a replayed tier drifted to oracleSwept")
      ] 1 42 (h := by simp) ]

/-! ## 2. The why-answer's shape (live) -/

def liveWhySpecs (rows : List InspRow) : List Spec :=
  [ Spec.ofList "the why-answer's shape (a real check-lane label)"
      (fun _ => do
        let r := Inspector.why rows "schema/Example/example-count-positive"
        assert (r.contains "why `schema/Example/example-count-positive`")
          "the why-answer does not name its label"
        assert (r.contains "lane: check") "no lane line"
        assert (r.contains "provenance: SchemaCore") "no provenance line"
        assert (r.contains "tier: decidable-now") "no tier line"
        assert (r.contains "trust axes:") "no trust-axes block"
        assert (r.contains "evidence strength: bounded proof")
          "no honest strength line"
        assert (r.contains "GAP: undischarged")
          "the loud gap was omitted — the why-answer lied by silence"
        assert (r.contains "no universal claim is made")
          "the no-universal-claim disclaimer was omitted"
        -- the loud miss: an unknown label lists the available labels
        let miss := Inspector.why rows "no-such-label"
        assert (miss.contains "NO obligation labeled `no-such-label`")
          "the unknown-label miss was silent"
        assert (miss.contains "schema/Example/example-count-zero")
          "the miss does not list the available labels")
      [ ("the render must not claim a universal proof",
          fun _ => assert
            ((Inspector.why rows "schema/Example/example-count-positive").contains
              "universal proof")
            "the per-table claim rendered as a universal proof")
      , ("the render must not be silent about discharge",
          fun _ => assert
            (!(Inspector.why rows "schema/Example/example-count-positive").contains
              "GAP")
            "the gap was silently dropped")
      ] 1 42 (h := by simp) ]

/-! ## 3. The trust axes' honesty (pure, over the closed tier set) -/

def trustAxisSpecs : List Spec :=
  [ Spec.ofList "the trust axes are honest (an oracleSwept row never renders as a proof)"
      (fun _ => do
        -- the strength axis: sampled test, never "proof"
        let st := trustStrength .oracleSwept
        assert (st.contains "sampled test") s!"the strength line: {st}"
        assert (!(st.contains "proof")) s!"the strength line claims proof: {st}"
        -- the evidence kind line: TESTED AGREEMENT, never a universal theorem
        let kl := evidenceKindLine (.oracleRow "r")
        assert (kl.contains "TESTED AGREEMENT") s!"the kind line: {kl}"
        assert (kl.contains "NOT a proof") s!"the kind line: {kl}"
        assert (!(kl.contains "universal proof")) s!"the kind line claims proof: {kl}"
        -- the decided-true line names the kernel; the guest line names the pin
        assert ((evidenceKindLine (.decided true)).contains "kernel-checked")
          "the decided line does not name the kernel check"
        assert ((evidenceKindLine (.guestWitness "a" "r")).contains
          "identity must be pinned") "the guest line omits the identity pin"
        -- the honest oracle row is clean: observer present, tier matches
        assert honestOracle.isClean
          "the honest oracle row must be defect-free"
        assert (!(honestOracle.renderWhy.contains "FLAG:"))
          "the honest oracle row rendered a flag")
      [ ("the lying strength render", fun _ =>
          assert ((trustStrength .oracleSwept).contains "universal proof")
            "the strength line was honest")
      , ("the lying kind line", fun _ =>
          assert ((evidenceKindLine (.oracleRow "r")).contains "universal proof")
            "the kind line was honest")
      ] 1 42 ]

/-! ## 4. The gap-flagging teeth (pure, fabricated rows) -/

def teethSpecs : List Spec :=
  [ Spec.ofList "the gap-flagging teeth (a fabricated undischarged row flags)"
      (fun _ => do
        -- the loud gap flags
        assert (gapRow.defects.any (·.startsWith "GAP:"))
          "the fabricated undischarged row did not flag GAP"
        assert (!gapRow.isClean) "the gap row rendered clean"
        assert (gapRow.renderWhy.contains "GAP: undischarged")
          "the why-render omitted the gap"
        -- the mis-wire flags (data-level tier check)
        assert (miswiredRow.tierMismatch) "the mis-wired row was not detected"
        assert (miswiredRow.defects.any (·.startsWith "MISWIRED:"))
          "the mis-wired row did not flag MISWIRED"
        -- the observer rule flags (04 §4)
        assert (observerMissingRow.defects.any (·.startsWith "OBSERVER-MISSING:"))
          "the observer-less sweep row did not flag"
        assert (miswiredRow.defects.any (·.startsWith "OBSERVER-MISSING:") |>.not)
          "the observer-bearing row must not flag observer-missing"
        -- the honest decided row is clean
        assert (honestDecided.isClean) "the honest decided row flagged"
        assert (honestDecided.renderWhy.contains
          "decided true — kernel-checked decision")
          "the decided-true evidence line drifted")
      [ ("the gap row must not render clean", fun _ =>
          assert gapRow.isClean "the gap row flagged")
      , ("the mis-wire must not pass silently", fun _ =>
          assert (miswiredRow.defects.isEmpty) "the mis-wire was caught")
      ] 1 42
  , Spec.ofList "the sweep report renders every row + counts the gaps"
      (fun _ => do
        let rep := Inspector.report "test-roots"
          [honestDecided, honestOracle, gapRow]
        assert (rep.contains "3 obligation row(s)") s!"the count line: {rep}"
        assert (rep.contains "[test] test/honest-decided")
          "the decided row's sweep line is missing"
        assert (rep.contains "[test] test/honest-oracle — tier=oracle-swept \
          evidence=oracle row (TESTED AGREEMENT) observer=apiObs")
          "the oracle row's sweep line drifted"
        assert (rep.contains "1 gap(s)") "the gap count drifted"
        assert (rep.contains "1 row(s) flagged") "the flagged count drifted"
        assert (rep.contains "replayed roots: test-roots")
          "the demand-set line is missing"
        assert (rep.contains "the gates' obligation sweep consumes this report")
          "the forward-integration note is missing")
      [ ("the report must not count the gap", fun _ =>
          assert ((Inspector.report "t" [gapRow]).contains "0 gap(s)")
            "the gap was counted")
      , ("the report must not flag the mis-wire", fun _ =>
          assert ((Inspector.report "t" [miswiredRow]).contains "0 row(s) flagged")
            "the mis-wire was flagged")
      ] 1 42 ]

/-! ## 5. The ledger reading (the provenance ledger's queries over the fixture) -/

open Kit.Ledger in
/-- The backward fixture: the artifact's demand names its spec row. -/
def lrWit : LedgerRow :=
  { path := "gen/a.wit", emitter := "wit"
    demand := { rows := [`Schema.Example], collections := [], emitterRev := "rev-1" }
    contentHash := 7, obligations := ["obl/a"] }

open Kit.Ledger in
/-- The ENUMERATION fixture: the artifact's demand names NO spec row —
    it depends on the collection's CONTENTS-AS-A-SET (the demand-set
    correction's whole face). -/
def lrRust : LedgerRow :=
  { path := "gen/b.rs", emitter := "rust"
    demand := { rows := [], collections := [`Schema.Example], emitterRev := "rev-2" }
    contentHash := 9, obligations := [] }

def fixtureLedger : List Kit.Ledger.LedgerRow := [lrWit, lrRust]

def ledgerSpecs : List Spec :=
  [ Spec.ofList "the ledger reading (backward / forward / orphans / dormancy)"
      (fun _ => do
        -- BACKWARD: the artifact's full demand surface
        let (bw, known) := Inspector.LedgerView.backwardAnswer fixtureLedger "gen/a.wit"
        assert known "the tracked artifact answered untracked"
        assert (bw.contains "gen/a.wit ← wit") s!"the backward line: {bw}"
        assert (bw.contains "Schema.Example") "the demand's spec row is missing"
        -- the loud miss
        let (miss, known2) := Inspector.LedgerView.backwardAnswer fixtureLedger "gen/nope.wit"
        assert (!known2 && miss.contains "NO ledger row")
          "an untracked path answered as known"
        -- FORWARD: the proved conservatism — the enumeration face.
        -- cs = [the row]: the row lives IN its collection, so a row
        -- change is a contents change there (the CLI/report's face).
        let fwd := Kit.Ledger.forward `Schema.Example [`Schema.Example] fixtureLedger
        assert (fwd.contains lrWit) "the row-reading artifact was missed"
        assert (fwd.contains lrRust)
          "the collection-ENUMERATING artifact was missed — forward \
            under-reported (the demand-set correction regressed)"
        -- ORPHANS: the on-disk squatter
        let orph := Inspector.LedgerView.orphans fixtureLedger
          ["gen/a.wit", "gen/b.rs", "gen/squatter.wat"]
        assertEq "orphans" orph ["gen/squatter.wat"]
        -- the loaded report renders the tables + flags the squatter
        let (rep, failed) := Inspector.LedgerView.report
          ["gen/a.wit", "gen/b.rs", "gen/squatter.wat"] (.loaded fixtureLedger)
        assert failed "the orphan report did not fail the run"
        assert (rep.contains "ORPHAN gen/squatter.wat") s!"the report: {rep}"
        assert (rep.contains "backward (artifact → its demand surface)")
          "no backward table"
        assert (rep.contains "forward (spec name → affected artifacts)")
          "no forward table"
        -- the ABSENT state: dormant, never a fabricated clean
        let (abs, failedAbs) := Inspector.LedgerView.report ["gen/a.wit"] .absent
        assert (!failedAbs) "the dormant state failed the run"
        assert (abs.contains "ABSENT") "the absent state did not name itself"
        assert (abs.contains "DORMANT") "the absent state did not name its dormancy"
        -- the parse refusal fails loudly
        let (ref, failedRef) := Inspector.LedgerView.report []
          (.refused "malformed row")
        assert failedRef "the refusal did not fail the run"
        assert (ref.contains "REFUSED") "the refusal did not name itself"
        -- the selfStable round-trip: print → parse → identical
        let printed := Kit.Ledger.print fixtureLedger
        match Kit.Ledger.parse printed with
        | .ok rows =>
            assert (rows == fixtureLedger)
              s!"the round-trip rows drifted: {rows.length} row(s)"
        | .error e => assert false s!"the canonical print refused to parse: {e}"
        assert (Kit.Ledger.selfStable printed)
          "the canonical print failed its own stability check")
      [ ("forward under-reports the enumeration face (the pre-correction query)",
          fun _ => assert
            (!(Kit.Ledger.forward `Schema.Example [`Schema.Example]
              fixtureLedger).contains lrRust)
            "forward covered the enumeration face")
      , ("the absent state renders a clean orphan verdict",
          fun _ => assert ((Inspector.LedgerView.report ["gen/a.wit"] .absent).1.contains
            "orphans: none")
            "the dormant state refused to render a verdict")
      , ("a structurally hand-edited ledger passes its own stability check",
          fun _ => -- reordering the rows breaks the canonical order — the
                   -- parse refuses, the stability check is false. (A VALUE
                   -- edit stays canonical: the hash/header gates own the
                   -- content face; selfStable owns the form face.)
          assert (Kit.Ledger.selfStable (Kit.Ledger.print [lrRust, lrWit]))
            "the unsorted ledger was caught")
      ] 1 42 ]

/-! ## 6. The proof coverage (the census, as data) -/

open LintKit in
/-- The fabricated census: moduleOf + graph + pins, as data. -/
def fabricatedCites : Inspector.Cites.Cites :=
  let mods : NameMap Name := ({} : NameMap Name)
    |>.insert `T.thm1 `Lib.A |>.insert `T.thm2 `Lib.A |>.insert `T.thm3 `Lib.B
    |>.insert `Lib.A.g `Lib.A |>.insert `Lib.B.f `Lib.B
  { census := ({} : NameMap (Array Name))
      |>.insert `T.thm1 #[`Lib.B.f, `Lib.A.g]
      |>.insert `T.thm2 #[`Lib.A.g]
      |>.insert `T.thm3 #[]
    pinned := (· == `T.thm3)
    moduleOf := mods.find? }

def citesSpecs : List Spec :=
  [ Spec.ofList "the proof coverage (who cites this theorem — the census as data)"
      (fun _ => do
        -- the cited theorem: both citers, with their modules
        let (a, knownA) := Inspector.Cites.citesAnswer fabricatedCites `T.thm1
        assert knownA "the cited theorem answered unknown"
        assert (a.contains "2 citing declaration(s)") s!"the answer: {a}"
        assert (a.contains "← Lib.B.f (Lib.B)") "the outside citer is missing"
        assert (a.contains "← Lib.A.g (Lib.A)") "the same-module citer is missing"
        assert (!(a.contains "ZERO citations")) "a cited theorem read as zero"
        -- the zero-citation theorem: the leftover rule's finding
        let (z, _) := Inspector.Cites.citesAnswer fabricatedCites `T.thm2
        assert (z.contains "ZERO citations") "the zero did not read as zero"
        let zeros := Inspector.Cites.zeroCites fabricatedCites
          [(`Lib.A, `T.thm1), (`Lib.A, `T.thm2), (`Lib.B, `T.thm3)]
        assertEq "zero set" zeros [(`Lib.A, `T.thm2)]
        -- the test pin counts as the citation (the census's second medium)
        assert (!(Inspector.Cites.zeroCites fabricatedCites [(`Lib.B, `T.thm3)]
          ).contains (`Lib.B, `T.thm3))
          "the pinned theorem read as uncited"
        -- the loud miss: the unknown constant
        let (u, knownU) := Inspector.Cites.citesAnswer fabricatedCites `T.nope
        assert (!knownU && u.contains "NO SUCH CONSTANT")
          "the unknown constant answered as known"
        -- the per-library report (the module's ROOT names the section:
        -- Lib.A's root is Lib)
        let rep := Inspector.Cites.uncitedReportFull [(`Lib.A, `T.thm2)] 3
        assert (rep.contains "3 theorem(s) scanned") "the scan count drifted"
        assert (rep.contains "  Lib:") "no per-library section"
        assert (rep.contains "T.thm2") "the finding is missing")
      [ ("the same-module citation counts as a zero",
          fun _ => assert ((Inspector.Cites.zeroCites fabricatedCites
              [(`Lib.A, `T.thm1)]).contains (`Lib.A, `T.thm1))
            "the same-module face was not the loophole")
      , ("the pin does not count as a citation",
          fun _ => assert ((Inspector.Cites.zeroCites fabricatedCites
              [(`Lib.B, `T.thm3)]).contains (`Lib.B, `T.thm3))
            "the pin was ignored")
      , ("the unknown constant answers as known",
          fun _ => assert ((Inspector.Cites.citesAnswer fabricatedCites `T.nope).2)
            "the unknown was caught")
      ] 1 42 ]

/-! ## 7. The trust report (the honesty discipline) -/

def trustSpecs : List Spec :=
  [ Spec.ofList "the trust report's honesty (oracleSwept NEVER renders as a proof)"
      (fun _ => do
        -- the fabricated oracleSwept row's distribution line: TESTED AGREEMENT
        let dist := Inspector.Trust.tierDistribution [honestOracle, honestDecided]
        assert (dist.contains "oracle-swept: 1 row(s)") s!"the distribution: {dist}"
        assert (dist.contains "decidable-now: 1 row(s)") "the decided count drifted"
        let line := Inspector.Trust.tierLine .oracleSwept 1
        assert (line.contains "TESTED AGREEMENT") s!"the tier line: {line}"
        assert (!(line.contains "universal proof"))
          "the oracleSwept line rendered as a universal proof"
        -- the axiom surface: the empty tree state
        let ax0 := Inspector.Trust.axiomSummary []
        assert (ax0.contains "0 distinct axiom(s)") s!"the empty summary: {ax0}"
        assert (ax0.contains "NONE DISCLOSED") "the native line on an empty surface"
        assert (ax0.contains "outside the allowlist: none")
          "the outside line on an empty surface"
        -- the core triple classifies as the core triple
        let axC := Inspector.Trust.axiomSummary
          [`propext, `Classical.choice, `Quot.sound]
        assert (axC.contains "core triple: Classical.choice, Quot.sound, propext")
          s!"the core-triple summary: {axC}"
        -- the disclosed native trust base renders per class
        assert (Inspector.Trust.classifyAxiom `Foo._native.native_decide.ax_1
              == .nativeTrustBase)
          "the native certificate axiom did not classify as the native base"
        -- the OUTSIDE axiom renders as the LOUD flag
        let axBad := Inspector.Trust.axiomSummary [`Foo.myAxiom]
        assert (axBad.contains "AXIOM-OUTSIDE Foo.myAxiom") s!"the bad summary: {axBad}"
        assert (axBad.contains "FLAGGED") "the outside axiom was not flagged"
        -- the assembly: the duel zero-state + the replay coverage
        let rep := Inspector.Trust.trustReport "SchemaCore" 5 2383
          [] [honestOracle]
        assert (rep.contains "duel rows: NONE REGISTERED") "no duel zero-state"
        assert (rep.contains "5 of them the tree's own") "the project count line drifted"
        assert (rep.contains "2383 module(s) in the loaded closure")
          "the closure count line drifted"
        assert (rep.contains "TESTED AGREEMENT")
          "the honesty discipline line is missing")
      [ ("the fabricated oracleSwept tier renders as a universal proof",
          fun _ => assert ((Inspector.Trust.tierLine .oracleSwept 1).contains
            "universal proof") "the tier line was honest")
      , ("the outside axiom classifies as allowlisted",
          fun _ => assert (Inspector.Trust.classifyAxiom `Foo.myAxiom == .coreTriple)
            "the outside axiom was caught")
      , ("the duel zero-state does not name its absence",
          fun _ => assert (!(Inspector.Trust.duelStatus.contains "NONE REGISTERED"))
            "the zero-state named its absence")
      ] 1 42 ]

/-! ## 8. The what-if inspector (08 #20: the rewind + the divergence report) -/

open Inspector.WhatIf SchemaCore in
def whatIfSpecs : List Spec :=
  [ Spec.ofList "the what-if inspector (the rewind pin + the divergence report's known answer)"
      (fun _ => do
        -- THE REWIND PIN: the state as of occurrence 2 — the replay of
        -- the journal's prefix (the landed `runStates`' runtime face)
        assert (renderTable (rewindEvents "id" fixtureRows0 fixtureJournal 2)
            == renderTable [fixtureRow 1 "ann", fixtureRow 2 "bob2",
                fixtureRow 3 "cat"])
          "the rewind drifted"
        -- the rewind IS the prefix's replay
        -- (rewindEvents_eq_runStates's runtime face)
        assert (renderTable (rewindEvents "id" fixtureRows0 fixtureJournal 2)
            == renderTable (runStates "id" fixtureRows0
                (journalDeltas fixtureJournal) 2))
          "the rewind is not the prefix's replay"
        -- THE WHAT-IF's KNOWN ANSWER: the divergence is AT 1 — the
        -- prefix agrees (nothing before the modification point moved)
        assert (fixtureWhatIf.divergesAt? == some 1)
          "the worked what-if's divergence point drifted"
        assert (renderTable fixtureWhatIf.originalOutcome
            == renderTable [fixtureRow 2 "bob2", fixtureRow 3 "cat"])
          "the original outcome drifted"
        assert (renderTable fixtureWhatIf.modifiedOutcome
            == renderTable [fixtureRow 2 "bobby", fixtureRow 3 "cat"])
          "the what-if outcome drifted"
        -- THE ORIGINAL JOURNAL UNTOUCHED: the report's original is the
        -- fixture, byte for byte (the seqs + the rendered intents); the
        -- modified stream is a NEW journal with the SAME occurrences
        assert ((fixtureWhatIf.original.map (·.seq))
            == (fixtureJournal.map (·.seq)))
          "the original journal's occurrence identity drifted"
        assert ((fixtureWhatIf.original.map (fun e => renderDelta e.delta))
            == (fixtureJournal.map (fun e => renderDelta e.delta)))
          "the original journal's recorded intents drifted"
        assert ((fixtureWhatIf.modified.map (·.seq))
            == (fixtureJournal.map (·.seq)))
          "the modified stream renumbered the occurrences \
            (whatIfJournal_seqs's runtime face)"
        assert (renderDelta fixtureWhatIf.modified[1].delta
            == renderDelta fixtureReplacement)
          "the modified event's intent is not the replacement"
        assert (renderDelta fixtureWhatIf.modified[0].delta
            == renderDelta fixtureJournal[0].delta)
          "the unmodified events drifted"
        -- THE NET-ZERO WHAT-IF: the same update replaces itself — no
        -- divergence, the outcomes render equal (the none-face law's face)
        assert (fixtureNetZero.divergesAt? == none)
          "the net-zero what-if reported a divergence"
        assert (renderTable fixtureNetZero.modifiedOutcome
            == renderTable fixtureNetZero.originalOutcome)
          "the net-zero outcomes drifted"
        -- the render names the discipline
        let rep := Report.render fixtureWhatIf
        assert (rep.contains "NEW stream") "the render omits the new-stream line"
        assert (rep.contains "the original is untouched")
          "the render omits the untouched line"
        assert ((Report.render fixtureNetZero).contains "NET ZERO")
          "the net-zero render omits its honest none line")
      [ ("the divergence is reported early",
          fun _ =>
            assert (fixtureWhatIf.divergesAt? == some 0)
              "control fired: the prefix through event 0 agrees — the divergence \
                starts at the modification point, not before")
      , ("the what-if rewrote the original",
          fun _ =>
            assert (renderDelta fixtureWhatIf.original[1].delta
                == renderDelta fixtureReplacement)
              "control fired: the ORIGINAL journal keeps its recorded intent — \
                the what-if is a hypothetical, never a rewrite")
      , ("the net-zero reports a divergence",
          fun _ =>
            assert (fixtureNetZero.divergesAt?.isSome)
              "control fired: the self-replacement is a net zero — the walk \
                must report none")
      , ("the what-if renumbered the occurrences",
          fun _ =>
            assert ((fixtureWhatIf.modified.map (·.seq))
                != (fixtureJournal.map (·.seq)))
              "control fired: occurrence identity survives the what-if \
                (the trichotomy's event-identity discipline)")
      , ("the out-of-range modification fabricated an event",
          fun _ =>
            assert (match
                (whatIfJournal fixtureJournal 9 fixtureReplacement)[1]? with
              | some e => renderDelta e.delta == renderDelta fixtureReplacement
              | none => false)
              "control fired: a modification point past the end is the identity — \
                no occurrence at 9, nothing modified")]
    1 42 (h := by simp)]

/-! ## The driver -/

unsafe def main : IO UInt32 := do
  match ← Inspector.collectReplayed with
  | .error e =>
      IO.eprintln s!"InspectorTests: LOAD FAILED — {e}"
      return 1
  | .ok rows =>
      TestingKit.mainOfSuites
        [ ("live replay", liveReplaySpecs rows)
        , ("live why", liveWhySpecs rows)
        , ("trust axes", trustAxisSpecs)
        , ("teeth", teethSpecs)
        , ("ledger reading", ledgerSpecs)
        , ("proof coverage", citesSpecs)
        , ("trust report", trustSpecs)
        , ("what-if", whatIfSpecs) ]

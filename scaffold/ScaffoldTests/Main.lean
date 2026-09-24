/-
# ScaffoldTests — the scaffold generator's test battery

Positive pins + the MANDATORY negative controls (15-patterns #5); the
byte-tie discipline is TestingKit.Golden's (15-patterns #10); the runner
is TestingKit's (`mainOfSuites`).

1. The BYTE-TIE (the committed skeleton IS the golden): the adopted
   skeletons (DemoApp + the dogfood LedgerApp — the `ScaffoldDemo`/
   `ScaffoldLedger` libs) are the generator's own output over the
   adopted specs (Scaffold.Specs) — a drift between
   `Scaffold.Generate` and the committed bytes FAILS THE BUILD. The
   tie's subject is the GENERATED-header files; the hand-owned
   `<Name>/Flow.lean` seed (no header — the fill obligations' home)
   is OUTSIDE the tie by construction. Regen is the deliberate
   re-emit: `lake exe scaffoldgen all`; `lake build` (the adopted
   libs ride the default targets) is the compiled-ness proof.
2. The adopted suites RUN: the generated specs + the consumers'
   flow specs pass (property holds, every control caught) — the
   template's born-green proof.
3. The curated-failure teeth: every malformed-AppSpec refusal carries
   the ONE Diag envelope — the E-code, the valid space, the ONE
   engine's did-you-mean — pinned exactly.
4. The negative controls: the sabotaged generator variants (the
   controls section dropped, the validator tooth silenced, the
   byte-tie tampered, the Flow-seed headerless tooth flipped) are
   CAUGHT by the teeth.

Axiom self-check: `Axioms.lean` pins #print axioms — the CORE TRIPLE
only (the allowlist), the build fails on any drift.
Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import Scaffold
import TestingKit.Harness
import TestingKit.Golden
import DemoApp.Tests
import LedgerApp.Tests
import LedgerApp.Flow
import ScaffoldTests.Axioms

open Scaffold TestingKit

/-! ## The adopted specs (Scaffold.Specs — the ONE home per spec value) -/

-- The adopted skeletons' specs live in `Scaffold.Specs` (the writer
-- driver's input — one writer per artifact path means one home per
-- spec value): `demoSpec` (DemoApp) + `ledgerSpec` (the dogfood
-- LedgerApp). The malformed variants below derive from `demoSpec`.

/-! ## 1. The byte-tie + the adopted suites' run -/

/-- The byte-tie failures for one adopted skeleton (empty = tied).
    The tie's subject: the GENERATED-header files — the hand-owned
    Flow seed carries no header, so it is outside the tie by
    construction (the header's PRESENCE marks the generator's
    one-writer surface, the artifact-headers gate's detection-face
    precedent). -/
def byteTieFailures (spec : AppSpec) : IO (List String) := do
  match generate spec with
  | .error d => return [s!"generate refused {spec.name}: {d.code.code}: {d.message}"]
  | .ok files =>
    let mut fs : List String := []
    for f in files do
      unless f.contents.startsWith "-- GENERATED" do continue
      let p : System.FilePath := f.path
      unless ← p.pathExists do
        fs := s!"{f.path}: the adopted skeleton is ABSENT — regen" :: fs
        continue
      let committed ← IO.FS.readFile p
      match TestingKit.Golden.cmp f.contents committed with
      | .ok () => pure ()
      | .error e => fs := s!"{f.path}: {e}" :: fs
    return fs

/-- The adopted suites' verdicts must each be `.pass` (property holds,
    every control caught). -/
def adoptedSuiteFailures : List (String × Option String) :=
  [ ("DemoApp", match demoAppItemSpec.run with
      | .pass _ => none
      | v => some s!"the adopted DemoApp suite did not pass: {v}")
  , ("LedgerApp", match ledgerAppItemSpec.run with
      | .pass _ => none
      | v => some s!"the adopted LedgerApp suite did not pass: {v}")
  , ("LedgerApp flow", match LedgerApp.ledgerAppItemFlowSpec.run with
      | .pass _ => none
      | v => some s!"the adopted LedgerApp flow suite did not pass: {v}") ]

/-! ## 2. The pure teeth (the curated failures + the structure) -/

/-- The E-code spellings of a validation result. -/
def diagCodes (ds : List Kit.Diag) : List String := ds.map (fun d => d.code.code)

/-- The malformed specs (each names the refusal it must draw). -/
def unknownCapSpec : AppSpec := { demoSpec with capabilities := ["emitr"] }
def dupCapSpec : AppSpec := { demoSpec with capabilities := demoSpec.capabilities ++ ["emitter"] }
def unknownRowSpec : AppSpec := { demoSpec with gateRows := ["axiom"] }
def dupRowSpec : AppSpec := { demoSpec with gateRows := demoSpec.gateRows ++ ["axioms"] }
def badNameSpec : AppSpec := { demoSpec with name := "demo app" }
def dupConsumeSpec : AppSpec := { demoSpec with consumes := ["Order", "Order"] }
def emptyCapsSpec : AppSpec := { demoSpec with capabilities := [] }
def orphanCapSpec : AppSpec := { demoSpec with capabilities := ["emitter", "diagnostics"] }
def unknownRootSpec : AppSpec := { demoSpec with root := "Crossing" }
def unknownRungSpec : AppSpec := { demoSpec with rung := "kernel" }
def blankCarrierSpec : AppSpec := { demoSpec with carrier := "" }

/-- The skeleton's structure teeth over the generated bodies (spec-
    generic — every tooth derives from `itemTyOf spec` / `baseOf spec`). -/
def structuralTeeth (spec : AppSpec) : List Bool :=
  match generate spec with
  | .error _ => [false]
  | .ok files =>
      let reg := (files.find? (fun f => f.path.endsWith "Reg.lean")).map (·.contents)
      let flow := (files.find? (fun f => f.path.endsWith "Flow.lean")).map (·.contents)
      let tests := (files.find? (fun f => f.path.endsWith "Tests.lean")).map (·.contents)
      [ (files.map (·.path)).Nodup
      , files.length == 4
      , reg.map (fun b => b.contains ("register_lane " ++ itemTyOf spec))
          |>.getD false
      , tests.map (fun b =>
          decide (2 ≤ (b.splitOn "\n").countP (fun l => l.contains "sabotage:")))
          |>.getD false
      , tests.map (fun b => b.contains "Five questions") |>.getD false
      -- THE WIDENED REPLAY PIN (the dogfood's gap): the pin accepts the
      -- lane consumption's GROWTH (≥ 1 entries, the first pinned) — a
      -- second entry never breaks the generated suite's build.
      , tests.map (fun b => b.contains "reg.items.length ≥ 1") |>.getD false
      -- THE FLOW SEED (the fill obligations' home): present, HEADERLESS
      -- (hand-owned — outside the byte-tie), the emitter row lives
      -- there iff the capability was requested.
      , flow.isSome
      , flow.map (fun b => !b.startsWith "-- GENERATED") |>.getD false
      , flow.map (fun b => b.contains "Emitter") == hasCap spec .emitter
      , flow.map (fun b => b.contains "FlowSpec") |>.getD false
      -- THE ENTOURAGE WIRING (16-surface §3): the generated modules
      -- reference the evidence entourage — the obligation's tier is
      -- COMPUTED (the kind row) and the suite's controls are the
      -- entourage's mechanical shapes, not placeholders.
      , (files.find? (fun f => f.path.endsWith "App.lean")).map (fun a =>
          a.contents.contains "evidenceKindOfShape") |>.getD false
      , tests.map (fun b => b.contains "mechanicalControls") |>.getD false ]

/-- The pure sweep: both adopted specs validate clean, the structure
    is present, every malformed spec refuses with the curated
    envelope. -/
def teethSpec : Spec :=
  Spec.ofList "scaffold teeth (curated failures + structure)" (fun _ => do
    assert (validate demoSpec |>.isEmpty) "the demo spec must validate clean"
    assert ((structuralTeeth demoSpec).all id) "the skeleton's structure drifted"
    assert (validate ledgerSpec |>.isEmpty) "the dogfood spec must validate clean"
    assert ((structuralTeeth ledgerSpec).all id) "the dogfood skeleton's structure drifted"
    assert (diagCodes (validate unknownCapSpec) == ["SCF0002"])
      "unknown capability: wrong E-code"
    assert ((validate unknownCapSpec).all (fun d => d.valid == Capability.renderAll))
      "unknown capability: the valid space must enumerate the CLOSED enum"
    assert ((validate unknownCapSpec).any (fun d =>
        d.suggest == some " — did you mean: emitter?"))
      "unknown capability: the did-you-mean is the ONE engine's"
    assert (diagCodes (validate dupCapSpec) == ["SCF0003"])
      "duplicate capability: wrong E-code"
    assert (diagCodes (validate unknownRowSpec) == ["SCF0004"])
      "unknown gate row: wrong E-code"
    assert ((validate unknownRowSpec).any (fun d =>
        d.valid == gateRowNames
          && d.suggest == some " — did you mean: axioms?"))
      "unknown gate row: the valid space + did-you-mean drifted"
    assert (diagCodes (validate dupRowSpec) == ["SCF0005"])
      "duplicate gate row: wrong E-code"
    assert (diagCodes (validate badNameSpec) == ["SCF0001"])
      "bad name: wrong E-code"
    assert (diagCodes (validate dupConsumeSpec) == ["SCF0006"])
      "duplicate consume: wrong E-code"
    assert (diagCodes (validate emptyCapsSpec) == ["SCF0010"])
      "empty capabilities: wrong E-code (the scaffold refuses an empty skeleton)"
    assert (diagCodes (validate orphanCapSpec) == ["SCF0012"])
      "orphan capability: wrong E-code (a lane fold without the lane)"
    assert (diagCodes (validate unknownRootSpec) == ["SCF0007"])
      "unknown root: wrong E-code"
    assert ((validate unknownRootSpec).all (fun d => d.valid == Root.renderAll))
      "unknown root: the valid space drifted"
    assert (diagCodes (validate unknownRungSpec) == ["SCF0008"])
      "unknown rung: wrong E-code"
    assert (diagCodes (validate blankCarrierSpec) == ["SCF0009"])
      "blank carrier: wrong E-code (the five-questions header refuses blanks)"
    match generate unknownCapSpec with
    | .ok _ => assert false "generate accepted a malformed spec"
    | .error d =>
        assert (d.code.code == "SCF0002")
          "generate's refusal must carry the curated envelope")
    [
      ("sabotage: the controls tooth loses its discrimination", fun _ =>
        -- drop the sabotage lines from the generated Tests body: the
        -- structure tooth MUST stop seeing two controls
        match generate demoSpec with
        | .error _ => assert false "unreachable: the demo spec validates"
        | .ok files =>
            let body := (files.find? (fun f => f.path.endsWith "Tests.lean")).map (·.contents)
              |>.getD ""
            let sabotaged := (body.splitOn "\n")
              |>.filter (fun l => !l.contains "sabotage:")
            assert (((sabotaged.filter (fun l => l.contains "sabotage:")).length) ≥ 2)
              "control fired: the dropped-controls sabotage escaped the tooth")
    , ("sabotage: the validator's tooth silenced", fun _ =>
        -- an accepting validator would let the unknown capability through
        assert (validate unknownCapSpec |>.isEmpty)
          "control fired: the validator accepted an unknown capability")
    , ("sabotage: the byte-tie accepts a tampered body", fun _ =>
        match generate demoSpec with
        | .error _ => assert false "unreachable: the demo spec validates"
        | .ok files =>
            let body := (files.find? (fun f => f.path.endsWith "Reg.lean")).map (·.contents)
              |>.getD ""
            let tampered := body.replace "register_lane " "register_laneX "
            let tied := match TestingKit.Golden.cmp tampered body with
              | .ok () => true
              | .error _ => false
            assert (tied)
              "control fired: the tampered body tied the golden")
    , ("sabotage: the tie reads the HAND-OWNED Flow seed", fun _ =>
        -- the tie-filter tooth: the headerless seed must sit outside
        -- the tie — a filter that reads it would read the consumer's
        -- own bytes as a drift
        match generate demoSpec with
        | .error _ => assert false "unreachable: the demo spec validates"
        | .ok files =>
            let flow := (files.find? (fun f => f.path.endsWith "Flow.lean")).map (·.contents)
              |>.getD ""
            assert (flow.startsWith "-- GENERATED")
              "control fired: the hand-owned seed entered the tie")
    ] 8 42

/-! ## The driver -/

def main : IO UInt32 := do
  let mut failed := 0
  -- the byte-tie (IO): every adopted skeleton vs the generator
  for spec in adoptedSpecs do
    let btfs ← byteTieFailures spec
    for e in btfs do
      IO.println s!"FAIL byte-tie ({spec.name}): {e}"
      failed := failed + 1
    if btfs.isEmpty then
      IO.println s!"ok byte-tie: {spec.name} ties (the GENERATED files)"
  -- the adopted suites' runs
  for (name, failure) in adoptedSuiteFailures do
    match failure with
    | none => IO.println s!"ok adopted-suite ({name}): the Spec passes, controls caught"
    | some e => IO.println s!"FAIL adopted-suite ({name}): {e}"; failed := failed + 1
  -- the pure teeth
  let v := teethSpec.run
  IO.println (v.render teethSpec)
  match v with
  | .pass _ => pure ()
  | _ => failed := failed + 1
  unless failed == 0 do
    IO.println s!"{failed} group(s) failed"
  return if failed == 0 then 0 else 1

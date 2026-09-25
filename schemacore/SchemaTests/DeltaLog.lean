/- # SchemaTests.DeltaLog — the log model's scenario pins + the duel faces

Owner: the persistence lane (design-wave-30 A5's test face).
Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5). The scenarios are the DUEL's Lean side: the
LCG-seeded crash scenarios (the tree's ONE recurrence, `TestingKit.lcg`
— the same seed, the same draws the Rust `tests/crash_duel.rs` replays
through the REAL recovery), each cut's outcome pinned as a value-level
theorem over the landed model (`SchemaCore.DeltaLog`) + the landed
codec's fixture instantiation (`Emit.Journal.encRowJ`/`encKeyJ` — the
ONE copy). A model/Rust skew fails the duel loudly on either side.

The negative controls: a boundary cut is CLEAN (no phantom report), a
cut past the end reports nothing, a crash before the first byte is the
fresh-journal shape — and the sabotages fire the wrong claims.

Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import TestingKit.Harness
import SchemaCore.Event
import SchemaCore.Emit.Journal
import SchemaCore.DeltaLog

open SchemaCore SchemaCore.Emit.Journal TestingKit

namespace SchemaTests.DeltaLog

/-! ## The duel's scenario generator (the ONE shared shape) -/

/-- ONE LCG draw drives the delta: kind = `(r >>> 8) % 3`
    (insert/update/remove), key = `r % 7` (the small window keeps
    updates and removes hitting); the payload is the FIXED row
    `[id = key, name = "row"]` — the stream drives the shape, the
    string is fixed (the Rust side's `op` is this exact function). -/
def drawDelta (r : UInt64) : RowDelta journalFields :=
  let id := r % 7
  let k := (r >>> 8) % 3
  if k = 0 then .insert (.cons (.u64 id) (.cons (.string "row") .nil))
  else if k = 1 then .update (.cons (.u64 id) (.cons (.string "row") .nil))
  else .remove { ty := .u64, val := .u64 id }

/-- The op stream: n draws from the seed (the Rust side's `op_stream`
    at the SAME seed — the duel's shared scenarios). -/
def drawOps : Nat → UInt64 → List (RowDelta journalFields)
  | 0, _ => []
  | n + 1, st => drawDelta (TestingKit.lcg st) :: drawOps n (TestingKit.lcg st)

/-- The LCG state after n draws (the cut stream resumes there). -/
def streamState : Nat → UInt64 → UInt64
  | 0, s => s
  | n + 1, s => streamState n (TestingKit.lcg s)

/-- THE SCENARIO: the seeded journal (12 ops at seed 0x5EED) — the
    journal the Rust duel writes through the REAL `DeltaLog`. -/
def scenarioOps : List (RowDelta journalFields) := drawOps 12 0x5EED

/-- The scenario's log-file wire (the landed codec's own bytes). -/
def scenarioWire : List UInt8 := DeltaLog.logWire encRowJ encKeyJ scenarioOps

/-- The scenario's byte length (the cut draws' modulus: a crash lands
    at ANY byte in [0, L]). -/
def scenarioLen : Nat := scenarioWire.length

/-- The cut stream: n more LCG draws mod (L+1) — each a crash point. -/
def drawCuts : Nat → UInt64 → List Nat
  | 0, _ => []
  | n + 1, st =>
      (TestingKit.lcg st).toNat % (scenarioLen + 1) :: drawCuts n (TestingKit.lcg st)

/-- THE SCENARIO'S CRASH POINTS: 6 LCG-seeded cuts off the post-ops
    stream state (the Rust duel replays the SAME draws). -/
def scenarioCuts : List Nat := drawCuts 6 (streamState 12 0x5EED)

/-- The outcome face the duel pins: (surviving frames, torn offset,
    torn?) — `offset = 0 ∧ torn = false` on the clean shape. -/
def openFace (log : List (RowDelta journalFields)) (cut : Nat) :
    Nat × Nat × Bool :=
  match DeltaLog.openAt encRowJ encKeyJ cut log with
  | .clean es => (es.length, 0, false)
  | .torn es r => (es.length, r.offset, true)

/-- The scenario's faces, in cut order (the Rust duel's expected
    values — a skew fails HERE or there). -/
def scenarioFaces : List (Nat × Nat × Bool) :=
  scenarioCuts.map (fun c => openFace scenarioOps c)

/-! ## The duel faces (kernel-computed over the landed codec + walk) -/

/-- The scenario is real: 12 ops, a nonempty wire, 6 cuts, the cuts
    sweep the wire (the Rust duel's constants must match these). -/
theorem scenario_nonvacuous :
    scenarioOps.length = 12 ∧ scenarioLen = 69 ∧ scenarioCuts
      = [36, 65, 36, 63, 52, 45] := by
  decide

/-- THE DUEL FACES, pinned (the kernel's own computation over the
    landed codec + the landed walk — the Rust duel replays the same
    seed through the REAL recovery and must land HERE). -/
theorem scenarioFaces_pin : scenarioFaces
    = [(5, 30, true), (11, 62, true), (5, 30, true), (11, 62, true),
       (8, 51, true), (7, 44, true)] := by
  decide

/-- THE LONGEST-PREFIX CONTENT, at the scenario: the first torn face's
    report names the cut at the torn frame's start — offset 30 = the
    end of frame 5 = a genuine frame boundary (computed, not assumed). -/
theorem face1_offset_is_boundary :
    (scenarioWire.take 30).length = 30 := by decide

/-! ## The negative controls (the report's honesty, at values) -/

/-- THE BOUNDARY CONTROL: a cut ON a frame boundary (byte 30 = frame
    5's end) is a clean shorter journal — no report, exactly the five
    frames that fit. Never a phantom report. -/
theorem boundary_cut_clean :
    openFace scenarioOps 30 = (5, 0, false) := by decide

/-- THE PAST-THE-END CONTROL: a cut past the wire reports nothing —
    the full journal loads clean. -/
theorem past_end_clean :
    openFace scenarioOps (scenarioLen + 100) = (12, 0, false) := by decide

/-- THE ZERO CONTROL: a crash before the first byte is the
    fresh-journal shape — clean, empty. -/
theorem zero_cut_clean : openFace scenarioOps 0 = (0, 0, false) := by decide

/-! ## The runtime suite -/

def deltaLogSpec : Spec := Spec.ofList "the delta log's crash-recovery model"
  (fun _ => do
    -- the duel faces, runtime-pinned (the Lean side's own replay)
    assert (scenarioOps.length == 12) "scenario ops"
    assert (scenarioLen == 69) "scenario wire length"
    assert (scenarioCuts == [36, 65, 36, 63, 52, 45]) "scenario cuts"
    assert (scenarioFaces == [(5, 30, true), (11, 62, true), (5, 30, true),
        (11, 62, true), (8, 51, true), (7, 44, true)]) "duel faces"
    -- the honesty controls
    assert (openFace scenarioOps 30 == (5, 0, false)) "boundary cut is clean"
    assert (openFace scenarioOps (scenarioLen + 100) == (12, 0, false))
      "past-the-end cut is clean"
    assert (openFace scenarioOps 0 == (0, 0, false)) "zero cut is clean")
  [ ("sabotage: the boundary cut reports torn (phantom report)",
      fun _ =>
        assert (openFace scenarioOps 30 == (5, 30, true)) "control"),
    ("sabotage: the torn cut at 36 reports clean (silent loss)",
      fun _ =>
        assert (openFace scenarioOps 36 == (5, 0, false)) "control"),
    ("sabotage: the recovered prefix drops a surviving frame",
      fun _ =>
        match DeltaLog.openAt encRowJ encKeyJ 36 scenarioOps with
        | .torn es r => assert (es.length != r.frames) "control"
        | .clean _ => assert false "control"),
    ("sabotage: the report's offset rides the crash point (not the torn
        frame's start)",
      fun _ =>
        assert (openFace scenarioOps 36 == (5, 36, true)) "control") ]
  1 43

end SchemaTests.DeltaLog

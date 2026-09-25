/- # MachinesTests.CrashLog — the delta-log machine's teeth

Owned by: the persistence lane (design-wave-30 A5's machine face).
Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5), over `Machines.Crash.Log` (the delta log AS a crash
machine — the durable/volatile split, append as the ONE transition
family, the replay as the recovery). Suites:

1. `log-machine` — the durable/volatile split pinned in values: the
   crash drops the volatile (the materialized state) and keeps the
   persistent (the journal); the recovery reconstructs (the journal's
   replay); the closure is the identity at log-invariant states (and
   NOT at the lossy machine's — the control).
2. `torn-tail` — the recovery at the torn tail lands EXACTLY at the
   crash point's replay (the longest valid prefix, at the machine
   level), and the recovered state is faithful again: further crashes
   stay invisible (`beh_eq_recovered` at a witness).
3. `the-teeth` — the lossy log (journals nothing) is unfaithful, its
   crash+recovery REWINDS, and its refinement FAILS.

NOTE (wiring): compiled by the Machines lib glob; RUN only once
`MachinesTests.Main` imports it and registers `specCrashLog`. The
value-level theorems are compile-time checked regardless (the runtime
suite's asserts ride BEq faces — lengths — where the row types carry
no BEq; the value EQUALITIES are the theorems above them).

Axiom self-check: the core triple at most — a `sorry` or a new axiom
changes the axiom gate's printed sets and fails the build.
-/

import Machines
import Machines.CrashLog
import SchemaCore.Event
import TestingKit.Spec
import TestingKit.Harness

open Machines TestingKit
open Machines.Crash.Log
open SchemaCore (Field RowVals RowDelta deltaApply replay runStates)

namespace MachinesTests.CrashLog

/-! ## The fixture: the delta-log machine at the fixture schema -/

/-- The fixture fields (the delta crate's slice: id : u64 keyed,
    name : string — the Emit.Journal instantiation's shape). -/
abbrev fixtureFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "name", ty := .string }]

/-- A fixture row `[id = n, name = "r"]`. -/
def frow (n : UInt64) : RowVals fixtureFields :=
  .cons (.u64 n) (.cons (.string "r") .nil)

/-- The fixture insert delta (keyed on id). -/
def fins (n : UInt64) : RowDelta fixtureFields := .insert (frow n)

/-! ## Suite 1: the durable/volatile split, pinned in values -/

/-- THE CRASH DROPS THE VOLATILE: two different materialized states
    over the same journal crash to the SAME remnant. -/
theorem crash_drops_state :
    crashStep (([frow 1], [fins 3]) : List (RowVals fixtureFields)
        × List (RowDelta fixtureFields))
      = crashStep (([frow 9], [fins 3]) : List (RowVals fixtureFields)
        × List (RowDelta fixtureFields)) := rfl

/-- THE PERSISTENT SURVIVES: the remnant IS the journal. -/
theorem crash_keeps_journal :
    crashStep (([frow 1], [fins 3]) : List (RowVals fixtureFields)
        × List (RowDelta fixtureFields))
      = ([fins 3] : List (RowDelta fixtureFields)) := rfl

/-- THE RECOVERY RECONSTRUCTS: from the journal alone, the replay
    rebuilds the materialized state. -/
theorem recovery_replays :
    (logMachine (fs := fixtureFields) "id").recover [fins 3] = [frow 3] := rfl

/-- THE CLOSURE IS THE IDENTITY at a log-invariant state: crash +
    recovery = the journal's replay = exactly where the log was. -/
theorem closure_faithful_pin :
    (logMachine (fs := fixtureFields) "id").closure
        (([frow 3], [fins 3]) : List (RowVals fixtureFields)
          × List (RowDelta fixtureFields))
      = (([frow 3], [fins 3]) : List (RowVals fixtureFields)
        × List (RowDelta fixtureFields)) :=
  (logMachine "id").closure_of_faithful _ (by
    show [frow 3] = replay "id" [fins 3] []
    rfl)

/-! ## Suite 2: the torn tail, at the machine level -/

/-- The scenario journal: three appends. -/
def j3 : List (RowDelta fixtureFields) := [fins 1, fins 2, fins 3]

/-- THE TORN-TAIL RECOVERY: recovering over the walk's longest valid
    prefix (two frames survived) lands EXACTLY at the two-frame
    replay (`recover_prefix`, at values). -/
theorem recover_prefix_pin :
    (logMachine (fs := fixtureFields) "id").recover (j3.take 2)
      = [frow 1, frow 2] := rfl

/-- ... and that IS the crash point's replay (`runStates` at k = 2). -/
theorem recover_prefix_runStates :
    (logMachine (fs := fixtureFields) "id").recover (j3.take 2)
      = runStates "id" [] j3 2 := rfl

/-- THE RECOVERED STATE IS FAITHFUL AGAIN: after the torn-tail
    recovery, the crash+recovery closure is the identity — the log's
    invariant is restored, the recovered log is appendable. -/
theorem recovered_closure_identity :
    (logMachine (fs := fixtureFields) "id").closure
        ((logMachine "id").up (j3.take 2))
      = (logMachine "id").up (j3.take 2) := by
  rw [(logMachine "id").closure_of_faithful _
    (show (logMachine "id").FaithfulAt ((logMachine "id").up (j3.take 2)) from
      recovered_faithful "id" j3 2)]

/-- A crash interleaved after the recovery: the observed behavior
    streams are EQUAL with and without it (`beh_eq_recovered` at a
    witness). -/
def insCrash : Stream (Sum (RowDelta fixtureFields) Unit) :=
  fun t => match t with
    | 0 => Sum.inl (fins 4)
    | 1 => Sum.inr ()
    | _ => Sum.inl (fins 5)

theorem recovered_beh_eq :
    List.map (((logMachine "id").crashyCoalg stateObs).beh insCrash
        ((logMachine "id").up (j3.take 2))) [0, 1, 2]
      = List.map (((logMachine "id").freeCoalg stateObs).beh insCrash
        ((logMachine "id").up (j3.take 2))) [0, 1, 2] := by
  rw [beh_eq_recovered]

/-! ## Suite 3: THE TEETH — the lossy log -/

/-- The SABOTAGE machine: the step updates the materialized state but
    journals NOTHING — the write-through discipline's undo. -/
def lmach := lossyMachine (fs := fixtureFields) "id"

/-- THE TOOTH: the lossy state is UNFAITHFUL (the cache says one row,
    the journal replays to nothing). -/
theorem lossy_unfaithful_pin :
    ¬ (lmach).FaithfulAt (([frow 3], []) : List (RowVals fixtureFields)
      × List (RowDelta fixtureFields)) :=
  lossy_unfaithful "id" (frow 3)

/-- THE REWIND: at the unfaithful state the closure is NOT the
    identity — the crash+recovery rewinds to the journal's replay (the
    unjournaled delta is lost, loudly). -/
theorem lossy_rewinds_pin :
    (lmach).closure ((deltaApply "id" (fins 3) ([] : List (RowVals fixtureFields)),
        ([] : List (RowDelta fixtureFields))))
      = (([] : List (RowVals fixtureFields)),
        ([] : List (RowDelta fixtureFields))) := rfl

/-- THE REFINEMENT FAILS for the lossy machine: no simulation through
    "the same faithful state" survives the append — the step lands on
    the unfaithful state, where the relation is uninhabited. -/
theorem lossy_not_refines :
    ¬ Refines ((lmach).crashyCoalg stateObs) ((lmach).freeCoalg stateObs)
      (fun a b => a = b ∧ logF "id" a) := by
  intro h
  have hstepC : ((lmach).crashyCoalg stateObs).observe ([], []) (Sum.inl (fins 3))
      = some ([frow 3], ([frow 3], [])) := rfl
  have hstepF : ((lmach).freeCoalg stateObs).observe ([], []) (Sum.inl (fins 3))
      = some ([frow 3], ([frow 3], [])) := rfl
  rcases h.step (⟨rfl, rfl⟩ :
      ((fun a b => a = b ∧ logF "id" a) ([], []) ([], []))) (Sum.inl (fins 3))
    with ⟨hn, _⟩ | ⟨o, a, b, h₁, h₂, hR⟩
  · rw [hstepC] at hn; simp at hn
  · rw [hstepC] at h₁
    obtain ⟨_, ha⟩ := by simpa using h₁
    rw [hstepF] at h₂
    obtain ⟨_, hb⟩ := by simpa using h₂
    rw [← ha, ← hb] at hR
    exact absurd hR.2 (by
      intro hF
      simpa [logF, replay, SchemaCore.journalApply] using hF)

/-! ## The runtime suite (BEq faces: lengths — the equalities above are
     the compile-time teeth) -/

def specCrashLog : Spec := Spec.ofList "crash-log-machine"
  (fun _ => do
    -- the recovery reconstructs: one append replays to one row
    assert (((logMachine "id").recover [fins 3]).length == 1) "recovery replays"
    -- the torn-tail recovery: the longest valid prefix's replay
    assert (((logMachine "id").recover (j3.take 2)).length == 2)
      "torn-tail recovery = the longest valid prefix's replay"
    -- the recovery remembers NOTHING: the empty journal replays empty
    assert (((logMachine "id").recover
      ([] : List (RowDelta fixtureFields))).length == 0) "recovery forgets")
  [ ("sabotage-lossy-faithful", fun _ =>
      -- the lossy journal does NOT carry the unjournaled delta
      assert (((lmach).recover
        ([] : List (RowDelta fixtureFields))).length == 1) "control"),
    ("sabotage-closure-moves-at-faithful", fun _ =>
      -- the closure at the recovered state does NOT shrink the state
      assert (((logMachine "id").closure
        ((logMachine "id").up (j3.take 2))).1.length == 1) "control"),
    ("sabotage-recovery-remembers", fun _ =>
      assert (((logMachine "id").recover
        ([] : List (RowDelta fixtureFields))).length == 1) "control") ]
  1 47

end MachinesTests.CrashLog

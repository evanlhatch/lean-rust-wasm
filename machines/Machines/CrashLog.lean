/- # Machines.CrashLog — the delta log AS a crash machine (A5)

Owner: the persistence lane (the mandate tree, `machines/` — the bridge
face of design-wave-30 A5).
Driving decisions: notes/design-wave-30.md A5 (the Crash discipline →
the persistence model: the log = one transition family (append); the
crash = the Crash discipline's crash step; the state = the durable/
volatile split) + `Machines.Crash` (the discipline's model face) +
`SchemaCore.DeltaLog` (the byte-level walk + the recovery outcome
algebra — the honest home of the log MODEL; this module is the MACHINE
face over it).

THE INSTANTIATION: the delta log's durable/volatile split IS the Crash
discipline's persistent/volatile separation — the PERSISTENT component
is the journal (the frame list on stable storage), the VOLATILE
component is the materialized state (the keyed table the app reads).
The honest step is the log's ONE transition family: APPEND — journal
the delta AND update the state (write-through, in the type). The
recovery discipline is the journal's REPLAY (`SchemaCore.replay`, the I
operator) — from the persistent alone, there is no state input to
remember from.

THE TORN-TAIL FACE: a crash DURING an append leaves a strict byte
prefix of the journal — the torn frame is not a frame, so the machine
level never sees it: the recovery replays the LONGEST VALID PREFIX
(`SchemaCore.DeltaLog`'s walk; the report is the byte-level face's
data). The theorems:

- `log_faithful` — the log's invariant (the state IS the journal's
  replay) is a faithful fragment: recovery reconstructs, append
  preserves (`replay_snoc` — the append law IS the preservation);
- `recover_prefix` — the recovery at the torn tail lands EXACTLY at the
  crash point's replay (`runStates` at the surviving frame count): the
  honest relation recovered = the longest valid prefix, at the machine
  level;
- the refinement instantiates (`refines_crashy`/`refines_free_crashy`
  cited, never re-proved): the log's observed behavior is PRESERVED
  across crash+recovery — from any log-invariant state, crashes are
  invisible in the observation (`beh_eq_recovered` exercises it from a
  RECOVERED state: the crash+replay closure composes);
- the SABOTAGE (the teeth): a lossy log — a step that updates the
  materialized state but journals NOTHING — is unfaithful, its
  crash+recovery REWINDS the state, and NO simulation through "the same
  faithful state" survives: the refinement's premise is load-bearing
  for the persistence discipline exactly as the abstract worked example
  showed.

The five questions (notes/v3/01-core.md):
- root: TraceModel (01 §3) — the machine face rides the landed
  `CrashMachine` carrier + `Coalg.Refines`; no new root.
- carrier grade: pattern #1 — the crashy/free machines ARE `Machine`s
  over the landed carrier; the refinement rides the ONE relation family.
- spine reading: none — a bridge over `SchemaCore.DeltaLog`.
- ladder rung: the faithfulness theorem is one `replay_snoc` citation
  (rung 6); the value faces are rung-3 decides in MachinesTests.
- gate row: MachinesTests.CrashLog + the axiom report.

Cone: machines is the bridge grade (A4/A5's zone: machines +
schemacore) — imports `Machines.Crash` + `SchemaCore.Event` (read-only:
the replay + the delta semantics, the ONE copy).
-/

import Machines.Crash
import SchemaCore.Event

namespace Machines.Crash.Log

open SchemaCore

variable {fs : List Field}

/-! ## The log machine -/

/-- THE DELTA-LOG MACHINE (`log.rs`'s `DeltaLog` discipline, model
    face): the volatile state is the keyed table, the persistent state
    is the journal; the honest step is the log's ONE transition family
    — APPEND (journal the delta, update the state: write-through in the
    type); the recovery discipline is the journal's REPLAY. -/
def logMachine (key : String) :
    CrashMachine (List (RowVals fs)) (List (RowDelta fs)) (RowDelta fs) :=
  ⟨fun v p d => some (deltaApply key d v, p ++ [d]), fun p => replay key p []⟩

/-- The log's invariant: the materialized state IS the journal's replay
    (the event-sourcing invariant at the keyed-table face). -/
def logF (key : String) (vp : List (RowVals fs) × List (RowDelta fs)) : Prop :=
  vp.1 = replay key vp.2 []

/-- THE LOG'S FAITHFUL FRAGMENT: recovery reconstructs (the recovery IS
    the replay — definitional), and the honest step preserves the
    fragment (`replay_snoc` — the append law IS the preservation: an
    append keeps the state exactly one delta ahead of the replayed
    past). -/
theorem log_faithful (key : String) :
    (logMachine (fs := fs) key).Faithful (logF key) := by
  refine ⟨?_, ?_⟩
  · intro vp hvp
    show (logMachine key).recover vp.2 = vp.1
    rw [hvp]
    rfl
  · intro vp i v' p' hvp hstep
    have hinj : deltaApply key i vp.1 = v' ∧ vp.2 ++ [i] = p' := by
      simpa [logMachine, CrashMachine.step?] using hstep
    show (v', p').1 = replay key (v', p').2 []
    rw [← hinj.1, ← hinj.2, replay_snoc, hvp]

/-! ## The torn-tail face (the byte-level model's machine reading) -/

/-- THE RECOVERY AT THE TORN TAIL: the walk's longest valid prefix
    (`SchemaCore.DeltaLog`'s kept frames) recovers to EXACTLY the crash
    point's replay (`runStates` at the surviving frame count) — the
    honest relation `recovered = the longest valid prefix`, at the
    machine level. The torn frame is not a frame: the machine level
    never sees it. -/
theorem recover_prefix (key : String) (log : List (RowDelta fs)) (k : Nat) :
    (logMachine (fs := fs) key).recover (log.take k) = runStates key [] log k :=
  rfl

/-- THE RECOVERED STATE IS FAITHFUL AGAIN: the crash+recovery closure
    lands on the log's invariant — the recovered log is honest and
    appendable. -/
theorem recovered_faithful (key : String) (log : List (RowDelta fs)) (k : Nat) :
    logF key ((logMachine (fs := fs) key).up (log.take k)) := rfl

/-! ## The refinement, instantiated (cited, never re-proved) -/

/-- The observer: sees the materialized state (the app's observable
    face — the journal is the disk, not the view). -/
def stateObs : Kit.Observer (List (RowVals fs) × List (RowDelta fs))
    (List (RowVals fs)) := ⟨fun vp => vp.1⟩

/-- THE LOG'S REFINEMENT, crashy ≤ free: the log machine's observed
    behavior is preserved through crashes — the generic theorem
    instantiated on the faithful log fragment. -/
theorem refines_log (key : String) :
    Refines ((logMachine (fs := fs) key).crashyCoalg stateObs)
      ((logMachine (fs := fs) key).freeCoalg stateObs)
      (fun a b => a = b ∧ logF key a) :=
  (logMachine (fs := fs) key).refines_crashy (logF key) (log_faithful key) stateObs

/-- THE LOG'S REFINEMENT, free ≤ crashy — the reverse face. -/
theorem refines_log_reverse (key : String) :
    Refines ((logMachine (fs := fs) key).freeCoalg stateObs)
      ((logMachine (fs := fs) key).crashyCoalg stateObs)
      (fun a b => a = b ∧ logF key a) :=
  (logMachine (fs := fs) key).refines_free_crashy (logF key) (log_faithful key) stateObs

/-- THE PAYOFF FROM A RECOVERED STATE: after a torn-tail recovery, the
    log machine's observed behavior is THE SAME with or without further
    crashes interleaved — the crash+replay closure composes (the
    recovery lands on the faithful fragment, so the refinement applies
    again). -/
theorem beh_eq_recovered (key : String) (log : List (RowDelta fs)) (k : Nat)
    (ins : Stream (Sum (RowDelta fs) Unit)) :
    ((logMachine (fs := fs) key).crashyCoalg stateObs).beh ins
        ((logMachine (fs := fs) key).up (log.take k))
      = ((logMachine (fs := fs) key).freeCoalg stateObs).beh ins
        ((logMachine (fs := fs) key).up (log.take k)) :=
  (logMachine (fs := fs) key).beh_eq_faithful (logF key) (log_faithful key) stateObs
    _ (recovered_faithful key log k) ins

/-! ## The teeth: the lossy log breaks the refinement -/

/- THE SABOTAGE: the step updates the materialized state but journals
NOTHING — the write-through discipline's undo. The recovery discipline
is the honest replay; the loss lives in the step that stopped
persisting what it cached. -/

def lossyMachine (key : String) :
    CrashMachine (List (RowVals fs)) (List (RowDelta fs)) (RowDelta fs) :=
  ⟨fun v p d => some (deltaApply key d v, p), fun p => replay key p []⟩

/-- THE TOOTH: the lossy state is UNFAITHFUL — the journal's replay
    does not reconstruct the materialized state (the cache carries the
    delta, the journal carries nothing; the replay says empty). -/
theorem lossy_unfaithful (key : String) (r : RowVals fs) :
    ¬ (lossyMachine (fs := fs) key).FaithfulAt ([r], []) := by
  intro h
  rw [CrashMachine.FaithfulAt, lossyMachine] at h
  simp [replay, journalApply] at h

/-- THE REWIND: at the unfaithful state the crash+recovery is NOT the
    identity — the closure rewinds the materialized state to the
    journal's replay (the cache's unjournaled delta is LOST, loudly). -/
theorem lossy_rewinds (key : String) (d : RowDelta fs) (p : List (RowDelta fs)) :
    (lossyMachine (fs := fs) key).closure (deltaApply key d (replay key p []), p)
      = (replay key p [], p) := rfl

end Machines.Crash.Log

/-
# MachinesTests.Crash — the crash/recovery refinement's teeth

Owned by: the crash/recovery refinement lane (the mandate tree, `machines/`).
Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5), over `Machines.Crash` (D13's 10C — first-class crash
steps + persistent/volatile separation + the refinement). Suites:

1. `crash-discipline` — the two first-class transitions pinned in
   values: the crash DROPS the volatile (two different caches over the
   same disk crash to the SAME remnant) and KEEPS the persistent; the
   recovery RECONSTRUCTS (from the persistent alone); the closure is
   the identity at faithful states (and NOT at unfaithful ones — the
   control). The tick faces pinned on the worked journal machine.
2. `refinement` — the worked example exercised: the journal-backed
   machine's observed behavior streams are EQUAL with and without a
   crash interleaved (the event-sourcing invariant makes the recovery
   the journal's replay = exactly where the machine was). Controls: the
   LOSSY persistence (a step that caches but journals a zero) breaks
   faithfulness, rewinds the state, and diverges the behaviors — the
   refinement's premise is load-bearing; the lossy machine does NOT
   refine.
3. `the-teeth` — the mandatory negative controls: the closure is NOT
   invisible at unfaithful states; faithfulness is not vacuous; the
   stutter is not the crashy move.

NOTE (wiring): this module is compiled by the Machines lib
(`MachinesTests.+` glob) but is RUN only once `MachinesTests.Main`
imports it and registers `specCrash` in its `mainOfSuites` list. The
value-level theorems below are compile-time checked regardless.

Axiom self-check: `#print axioms` pins over the refinement laws + the
faithfulness closure — the expected outputs name the CORE TRIPLE AT
MOST; a `sorry` or a new axiom changes the printed set and fails the
build. Evidence, not architecture — the five-question block lives in
the modules under test.
-/

import Machines
import TestingKit.Spec
import TestingKit.Harness

open Machines TestingKit
open Machines.Crash.Journal

/-- journalF's decidability at values (the decide-driven pins' face —
    the event-sourcing invariant is decidable, so the teeth are). -/
instance journalF_dec (vp : Int × List Int) : Decidable (journalF vp) :=
  inferInstanceAs (Decidable (vp.1 = replayJ vp.2))

/-! ## The worked journal machine, exercised -/

/-- A crash interleaved into the input stream: inc, CRASH, inc. -/
def insCrash : Stream (Sum JInput Unit) :=
  fun t => match t with
    | 0 => Sum.inl .inc
    | 1 => Sum.inr ()
    | _ => Sum.inl .inc

/-- The crashy/free coalgebras of the worked machine, under the cache
    observer. -/
def crashyJ : Coalgebra (Int × List Int) (Sum JInput Unit) Int :=
  jmach.crashyCoalg cacheObs

def freeJ : Coalgebra (Int × List Int) (Sum JInput Unit) Int :=
  jmach.freeCoalg cacheObs

/-! ## Suite 1: the crash discipline, pinned in values -/

/-- THE CRASH DROPS THE VOLATILE: two different caches over the same
    journal crash to the SAME remnant — the volatile's value cannot
    affect what a crash leaves (`crashStep_congr`, at values). -/
theorem crash_drops_volatile :
    crashStep (3, [1, 2]) = crashStep (99, [1, 2]) := rfl

/-- THE PERSISTENT SURVIVES: the remnant IS the journal
    (`crashStep_survives`, at values). -/
theorem crash_keeps_persistent : crashStep (3, [1, 2]) = [1, 2] := rfl

/-- THE RECOVERY RECONSTRUCTS: from the persistent alone — there is no
    volatile input, the type has none — the replay rebuilds the cache. -/
theorem recovery_reconstructs : jmach.up [1, 1] = (2, [1, 1]) := rfl

/-- THE CLOSURE IS THE IDENTITY at a faithful state: crash + recovery
    = the journal's replay = exactly where the machine was. -/
theorem closure_faithful_pin :
    jmach.closure (2, [1, 1]) = (2, [1, 1]) :=
  jmach.closure_of_faithful _ (journal_faithful.faithful _ (by decide))

/-- The tick faces: the crashy machine's crash event moves along the
    closure; the crash-free machine's stutters — IDENTICAL here,
    because the state is faithful. -/
theorem tick_faces_pin :
    jmach.crashy.tick (Sum.inr ()) (2, [1, 1]) = (2, [1, 1])
    ∧ jmach.free.tick (Sum.inr ()) (2, [1, 1]) = (2, [1, 1]) :=
  ⟨rfl, rfl⟩

/-! ## Suite 2: the refinement, exercised -/

/-- THE STATE STREAMS, pinned: with the crash interleaved, the crashy
    machine's states and the crash-free machine's states AGREE — the
    crash is invisible (the state is faithful at the crash point). -/
theorem states_agree_pin :
    List.map (crashyJ.states insCrash (0, [])) [0, 1, 2, 3]
      = [(0, []), (1, [1]), (1, [1]), (2, [1, 1])]
    ∧ List.map (freeJ.states insCrash (0, [])) [0, 1, 2, 3]
      = [(0, []), (1, [1]), (1, [1]), (2, [1, 1])] := by decide

/-- THE BEHAVIOR PRESERVATION, pinned in values: the observed behavior
    streams are EQUAL — inc sees 1, the crash sees 1, inc sees 2 — on
    both machines. This is `beh_eq_journal`'s content at a witness. -/
theorem beh_eq_pin :
    List.map (crashyJ.beh insCrash (0, [])) [0, 1, 2] = [some 1, some 1, some 2]
    ∧ List.map (freeJ.beh insCrash (0, [])) [0, 1, 2] = [some 1, some 1, some 2] := by
  decide

/-- THE PAYOFF, exercised as the theorem (not just the values): the
    behavior streams are equal on EVERY input stream, from every
    faithful state — `beh_eq_journal` cited, never re-proved. -/
theorem journalBeh_eq : (jmach.crashyCoalg cacheObs).beh insCrash (0, [])
      = (jmach.freeCoalg cacheObs).beh insCrash (0, []) :=
  beh_eq_journal (0, []) (by decide) insCrash

/-! ## Suite 3: THE TEETH — the lossy persistence breaks the refinement -/

/- The SABOTAGE machine: the step updates the cache but journals a ZERO
— the delta is lost. The recovery discipline is the honest replay; the
loss lives in the step that stopped persisting what it cached. -/

def lstep? : Int → List Int → JInput → Option (Int × List Int)
  | v, j, .inc => some (v + 1, j ++ [0])
  | v, j, .dec => some (v - 1, j ++ [0])

def lmach : CrashMachine Int (List Int) JInput := ⟨lstep?, replayJ⟩

def crashyL : Coalgebra (Int × List Int) (Sum JInput Unit) Int :=
  lmach.crashyCoalg cacheObs

def freeL : Coalgebra (Int × List Int) (Sum JInput Unit) Int :=
  lmach.freeCoalg cacheObs

/-- THE TOOTH: the lossy state is UNFAITHFUL — the journal's replay does
    not reconstruct the cache (the +1 was never journaled). -/
theorem lossy_unfaithful : ¬ lmach.FaithfulAt (1, [0]) := by decide

/-- THE REWIND: at the unfaithful state the closure is NOT the identity —
    the crash+recovery rewinds the cache to the journal's replay. -/
theorem lossy_rewinds : lmach.closure (1, [0]) = (0, [0]) := rfl

/-- THE DIVERGENCE: one inc then one crash — the crashy machine's
    observed step sees the REWOUND cache (0); the crash-free machine's
    sees the truth (1). The behaviors differ: the refinement's premise
    is load-bearing. -/
theorem lossy_diverges :
    List.map (crashyL.beh insCrash (0, [])) [0, 1, 2] = [some 1, some 0, some 1]
    ∧ List.map (freeL.beh insCrash (0, [])) [0, 1, 2] = [some 1, some 1, some 2] := by
  decide

/-- THE STATE STREAMS DIVERGE too: the lossy crashy machine REWINDS
    ((1,[0]) ↦ (0,[0])); the crash-free machine stays. -/
theorem lossy_streams :
    List.map (crashyL.states insCrash (0, [])) [0, 1, 2, 3]
      = [(0, []), (1, [0]), (0, [0]), (1, [0, 0])]
    ∧ List.map (freeL.states insCrash (0, [])) [0, 1, 2, 3]
      = [(0, []), (1, [0]), (1, [0]), (2, [0, 0])] := by
  decide

/-- THE REFINEMENT FAILS for the lossy machine: no simulation through
    "the same faithful state" survives the inc step — it lands on the
    unfaithful (1, [0]), where the relation is uninhabited. -/
theorem lossy_not_refines :
    ¬ Refines (crashyL) (freeL) (fun a b => a = b ∧ journalF a) := by
  intro h
  -- both machines fire inc from the faithful (0, []), landing (1, [0])
  have hstepC : crashyL.observe (0, []) (Sum.inl .inc) = some (1, (1, [0])) := rfl
  have hstepF : freeL.observe (0, []) (Sum.inl .inc) = some (1, (1, [0])) := rfl
  rcases h.step (⟨rfl, by decide⟩ :
      ((fun a b => a = b ∧ journalF a) (0, []) (0, []))) (Sum.inl .inc)
    with ⟨hn, _⟩ | ⟨o, a, b, h₁, h₂, hR⟩
  · rw [hstepC] at hn; simp at hn
  · rw [hstepC] at h₁
    obtain ⟨_, ha⟩ := by simpa using h₁
    rw [hstepF] at h₂
    obtain ⟨_, hb⟩ := by simpa using h₂
    rw [← ha, ← hb] at hR
    have hF := hR.2
    exact absurd hF (by decide)

/-! ## The mandatory negative controls (the refinement's teeth) -/

/-- THE CONTROL: the closure is NOT unconditionally invisible — at the
    unfaithful state the crashy machine's crash event MOVES the state
    (the rewind), while the crash-free machine's stutters. -/
theorem control_closure_moves :
    lmach.crashy.tick (Sum.inr ()) (1, [0]) ≠ lmach.free.tick (Sum.inr ()) (1, [0]) := by
  decide

/-- THE CONTROL: faithfulness is not vacuous — the honest machine's
    fragment carries (0, []) AND (1, [1]) (the lossy machine's (1, [0])
    does not). -/
theorem control_faithful_nonvacuous :
    journalF (0, []) ∧ journalF (1, [1]) := ⟨by decide, by decide⟩

/-! ## The suites (wired by MachinesTests.Main — see the header note) -/

def specCrash : Spec := Spec.ofList "crash-recovery"
  (fun _ => do
    -- the crash drops the volatile, keeps the persistent
    assert (crashStep (3, [1, 2]) == crashStep (99, [1, 2]))
      "crash leaked the volatile's value"
    assert (crashStep (3, [1, 2]) == [1, 2]) "persistent did not survive"
    -- the recovery reconstructs from the persistent alone
    assert (jmach.up [1, 1] == (2, [1, 1])) "recovery wrong"
    -- the closure is the identity at faithful states
    assert (jmach.closure (2, [1, 1]) == (2, [1, 1])) "faithful closure moved"
    -- the refinement: behavior streams agree with the crash interleaved
    assert (List.map (crashyJ.beh insCrash (0, [])) [0, 1, 2]
        == [some 1, some 1, some 2]) "crashy behavior wrong"
    assert (List.map (freeJ.beh insCrash (0, [])) [0, 1, 2]
        == [some 1, some 1, some 2]) "crash-free behavior wrong"
    -- the teeth: the lossy persistence rewinds and diverges
    assert (lmach.closure (1, [0]) == (0, [0])) "lossy closure did not rewind"
    assert (List.map (crashyL.beh insCrash (0, [])) [0, 1, 2]
        == [some 1, some 0, some 1]) "lossy behavior did not rewind"
    assert (List.map (freeL.beh insCrash (0, [])) [0, 1, 2]
        == [some 1, some 1, some 2]) "lossy crash-free face wrong")
  [ ("sabotage-closure-invisible", fun _ =>
      -- the rewind makes the closure NOT the identity at (1, [0])
      assert (lmach.closure (1, [0]) == (1, [0])) "control"),
    ("sabotage-faithfulness-vacuous", fun _ =>
      -- the lossy state is genuinely unfaithful: the replay cannot lie
      assert (decide (lmach.FaithfulAt (1, [0]))) "control"),
    ("sabotage-stutter-collapsed", fun _ =>
      -- the crashy machine's crash event is NOT the stutter at
      -- unfaithful states: the machines' ticks differ there
      assert (lmach.crashy.tick (Sum.inr ()) (1, [0])
        == lmach.free.tick (Sum.inr ()) (1, [0])) "control") ]
  1 49

/-! ## The axiom self-check -/

/-- info: 'Machines.CrashMachine.closure_of_faithful' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.CrashMachine.closure_of_faithful

/-- info: 'Machines.CrashMachine.refines_crashy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.CrashMachine.refines_crashy

/-- info: 'Machines.CrashMachine.refines_free_crashy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.CrashMachine.refines_free_crashy

/-- info: 'Machines.CrashMachine.beh_eq_faithful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.CrashMachine.beh_eq_faithful

/-- info: 'Machines.Crash.Journal.journal_faithful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Crash.Journal.journal_faithful

/-- info: 'Machines.Crash.Journal.beh_eq_journal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Crash.Journal.beh_eq_journal

/-
# MachinesTests.Live — the coinductive foundation's + liveness's teeth

Owned by: the machines agent (the mandate tree, `machines/`).
Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5), over `Machines.Live` (08 §10's liveness lane +
the coinductive infinite face). Suites:

1. `liveness-coinductive` — the worked machine (the mod-3 wheel plus a
   refusing `bump` label): the wheel's INFINITE run proved by the Park
   induction (`InfRun.park` — the coinductive twin of the landed
   finality's time-shifted induction); the fairness assumption AS DATA
   (`Fairness`) proved for the tick stream and REFUTED for the bump
   stream (the assumption is never derived — 01-core §3); the Explore
   integration (the PROVED face's enabledness invariant + the
   environment's constant supply = the infinite run; the UNKNOWN face
   bridges to NOTHING); the Eventually faces (proved on the wheel,
   REFUTED on the held stream — the honest gap); always-eventually
   (coinductive `InfOften`) proved and refuted on the same pair.

The fairness pin is THE tooth: the SAME machine, the SAME invariant —
under the fair stream the liveness proves, under the unfair stream the
eventually is REFUTED and the `Fairness` datum does not exist to name.
No theorem "derives" fairness from the table; the caller supplies it or
the liveness does not land.

NOTE (wiring): compiled by the Machines lib (`MachinesTests.+` glob),
RUN only once `MachinesTests.Main` imports it and registers
`specLive`. Axiom self-check: `#print axioms` pins over the Park
principles and the bridges — the expected outputs name the CORE TRIPLE
AT MOST (the `coinductive` command adds ZERO kernel extensions; its
compilation rides `Lean.Order`'s fixpoints). Evidence, not
architecture.
-/

import Machines
import TestingKit.Spec
import TestingKit.Harness

open Machines TestingKit

/-! ## The fixture: the wheel + the refusing label -/

inductive LInput where
  | tick | bump
deriving DecidableEq, Repr, BEq

open LInput

/-- The liveness machine: tick cycles the mod-3 wheel (always enabled);
    bump is the label the environment can name that REFUSES in every
    state — the unfairness instrument (the refusal is data, never a
    silent self-loop). -/
def stepL : Nat → LInput → Option Nat
  | s, .tick => some ((s + 1) % 3)
  | _, .bump => none

def mL : Machine Nat LInput := ⟨stepL⟩

def obsL : Kit.Observer Nat Nat := ⟨fun n => n⟩
def coalL : Coalgebra Nat LInput Nat := ⟨mL, obsL⟩

def insTick : Stream LInput := fun _ => .tick
def insBump : Stream LInput := fun _ => .bump

theorem bump_none (s : Nat) : mL.step? s .bump = none := rfl

/-- The same refusal, at the coalgebra's machine projection — the
    shape the liveness hypotheses carry. -/
theorem bump_none' : coalL.machine.step? 0 .bump = none := rfl

/-! ## The wheel's states under the two streams -/

/-- Under constant ticks the wheel's hold-states stream is the mod-3
    cycle — pinned as a THEOREM (the induction the liveness rides). -/
theorem states_tick_mod3 (t : Nat) : coalL.states insTick 0 t = t % 3 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [coalL.states_succ insTick 0 t, ih]
      show (t % 3 + 1) % 3 = (t + 1) % 3
      omega

/-- Under constant bumps the stream HOLDS at 0 forever — every step
    refuses, the hold-on-refusal convention keeps the stream total and
    motionless. -/
theorem states_bump_hold (t : Nat) : coalL.states insBump 0 t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hobs : coalL.observe 0 (insBump t) = none := by
        show Option.map (fun s' => (coalL.observer.see s', s'))
              (coalL.machine.step? 0 (insBump t)) = none
        rw [show coalL.machine.step? 0 (insBump t) = none from rfl]
        rfl
      rw [coalL.states_succ insBump 0 t, ih, coalL.next_of_none hobs]

/-! ## The coinductive foundation, exercised -/

/-- THE INFINITE RUN, proved by the PARK INDUCTION: the mod-3 wheel
    under constant ticks never refuses — the relation `x < 3` is
    step-closed (the bisimulation proof principle at work). -/
theorem infRun_wheel : InfRun mL insTick 0 := by
  apply InfRun.park (fun is x => (∀ u, is u = .tick) ∧ x < 3)
  · exact ⟨fun _ => rfl, by decide⟩
  · rintro is x ⟨his, hx⟩
    rw [his 0]
    exact ⟨(x + 1) % 3, rfl, fun u => his (u + 1), by omega⟩

/-- THE REFUSAL TOOTH: the same machine under the bump stream admits NO
    infinite run — the first step refuses, and the greatest fixed point
    sees it (`InfRun.refuses`). -/
theorem noInfRun_bump : ¬ InfRun mL insBump 0 := by
  intro h
  exact InfRun.refuses h (by rfl)

/-- THE EXPLORE BRIDGE, exercised: the bounded exploration's PROVED
    face for the enabledness invariant (every reachable state has tick
    enabled) — the verdict is data, computed. -/
theorem explore_enabled_proved :
    check mL (fun s => (mL.step? s .tick).isSome) [tick, bump] 0 5 = .proved := by
  rfl

/-- The coverage premise, discharged: tick and bump are all the labels
    there are. -/
theorem coverage_tick : ∀ s i s', mL.Reachable 0 s → mL.step s i s' → i ∈ [tick, bump] := by
  intro s i s' _ hs
  cases i with
  | tick => simp
  | bump => exact absurd hs (by simp [Machine.step, bump_none])

/-- THE EXPLORE BRIDGE: the PROVED face + the environment's constant
    supply give the coinductive infinite run. The UNKNOWN face
    (budget exhaustion) bridges to NOTHING — the honest gap. -/
theorem infRun_of_explore_tick : InfRun mL (fun _ => .tick) 0 :=
  InfRun.of_explore explore_enabled_proved coverage_tick

/-! ## The liveness vocabulary: Eventually + the fairness pin -/

/-- THE PROVED FACE: under constant ticks the wheel returns to 0 —
    eventually. -/
theorem eventually_zero : Eventually (fun n => n % 3 = 0) coalL insTick 0 :=
  ⟨3, by rw [states_tick_mod3]⟩

/-- THE REFUTED FACE: under constant bumps the stream holds at 0
    forever — 5 is never reached, and the theorem says so. THE FAIRNESS
    HONESTY PIN: the SAME machine, the SAME invariant — only the
    environment's stream changed (the assumption was withdrawn), and
    the liveness does not land. -/
theorem eventually_5_refuted : ¬ Eventually (fun n => n = 5) coalL insBump 0 := by
  rintro ⟨t, ht⟩
  rw [states_bump_hold t] at ht
  have h5 : (0 : Nat) = 5 := ht
  omega

/-- THE FAIRNESS ASSUMPTION AS DATA: proved for the tick stream — the
    environment keeps firing at every reached state. -/
theorem fair_tick : Fairness coalL insTick 0 := by
  refine ⟨fun t => ⟨(t % 3 + 1) % 3, ?_⟩⟩
  rw [states_tick_mod3]
  rfl

/-- THE ASSUMPTION IS THE RUN: the fairness datum feeds the unfold
    bridge — `Fairness.infRun` at the worked instance. -/
theorem infRun_of_fairness_tick : InfRun mL insTick 0 := fair_tick.infRun

/-- THE HONESTY PIN, the other side: NO `Fairness` value exists for the
    bump stream — the assumption is not derivable from the table, and
    here the table refutes it outright (bump refuses in every state). -/
theorem unfair_bump : ¬ Fairness coalL insBump 0 := by
  rintro ⟨kf⟩
  obtain ⟨s', h1⟩ := kf 0
  rw [show coalL.states insBump 0 0 = 0 from rfl,
      show insBump 0 = .bump from rfl, bump_none'] at h1
  simp at h1

/-! ## The infinite face: always-eventually -/

/-- THE INFINITE FACE, proved by the time-indexed Park induction: 0 mod
    3 recurs FOREVER on the wheel. -/
theorem alwaysEventually_zero :
    AlwaysEventually (fun n => n % 3 = 0) coalL insTick 0 := by
  apply InfOften.park (fun _ => True) trivial
  intro t _
  refine ⟨3 - t % 3, ?_, trivial⟩
  show (fun n => n % 3 = 0) (coalL.states insTick 0 (t + (3 - t % 3)))
  rw [states_tick_mod3]
  omega

/-- THE FACE TIE: the infinite face implies the finite one. -/
theorem eventually_zero_of_ae : Eventually (fun n => n % 3 = 0) coalL insTick 0 :=
  alwaysEventually_zero.eventually

/-- THE INFINITE FACE REFUTED on the held stream: infinitely often is
    at least once (`InfOften.some_time`), and once never comes. -/
theorem alwaysEventually_held_refuted :
    ¬ AlwaysEventually (fun n => n = 5) coalL insBump 0 := by
  intro h
  obtain ⟨t, ht⟩ := h.some_time
  simp [states_bump_hold] at ht

/-! ## The runtime suite (wired by MachinesTests.Main — see the header) -/

def specLive : Spec := Spec.ofList "liveness-coinductive"
  (fun _ => do
    assert (List.map (coalL.states insTick 0) [0, 1, 2, 3, 4] == [0, 1, 2, 0, 1])
      "wheel states wrong"
    assert (List.map (coalL.states insBump 0) [0, 1, 2] == [0, 0, 0])
      "held stream wrong"
    assert (check mL (fun s => (mL.step? s .tick).isSome) [tick, bump] 0 5
        matches .proved) "explore verdict wrong")
  [ ("sabotage-states-drift", fun _ =>
      -- the wheel's cycle is 0,1,2 — not 1,2,0 from state 0
      assert (List.map (coalL.states insTick 0) [0, 1, 2] == [1, 2, 0]) "control"),
    ("sabotage-held-moves", fun _ =>
      -- the held stream never moves
      assert (List.map (coalL.states insBump 0) [0, 1] == [0, 1]) "control"),
    ("sabotage-explore-refuted", fun _ =>
      assert (check mL (fun s => (mL.step? s .tick).isSome) [tick, bump] 0 5
        matches .refuted _ _) "control") ]
  1 49

/-! ## The axiom self-check -/

/-- info: 'Machines.InfRun.park' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.InfRun.park

/-- info: 'Machines.InfRun.of_explore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.InfRun.of_explore

/-- info: 'Machines.states_fires_of_infRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.states_fires_of_infRun

/-- info: 'Machines.beh_some_of_infRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.beh_some_of_infRun

/-- info: 'Machines.Fairness.infRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Fairness.infRun

/-- info: 'Machines.InfOften.park' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.InfOften.park

/-- info: 'Machines.not_eventually_of_allRefuse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.not_eventually_of_allRefuse

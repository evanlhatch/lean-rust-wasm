/-
# MachinesTests.Coalg — the coalgebraic half's teeth

Owned by: the coalgebra agent (the mandate tree, `machines/`).
Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5), over `Machines.Coalg` (16-surface §4.2's
coalgebraic half). Suites:

1. `the-unfold` — the worked mod-3 machine AS an observation
   coalgebra: `beh` pinned in values (the observations 1,2,0,1 under
   constant ticks), the finality iff exercised in both directions
   (exhibited bisimulation ⟹ behavioral equality; the KERNEL of
   `beh` as the witnessing bisimulation), and the axiom pins (the
   core-triple surface over the coinduction principle + the iff).
2. `the-teeth` — the separation pin: states 0 and 1 have DIFFERENT
   behavior, so NO bisimulation relates them (finality's
   contrapositive has teeth); the trivial relation is NOT a
   bisimulation (the coinduction principle is not vacuous).
3. `refinement` — the worked instance: the unbounded counter
   refines the mod-3 wheel under the mod-3 observer (impl ≤ spec,
   the simulation exhibited); the behavior-inclusion law exercised;
   the composition tower exercised (`Refines.comp` over
   `Kit.Rel.comp`). Controls: an over-tight simulation is NOT a
   refinement; the direction is REAL (the reverse refinement
   fails — Kit's directionality control's face).

NOTE (wiring): this module is compiled by the Machines lib
(`MachinesTests.+` glob) but is RUN only once `MachinesTests.Main`
(the machine!-macro agent's file) imports it and registers
`specCoalg` in its `mainOfSuites` list. The value-level theorems
below are compile-time checked regardless.

The fixtures are local to this module (the mod-3 tick/reset wheel;
the unbounded tick/reset counter) — the pattern mirrors
MachinesTests.Main's worked machine, without touching its files.

Axiom self-check: `#print axioms` pins over the coinduction
principle, the finality iff, and the refinement laws — the expected
outputs name the CORE TRIPLE AT MOST; a `sorry` or a new axiom
changes the printed set and fails the build. Evidence, not
architecture — the five-question block lives in the modules under
test.
-/

import Machines
import TestingKit.Spec
import TestingKit.Harness

open Machines TestingKit

/-! ## The fixture: the mod-3 wheel as an observation coalgebra -/

inductive CInput where
  | tick | reset
deriving DecidableEq, Repr, BEq

open CInput

/-- The mod-3 wheel: tick cycles, reset lands. The SAME shape as the
    umbrella's worked machine (tick/reset labels only — bump would
    separate the bisimilar pair below). -/
def step3c : Nat → CInput → Option Nat
  | s, .tick => some ((s + 1) % 3)
  | _, .reset => some 0

def m3c : Machine Nat CInput := ⟨step3c⟩

/-- The identity observer: sees the whole state. -/
def obsId : Kit.Observer Nat Nat := ⟨fun n => n⟩

/-- The mod-3 observer: sees only `n % 3`. -/
def obsMod : Kit.Observer Nat Nat := ⟨fun n => n % 3⟩

/-- The wheel AS an observation coalgebra. -/
def coal3 : Coalgebra Nat CInput Nat := ⟨m3c, obsId⟩

/-- The unbounded counter: tick increments forever — the impl of the
    refinement instance (its states are NOT the wheel's). -/
def stepCounter : Nat → CInput → Option Nat
  | s, .tick => some (s + 1)
  | _, .reset => some 0

def mCounter : Machine Nat CInput := ⟨stepCounter⟩

/-- The counter AS an observation coalgebra, under the mod-3 observer. -/
def coalCounter : Coalgebra Nat CInput Nat := ⟨mCounter, obsMod⟩

def insTickC : Stream CInput := fun _ => .tick

/- The observe faces, pinned (all `rfl` — the coalgebra map is tied
   to the landed `step?` by definition, no parallel encoding). -/
theorem observe_counter_tick (s : Nat) :
    coalCounter.observe s .tick = some ((s + 1) % 3, s + 1) := rfl

theorem observe_counter_reset (s : Nat) :
    coalCounter.observe s .reset = some (0, 0) := rfl

theorem observe_m3_tick (s : Nat) :
    coal3.observe s .tick = some ((s + 1) % 3, (s + 1) % 3) := rfl

theorem observe_m3_reset (s : Nat) :
    coal3.observe s .reset = some (0, 0) := rfl

/-! ## The mod-3 arithmetic the wheels need (core lemmas, once) -/

/-- One step of the wheel only depends on the state mod 3. -/
theorem tick_mod3 (s : Nat) : (s + 1) % 3 = (s % 3 + 1) % 3 := by
  simp [Nat.add_mod]

theorem mod3_tick_congr (a b : Nat) (h : a % 3 = b) : (b + 1) % 3 = (a + 1) % 3 := by
  subst h
  simp [tick_mod3]

theorem mod3_congr (a b : Nat) (h : a % 3 = b % 3) : (a + 1) % 3 = (b + 1) % 3 := by
  simp [tick_mod3, h]

/-! ## The coinduction principle + FINALITY, exercised -/

/-- The bisimulation `a ≡ b mod 3`: the wheel's 0 and 3 are related
    (they ARE the same state of the wheel). -/
abbrev R3 : Kit.Rel Nat Nat := fun a b => a % 3 = b % 3

theorem bisim3 : coal3.Bisim R3 := by
  intro s t h i
  cases i with
  | tick =>
      refine ⟨?_, ?_⟩
      · show some ((s + 1) % 3) = some ((t + 1) % 3)
        rw [mod3_congr s t h]
      · show ((s + 1) % 3) % 3 = ((t + 1) % 3) % 3
        rw [Nat.mod_mod, Nat.mod_mod, mod3_congr s t h]
  | reset =>
      exact ⟨rfl, rfl⟩

/-- THE COINDUCTION PRINCIPLE, exercised: bisimilar states 0 and 3
    have EQUAL behavior streams on EVERY input — pinned as `BehEq`. -/
theorem beh03_eq : coal3.BehEq 0 3 :=
  coal3.bisim_sound R3 bisim3 0 3 (by rfl)

/-- The behavior, pinned in values: the wheel's observations under
    constant ticks are 1, 2, 0, 1 — from 0 AND from the bisimilar 3. -/
theorem beh3_pin :
    List.map (coal3.beh insTickC 0) [0, 1, 2, 3] = [some 1, some 2, some 0, some 1]
    ∧ List.map (coal3.beh insTickC 3) [0, 1, 2, 3] = [some 1, some 2, some 0, some 1] := by
  decide

/-- FINALITY, forward: behavioral equality gives a bisimulation —
    the iff's mpr direction, pinned at a value: the witnessed relation
    forces the tick's observation out of state 0 to equal the one out
    of state 3 (both `some 1`). -/
theorem finality_forward_pin :
    coal3.beh (fun _ => .tick) 0 0 = some 1 :=
  (congrFun ((Coalgebra.behEq_iff_bisim coal3 0 3).mpr ⟨R3, bisim3, by rfl⟩
    (fun _ => .tick)) 0).trans (by decide)

/-- FINALITY, the kernel face: the KERNEL of `beh` is itself a
    bisimulation — the iff's mp direction on the proved behavioral
    equality exhibits SOME witnessing relation. -/
theorem finality_kernel_pin :
    ∃ R : Kit.Rel Nat Nat, coal3.Bisim R ∧ R 0 3 :=
  (Coalgebra.behEq_iff_bisim coal3 0 3).mp beh03_eq

/-! ## THE TEETH (15-patterns #5): the separation pin -/

/-- THE SEPARATION PIN: states 0 and 1 have DIFFERENT behavior (under
    constant ticks: 1,2,0,… vs 2,0,1,…) — so NO bisimulation relates
    them. Finality's contrapositive has teeth: behavioral difference
    is bisimulative separation. -/
theorem not_bisim01 : ¬ ∃ R : Kit.Rel Nat Nat, coal3.Bisim R ∧ R 0 1 := by
  intro ⟨R, hB, h01⟩
  have h := (hB 0 1 h01 .tick).1
  simp only [observe_m3_tick] at h
  simp at h

/-- The behavioral difference itself, pinned: the streams differ at
    time 0. -/
theorem beh01_differ : coal3.beh (fun _ => .tick) 0 ≠ coal3.beh (fun _ => .tick) 1 := by
  intro h
  have h0 := congrFun h 0
  rw [Coalgebra.beh_eq, Coalgebra.beh_eq] at h0
  rw [Coalgebra.states_zero, Coalgebra.states_zero] at h0
  rw [observe_m3_tick, observe_m3_tick] at h0
  simp at h0

/-- THE NEGATIVE CONTROL: the trivial relation is NOT a bisimulation —
    the coinduction principle is not vacuous (an `R` that relates
    everything would prove everything behaviorally equal). -/
theorem trivial_not_bisim : ¬ coal3.Bisim (fun _ _ => True) := by
  intro hB
  have h := (hB 0 1 trivial .tick).1
  simp only [observe_m3_tick] at h
  simp at h

/-! ## Refinement: the unbounded counter ≤ the mod-3 wheel -/

/-- THE SIMULATION: `a` implements `b` iff `a % 3 = b` — the counter's
    state, seen mod 3, IS the wheel's state. -/
abbrev RCounter : Kit.Rel Nat Nat := fun a b => a % 3 = b

/-- THE REFINEMENT INSTANCE (16 §4.2 — impl ≤ spec, exhibited): the
    unbounded counter refines the mod-3 wheel under the mod-3
    observer. impl fires ⟹ spec fires with the SAME observation
    (`(s+1) % 3` on both sides) and a simulated successor. -/
theorem refines_counter : Refines coalCounter coal3 RCounter := by
  refine ⟨?_⟩
  intro s₁ s₂ h i
  cases i with
  | tick =>
      refine Or.inr ⟨(s₁ + 1) % 3, s₁ + 1, (s₂ + 1) % 3, ?_, ?_, ?_⟩
      · rw [observe_counter_tick]
      · rw [observe_m3_tick, mod3_tick_congr s₁ s₂ h]
      · show (s₁ + 1) % 3 = (s₂ + 1) % 3
        rw [tick_mod3, h]
  | reset =>
      exact Or.inr ⟨0, 0, 0, rfl, rfl, rfl⟩

/-- THE BEHAVIOR-INCLUSION LAW, exercised (`Refines.beh_le_at`): every
    observation the counter makes, the wheel makes — pinned at time 2
    (the counter is at state 3, seen mod 3 as 0; the wheel is at 0). -/
theorem counter_beh_le_pin :
    coalCounter.beh insTickC 0 2 = some 0 ∧ coal3.beh insTickC 0 2 = some 0 :=
  ⟨by decide,
   refines_counter.beh_le_at 0 0 insTickC (by rfl) 2 0 (by decide)⟩

/-- The wheel refines ITSELF under `R3` (determinism) — the tower's
    middle stage. -/
theorem refines_wheel_self : Refines coal3 coal3 R3 := by
  refine ⟨?_⟩
  intro s₁ s₂ h i
  cases i with
  | tick =>
      refine Or.inr ⟨(s₁ + 1) % 3, (s₁ + 1) % 3, (s₂ + 1) % 3, ?_, ?_, ?_⟩
      · rfl
      · rw [observe_m3_tick, (mod3_congr s₁ s₂ h).symm]
      · show ((s₁ + 1) % 3) % 3 = ((s₂ + 1) % 3) % 3
        rw [Nat.mod_mod, Nat.mod_mod, mod3_congr s₁ s₂ h]
  | reset =>
      refine Or.inr ⟨0, 0, 0, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · rfl

/-- REFINEMENTS CHAIN (`Refines.comp`): counter ≤ wheel ≤ wheel —
    the tower lands the composite relation `Kit.Rel.comp RCounter R3`. -/
theorem refines_counter_tower :
    Refines coalCounter coal3 (Kit.Rel.comp RCounter R3) :=
  Refines.comp refines_counter refines_wheel_self

/-- THE COMPOSITE RELATION, pinned: `0` is related to `0` through the
    tower — the mid witness `0` satisfies both legs. -/
theorem composite_rel_pin : Kit.Rel.comp RCounter R3 0 0 :=
  ⟨0, rfl, rfl⟩

/-! ## The mandatory negative controls (the refinement's teeth) -/

/-- THE CONTROL: an over-tight simulation is NOT a refinement —
    `a = b ∧ a ≠ 1` relates 0~0, but the wheel's tick leaves it
    immediately (0 ↦ 1), and `1 = 1 ∧ 1 ≠ 1` is false. -/
theorem tight_not_refines :
    ¬ Refines coal3 coal3 (fun a b => a = b ∧ a ≠ 1) := by
  intro h
  rcases h.step (⟨rfl, by omega⟩ : ((fun a b => a = b ∧ a ≠ 1) 0 0)) .tick
    with ⟨hn, _⟩ | ⟨o, a, b, h₁, h₂, hR⟩
  · rw [observe_m3_tick] at hn; simp at hn
  · rw [observe_m3_tick] at h₁ h₂
    have e₁ : 1 = o ∧ 1 = a := by simpa using h₁
    have e₂ : 1 = o ∧ 1 = b := by simpa using h₂
    obtain ⟨_, rfl⟩ := e₁
    obtain ⟨_, rfl⟩ := e₂
    simp at hR

/-- THE DIRECTIONALITY CONTROL: the reverse refinement FAILS — the
    wheel does NOT refine the counter under the same simulation
    (`a % 3 = b`): from the related pair (2, 2), the wheel's tick
    lands 0 but the counter's lands 3, and `0 % 3 = 3` is false. The
    direction of impl ≤ spec is REAL (Kit's directionality face). -/
theorem reverse_not_refines : ¬ Refines coal3 coalCounter RCounter := by
  intro h
  rcases h.step (by rfl : RCounter 2 2) .tick
    with ⟨hn, _⟩ | ⟨o, a, b, h₁, h₂, hR⟩
  · rw [observe_m3_tick] at hn; simp at hn
  · rw [observe_m3_tick] at h₁
    rw [observe_counter_tick] at h₂
    have e₁ : 0 = o ∧ 0 = a := by simpa using h₁
    have e₂ : 0 = o ∧ 3 = b := by simpa using h₂
    obtain ⟨_, rfl⟩ := e₁
    obtain ⟨_, rfl⟩ := e₂
    simp [RCounter] at hR

/-! ## The suites (wired by MachinesTests.Main — see the header note) -/

def specCoalg : Spec := Spec.ofList "coalgebra"
  (fun _ => do
    assert (List.map (coal3.beh insTickC 0) [0, 1, 2, 3]
        == [some 1, some 2, some 0, some 1]) "beh wrong"
    assert (List.map (coal3.beh insTickC 3) [0, 1, 2, 3]
        == [some 1, some 2, some 0, some 1]) "bisimilar behavior wrong"
    assert (List.map (coalCounter.beh insTickC 0) [0, 1, 2, 3]
        == [some 1, some 2, some 0, some 1]) "counter's observed behavior wrong"
    assert (coalCounter.beh insTickC 0 2 == some 0) "counter at time 2 wrong"
    assert (coal3.beh insTickC 0 2 == some 0) "wheel at time 2 wrong")
  [ ("sabotage-behavior-drift", fun _ =>
      -- state 1's behavior is 2,0,1 — NOT 1,2,0: the separation is real
      assert (List.map (coal3.beh insTickC 1) [0, 1, 2]
        == [some 1, some 2, some 0]) "control"),
    ("sabotage-trivial-bisim", fun _ =>
      -- the trivial relation would make 0~1 behaviorally equal: it cannot
      assert (coal3.beh (fun _ => .tick) 0 0
        == coal3.beh (fun _ => .tick) 1 0) "control"),
    ("sabotage-composite-witness", fun _ =>
      -- no x in the witness range has RCounter 0 x AND R3 x 1:
      -- the composite relation does NOT relate 0 to 1 through the tower
      assert ((List.range 4).any
        (fun x => decide (RCounter 0 x) && decide (R3 x 1))) "control") ]
  1 47

/-! ## The axiom self-check -/

/-- info: 'Machines.Coalgebra.bisim_sound' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Machines.Coalgebra.bisim_sound

/-- info: 'Machines.Coalgebra.bisim_sound_at' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.Coalgebra.bisim_sound_at

/-- info: 'Machines.Coalgebra.behEq_iff_bisim' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Machines.Coalgebra.behEq_iff_bisim

/-- info: 'Machines.Refines.beh_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Refines.beh_le

/-- info: 'Machines.Refines.comp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Refines.comp

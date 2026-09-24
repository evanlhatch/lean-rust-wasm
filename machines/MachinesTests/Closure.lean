/-
# MachinesTests.Closure — the closure bridge, exercised both ways

The worked machine's reachability computed TWICE — once by the frontier
fold (`Machines.Testing.reachableStates`), once by the Datalog LFP
evaluator (`Datalog.eval` over the machine-as-rules encoding,
`Machines.Closure`) — and pinned EQUAL, state by state. The bridge
THEOREM (`Machines.Closure.bridge`) is exercised at the instance: all
its premises discharged, the agreement becomes an iff over ALL states.

Negative controls (15-patterns #5), one per premise family:
- the CLOSEDNESS of the extraction (`hclosed`): a fragment list missing
  a reachable state silently truncates the closure — the fold still
  finds the state, the closure does not (the agreement FAILS);
- the INIT FACT: drop `state(init)` from the EDB — nothing derives
  (the rules' bodies need the state fact);
- the FUEL: an under-fueled fold reports the honest `none` while the
  Datalog side needs no budget premise (its fuel IS the height bound
  by construction — `Datalog.height`, pinned live here).

The fixture: the mod-3 tick cycle + reset + the never-reachable bump
(the same shape as Main.lean's worked machine, restated here — the
closure-bridge suite is self-contained so it can evolve independently).
-/

import Machines
import Datalog
import TestingKit.Spec

open Machines Machines.Closure TestingKit

/-! ## The fixture -/

inductive TInput3 where
  | tick | bump | reset
deriving DecidableEq, Repr, BEq

/-- The worked machine: the mod-3 tick cycle + reset + the
    reachable-only-at-7 bump. -/
def step3cl : Nat → TInput3 → Option Nat
  | 7, .bump => some 10
  | _, .bump => none
  | s, .tick => some ((s + 1) % 3)
  | _, .reset => some 0

def m3cl : Machines.Machine Nat TInput3 := ⟨step3cl⟩

def inputs3cl : List TInput3 := [.tick, .bump, .reset]

/-- The enumerated fragment: the closed reachable candidate set. -/
def states3cl : List Nat := [0, 1, 2]

/-! ## The bridge's premises, discharged -/

theorem hinit3 : (0 : Nat) ∈ states3cl := by decide

theorem hclosed3 : ∀ s ∈ states3cl, ∀ i ∈ inputs3cl, ∀ s',
    m3cl.step? s i = some s' → s' ∈ states3cl := by
  intro s hs i _ s' hstep
  simp only [states3cl, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl
  · cases i <;> simp [m3cl, step3cl, states3cl] at hstep ⊢ <;> omega
  · cases i <;> simp [m3cl, step3cl, states3cl] at hstep ⊢ <;> omega
  · cases i <;> simp [m3cl, step3cl, states3cl] at hstep ⊢ <;> omega

theorem hinputs3 : ∀ s i s', m3cl.Reachable 0 s → m3cl.step? s i = some s' →
    i ∈ inputs3cl := by
  intro _ i _ _ _; cases i <;> simp [inputs3cl]

/-! ## The two engines, computed -/

/-- The machine-as-rules encoding of the worked machine. -/
def P3 : Datalog.Program (MVal Nat TInput3) := programOf m3cl states3cl inputs3cl

def E3 : List (Datalog.Atom (MVal Nat TInput3)) := edbOf (0 : Nat) inputs3cl

/-- The Datalog closure: the LFP evaluator's output, computed. -/
def ev3 : List (Datalog.Atom (MVal Nat TInput3)) := Datalog.eval P3 E3

set_option maxRecDepth 100000 in
/-- THE FOLD, computed: the frontier stabilizes at the reachable
    fragment {0, 1, 2} (three rounds — one per fresh state). -/
theorem fold3 :
    Machines.Testing.reachableStates m3cl inputs3cl 0 5 = some [0, 1, 2] := by
  decide

set_option maxRecDepth 100000 in
/-- THE CLOSURE, computed: the evaluator derives EXACTLY the three
    reachable states' facts — and nothing else over the fragment. -/
theorem closure3 :
    (⟨stPred, [Sum.inl (0 : Nat)]⟩ ∈ ev3)
    ∧ (⟨stPred, [Sum.inl 1]⟩ ∈ ev3)
    ∧ (⟨stPred, [Sum.inl 2]⟩ ∈ ev3)
    ∧ ¬(⟨stPred, [Sum.inl 5]⟩ ∈ ev3)
    ∧ ¬(⟨stPred, [Sum.inl 7]⟩ ∈ ev3) := by
  decide

set_option maxRecDepth 100000 in
/-- THE FUEL/HEIGHT RELATIONSHIP, pinned: the fold's budget is the
    caller's (2 rounds under-fuel a 3-state fragment — the honest
    `none`; 3 rounds suffice); the Datalog side consumes its OWN
    theoretic fuel `Datalog.height` by construction — no budget
    premise on that side. -/
theorem fuel3 :
    Machines.Testing.reachableStates m3cl inputs3cl 0 2 = none
    ∧ Machines.Testing.reachableStates m3cl inputs3cl 0 3 = some [0, 1, 2]
    ∧ 0 < Datalog.height P3 E3 := by
  decide

/-! ## THE BRIDGE, exercised as a theorem -/

/-- THE BRIDGE at the instance: for EVERY state (not a sample — the
    theorem, with all premises discharged), fold-membership and
    closure-membership agree. This is the payoff's alternative
    evaluation path: ONE Datalog evaluation answers every
    reachability question the fold would. -/
theorem bridge3_all (s : Nat) :
    s ∈ [0, 1, 2] ↔ ⟨stPred, [Sum.inl s]⟩ ∈ ev3 :=
  (bridge m3cl states3cl inputs3cl 0 5 hinit3 hclosed3 hinputs3 [0, 1, 2]
    fold3 s)

/-- check_proved's content, re-expressed through the closure: the
    invariant `n < 3` holds on every state the closure derives, so it
    holds on every reachable state (`Machines.Closure.inv_of_eval`) —
    WITHOUT consuming the fold. -/
theorem payoff3_reachable (s : Nat) (hr : m3cl.Reachable 0 s) : s < 3 := by
  have hinv : ∀ s : Nat, ⟨stPred, [Sum.inl s]⟩ ∈ ev3 →
      (fun n => decide (n < 3)) s = true := by
    intro s h
    have hmem : s ∈ ([0, 1, 2] : List Nat) := bridge3_all s |>.2 h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> simp
  have := inv_of_eval m3cl states3cl inputs3cl 0 hinit3 hclosed3 hinputs3
    (fun n => decide (n < 3)) hinv s hr
  simpa using this

/-- The two verdict paths agree on the worked machine: the fold-based
    check PROVED, and the closure-based re-expression PROVED the same
    invariant on the same fragment. -/
theorem bothPaths3 :
    check m3cl (fun n => n < 3) inputs3cl 0 5 = .proved := by rfl

/-! ## The negative controls (15-patterns #5) -/

set_option maxRecDepth 100000 in
/-- SABOTAGED FRAGMENT: the closedness premise is load-bearing. With
    the fragment missing reachable state 1, the extraction misses every
    transition OUT of 1 — the closure truncates at {0, 1} while the
    fold (which needs no fragment) still reaches 2. The agreement
    FAILS — exactly the hole `hclosed` seals. -/
def Psab : Datalog.Program (MVal Nat TInput3) := programOf m3cl [0, 2] inputs3cl

set_option maxRecDepth 100000 in
theorem closedness_sabotaged :
    (2 : Nat) ∈ (Machines.Testing.reachableStates m3cl inputs3cl 0 5).getD []
    ∧ ¬(⟨stPred, [Sum.inl 2]⟩ ∈ Datalog.eval Psab E3) := by
  refine ⟨by simp [fold3], ?_⟩
  decide

set_option maxRecDepth 100000 in
/-- SABOTAGED EDB: drop the initial state's fact — nothing derives (the
    ground rules' bodies need a state fact; the `in` facts alone are
    inert). The closure's State projection is EMPTY while the fragment
    is {0, 1, 2}. -/
def EnoInit : List (Datalog.Atom (MVal Nat TInput3)) :=
  inputs3cl.map (fun i => ⟨inPred, [Sum.inr i]⟩)

set_option maxRecDepth 100000 in
theorem init_fact_sabotaged :
    ¬(⟨stPred, [Sum.inl (0 : Nat)]⟩ ∈ Datalog.eval P3 EnoInit)
    ∧ ¬(⟨stPred, [Sum.inl 1]⟩ ∈ Datalog.eval P3 EnoInit) := by
  decide

/-! ## The suite -/

def specClosure : Spec := Spec.ofList "closure-bridge"
  (fun _ => do
    -- BOTH engines, computed: the fold's stabilized fragment …
    assert (Machines.Testing.reachableStates m3cl inputs3cl 0 5 == some [0, 1, 2])
      "the fold's stabilized fragment wrong"
    -- … and the Datalog closure, pinned equal state by state
    assert (decide (⟨stPred, [Sum.inl (0 : Nat)]⟩ ∈ ev3)) "closure misses 0"
    assert (decide (⟨stPred, [Sum.inl 1]⟩ ∈ ev3)) "closure misses 1"
    assert (decide (⟨stPred, [Sum.inl 2]⟩ ∈ ev3)) "closure misses 2"
    assert (!(decide (⟨stPred, [Sum.inl 5]⟩ ∈ ev3))) "closure invented 5"
    assert (!(decide (⟨stPred, [Sum.inl 7]⟩ ∈ ev3))) "closure invented 7"
    -- the fuel/height relationship, live
    assert (Machines.Testing.reachableStates m3cl inputs3cl 0 2 matches none)
      "under-fueled fold did not report the honest gap"
    assert (Machines.Testing.reachableStates m3cl inputs3cl 0 3 == some [0, 1, 2])
      "3 rounds did not stabilize the 3-state fragment"
    assert (decide (0 < Datalog.height P3 E3))
      "the Datalog side's theoretic fuel is zero")
  [ ("sabotage-closedness-dropped", fun _ =>
      -- the sabotaged agreement: fold finds 2, the truncated closure does not
      assert (decide ((2 : Nat)
          ∈ (Machines.Testing.reachableStates m3cl inputs3cl 0 5).getD [])
        == decide (⟨stPred, [Sum.inl 2]⟩ ∈ Datalog.eval Psab E3))
      "control"),
    ("sabotage-init-fact-dropped", fun _ =>
      assert (decide (⟨stPred, [Sum.inl (0 : Nat)]⟩
        ∈ Datalog.eval P3 EnoInit)) "control"),
    ("sabotage-fold-underfueled", fun _ =>
      assert (Machines.Testing.reachableStates m3cl inputs3cl 0 2
        == some [0, 1, 2]) "control") ]
  1 49

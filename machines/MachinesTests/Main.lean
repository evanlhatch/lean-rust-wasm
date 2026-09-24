/-
# MachinesTests — the verdicts' three faces + the soundness + the controls

Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5). Suites:

1. `verdict-faces` — the worked machine's THREE faces pinned exactly:
   PROVED (the covered reachable fragment), REFUTED (with the tape
   witness), UNKNOWN (budget exhaustion — never laundered into a
   verdict). The negative controls are the sabotages the doctrine
   demands: a refutable invariant claimed PROVED; budget exhaustion
   claimed as a verdict; the witness denied.
2. `ties-and-soundness` — the projections tied to `run` (the record
   projection's value pin, the loop pin: three states, unboundedly many
   executions), check_refuted exercised at runtime (the computed
   verdict's witness RUNS), and the soundness theorems exercised: state
   5 and state 7 are in the type but NOT in the reachable fragment —
   `check_proved` + the coverage premise prove their unreachability.

3. `conformance-battery` — the EventSpec/guard layer (Events.lean) +
   the conformance battery (Testing.lean) over the worked machine
   WITH its invariant slot (`m3i`, tied to `step3` by `m3i_tie`) and
   over the deliberately-broken `mGhost` (a never-enabled `ghost`
   event — dead code the compiler accepts, the battery REFUTES;
   a vacuous `True` invariant — refuted; an unbounded +1 walk — the
   honest `.unknown`). The mandatory negative controls are the
   sabotages: the teeth blunted, the budget gap laundered into a
   verdict, the vacuity passed.
4. `fusion-bridges` — the Stream/Fusion layer: the dI iso's round
   trips (pinned in values + at the Iso-value level), the journal
   bridge on the worked mod-3 machine (its journal differentiates its
   run; its replay integrates the journal — pinned), the observer-
   stream bisimulation pins, and the MANDATORY negative controls:
   the sabotaged zero-initial convention (the first-entry convention
   is load-bearing), and THE TRICHOTOMY TRIPWIRE (03 §7 as tests):
   the net-zero journal ≠ the empty run — the events happened.
5. `machine-entourage` — the machine! layer (Machines.Dsl, 15-patterns
   #9): the `wheel`/`lamp` fixtures' GENERATED table stack pinned in
   values, the tie theorem cited (never re-proved), the generated
   `DecidablePred` exercised, the battery REGISTRATION runtime-pinned
   (lamp all-proved; wheel's vacuous invariant refuted), and the
   curated-failure teeth (#guard_msgs: the unknown clause → the
   legal-clause enumeration + the did-you-mean; the cardinality and
   absence errors). Controls: the drifted table, the vacuity passed.

The fixture: the mod-3 tick cycle (0→1→2→0 — a LOOP, per 01-core §3's
"finite states ≠ finite executions"), reset, and a `bump` that fires
only at state 7 — which the exploration never reaches, so the covered
fragment stays {0,1,2} while the input list is COMPLETE (the coverage
premise of `check_proved` is discharged trivially — all inputs listed —
and the theorem still proves real unreachability).

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the bridge + soundness theorems. Evidence, not architecture — the
five-question block lives in the modules under test.
-/

import Machines
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import MachinesTests.Axioms
import MachinesTests.Coalg
import MachinesTests.Closure
import MachinesTests.Session

open Machines TestingKit

/-! ## The fixture: the worked machine -/

inductive TInput where
  | tick | bump | reset
deriving DecidableEq, Repr, BEq

open TInput

/-- The worked machine: the mod-3 tick cycle + reset + the
    reachable-only-at-7 bump. -/
def step3 : Nat → TInput → Option Nat
  | 7, .bump => some 10
  | _, .bump => none
  | s, .tick => some ((s + 1) % 3)
  | _, .reset => some 0

def m3 : Machine Nat TInput := ⟨step3⟩

/-- The COMPLETE input list — `check_proved`'s coverage premise
    discharges trivially against it, and the theorem still carries
    content (the unreachability pins below). -/
def inputs3 : List TInput := [tick, bump, reset]

/-! ## The EventSpec family: the worked machine gains its invariant slot -/

open Machines.Testing (deadlockFree guardCoverage guardCoverage_refuted invariantNonVacuous)

/- HAND-BUILT WITH A REASON (12 §5's discipline — a hand-built machine
carries a written one): `m3i` does NOT migrate onto `machine!`. Its
state space is `Nat`, deliberately carrying the out-of-fragment states
(5, 7, 10) that the soundness teeth (`unreachable_5`/`unreachable_7`),
the `step3` tie, and the Int fusion section require; `machine!`'s
`states:` clause generates the CLOSED finite enum, which cannot carry
them. The `machine!` fixtures below (`wheel`, `lamp`) are the
entourage's authored surface. -/

/-- tick: always enabled, cycles the mod-3 wheel; the safety PO is
    discharged HERE (an event that could break the invariant is
    unconstructible — the UPDATE…WHERE discipline). -/
def evTick : EventSpec Nat (fun n => n < 3) where
  guard := fun _ => true
  action := fun s _ => (s + 1) % 3
  safety := by intro s _ hs; omega

/-- bump: enabled only at state 7 — never on the reachable fragment
    (the teeth below). Its safety PO is vacuous (7 ≮ 3) and the
    constructor still demands it. -/
def evBump : EventSpec Nat (fun n => n < 3) where
  guard := fun s => decide (s = 7)
  action := fun _ _ => 10
  safety := by
    intro s h hs
    have h7 : s = 7 := decide_eq_true_eq.mp h
    omega

/-- reset: always enabled, lands on 0. -/
def evReset : EventSpec Nat (fun n => n < 3) where
  guard := fun _ => true
  action := fun _ _ => 0
  safety := by intro s _ hs; omega

/-- The worked machine WITH its invariant slot — the SAME transition
    table as `step3` (the tie is `m3i_tie`). -/
def m3i : MachineWithInv Nat TInput where
  inv := fun n => n < 3
  event := fun
    | .tick => evTick
    | .bump => evBump
    | .reset => evReset

instance : DecidablePred m3i.inv := fun n => Nat.decLt n 3

/-- THE TIE: the EventSpec-derived `step?` IS the landed `step3` —
    the invariant slot rides the same authoritative transition table,
    never a parallel encoding. -/
theorem m3i_tie (s : Nat) (i : TInput) : m3i.toMachine.step? s i = step3 s i := by
  cases i with
  | tick =>
      simp [MachineWithInv.step?, MachineWithInv.toMachine, m3i, evTick, step3]
  | reset =>
      simp [MachineWithInv.step?, MachineWithInv.toMachine, m3i, evReset, step3]
  | bump =>
      simp only [MachineWithInv.step?, MachineWithInv.toMachine, m3i, evBump]
      split
      · rename_i h
        have h7 : s = 7 := decide_eq_true_eq.mp h
        subst h7
        simp [step3]
      · rename_i h
        have hd : decide (s = 7) = false := by
          cases hb : decide (s = 7) with
          | false => rfl
          | true => rw [hb] at h; simp at h
        have h7 : ¬(s = 7) := decide_eq_false_iff_not.mp hd
        exact (step3.eq_2 s h7).symm

/-! ## The ghost machine (the battery's teeth) -/

inductive GInput where
  | tick | ghost
deriving DecidableEq, Repr, BEq

/-- The TEETH machine: `ghost` is NEVER enabled — dead code the
    compiler accepts; the battery refutes it with the dead label.
    The invariant is `True` — vacuous by construction — so the
    non-vacuity check refutes too. tick is an unbounded +1 walk, so
    the reachable fragment never stabilizes: the deadlock sweep
    answers the honest `.unknown`. -/
def mGhost : MachineWithInv Nat GInput where
  inv := fun _ => True
  event := fun
    | .tick => ⟨fun _ => true, fun s _ => s + 1, fun _ _ _ => trivial⟩
    | .ghost => ⟨fun _ => false, fun s _ => s, fun _ _ _ => trivial⟩

instance : DecidablePred mGhost.inv := fun _ => isTrue trivial

def ghostInputs : List GInput := [.tick, .ghost]
def ghostStates : List Nat := [0, 1]

theorem ghostInputs_complete : ∀ i, i ∈ ghostInputs := by
  intro i; cases i <;> simp [ghostInputs]

/-! ## The machine! entourage (Machines.Dsl, 15-patterns #9) -/

/- The mod-3 wheel, AUTHORED with `machine!`: the state enum, the
    event family, the table stack, the tie theorem, the decidable
    predicate, and the battery registration — all generated from the
    clauses. The invariant is `True` — the generated battery REFUTES
    its non-vacuity (the control below); that is the honest answer.
    (Block comment, not a docstring: a docstring does not attach to a
    syntax-declared command — the parse error is the audit's
    keyword-pollution trap in its docstring form.) -/
machine! wheel where
  states: [s0, s1, s2]
  Inv: fun _ => True
  event: tick guard: (fun _ => true) action: (fun s _ => match s with | .s0 => .s1 | .s1 => .s2 | .s2 => .s0)
  event: reset guard: (fun _ => true) action: (fun _ _ => .s0)

/- The non-vacuous fixture: `broke` is IN the enumeration but
    unreachable (the guards keep it out), so the invariant `≠ broke`
    excludes an enumerated state — all three battery checks PROVE. -/
machine! lamp where
  states: [off, on, broke]
  Inv: fun s => s ≠ .broke
  event: switchOn guard: (fun s => s = .off) action: (fun _ _ => .on)
  event: switchOff guard: (fun s => s ≠ .off) action: (fun _ _ => .off)

/-- THE GENERATED TABLE, pinned in values: tick cycles (label-major,
    states in enumeration order), reset lands. -/
theorem wheelTrans_pin :
    wheelTrans
      = [(wheel.Label.tick, wheel.State.s0, wheel.State.s1),
         (wheel.Label.tick, wheel.State.s1, wheel.State.s2),
         (wheel.Label.tick, wheel.State.s2, wheel.State.s0),
         (wheel.Label.reset, wheel.State.s0, wheel.State.s0),
         (wheel.Label.reset, wheel.State.s1, wheel.State.s0),
         (wheel.Label.reset, wheel.State.s2, wheel.State.s0)] := by rfl

/-- THE GENERATED TIE, exercised as a cited fact (never re-proved):
    the generated lookup IS the generated machine's `step?`, for every
    event and every state (the state type IS the enumeration). -/
theorem wheelTie (e : wheel.Label) (s : wheel.State) :
    wheelTableStep? e s = Machines.MachineWithInv.step? wheel s e :=
  wheelTableStep?_eq_step? e s

/-- The lookup, pinned: tick from s1 lands s2; reset from anywhere
    lands s0. -/
theorem wheelLookup_pin : wheelTableStep? .tick .s1 = some .s2
    ∧ wheelTableStep? .reset .s2 = some .s0 := ⟨rfl, rfl⟩

/-- The generated `DecidablePred` instance, exercised. -/
theorem lampInv_decides :
    decide (lamp.inv .off) = true ∧ decide (lamp.inv .broke) = false :=
  ⟨by decide, by decide⟩

/-- THE BATTERY REGISTRATION, pinned exactly: over `lamp` — the
    enumeration includes `broke`, the invariant excludes it — all
    three generated checks PROVE. -/
theorem lampBattery_proved :
    lamp.battery .off 4
      = [("deadlock-freedom", .proved),
         ("guard-coverage", .proved),
         ("invariant-non-vacuity", .proved)] := by rfl

/-- THE NEGATIVE CONTROL (15-patterns #5): the vacuous `True`
    invariant is REFUTED by the generated battery — the author who
    wrote `Inv: fun _ => True` does not get a silent pass. -/
theorem wheelBattery_vacuous_control :
    wheel.battery .s0 4
      = [("deadlock-freedom", .proved),
         ("guard-coverage", .proved),
         ("invariant-non-vacuity", .refuted .vacuous)] := by rfl

/- THE GENERATED TIE IS AXIOM-FREE: the `cases <;> rfl` proof carries
    the core triple at most — pinned (a generated proof that grew a
    `sorry` or an axiom fails HERE). -/
/-- info: 'wheelTableStep?_eq_step?' does not depend on any axioms -/
#guard_msgs in
#print axioms wheelTableStep?_eq_step?

/-! ## The curated-failure teeth (the clause surface's closed world) -/

/- THE UNKNOWN-CLAUSE TOOTH: a typo'd clause reaches the ELABORATOR
    (the low-priority catch-all) and is rejected with the legal-clause
    enumeration + the ONE did-you-mean engine (`TextKit.suggestSuffix`). -/
/-- error: machine!: unknown clause `evnt:` — legal clauses: `states:`, `Inv:`, `event:` — did you mean: event, Inv? -/
#guard_msgs in
machine! oops where
  evnt: nothing

/- The duplicate tooth: cardinality is enforced by the elaborator. -/
/-- error: machine!: duplicate `states:` clause — at most one -/
#guard_msgs in
machine! dup where
  states: [a]
  states: [b]
  event: t guard: (fun _ => true) action: (fun s _ => s)

/- The absence teeth: each mandatory clause names itself when missing. -/
/-- error: machine!: missing `Inv:` clause — the machine's invariant -/
#guard_msgs in
machine! noInv where
  states: [a]
  event: t guard: (fun _ => true) action: (fun s _ => s)

/-- error: machine!: missing `states:` clause — the state enumeration, a non-empty `[ident, …]` list -/
#guard_msgs in
machine! noStates where
  Inv: fun _ => True
  event: t guard: (fun _ => true) action: (fun s _ => s)

/-- error: machine!: missing `event:` clause — at least one event is required -/
#guard_msgs in
machine! noEvents where
  states: [a]
  Inv: fun _ => True

/-! ## The battery's verdict faces (rung-3 pins) -/

def statesFull : List Nat := [0, 1, 2, 7]
def statesReachable : List Nat := [0, 1, 2]

theorem inputsFull_complete : ∀ i, i ∈ inputs3 := by
  intro i; cases i <;> simp [inputs3]

/-- THE PROVED FACE (deadlock): the sweep stabilizes over the
    reachable fragment {0,1,2} — every legal state has an enabled
    event. -/
theorem battery3i_deadlock :
    deadlockFree m3i inputs3 0 5 inputsFull_complete = .proved := by rfl

/-- Guard coverage over the FULL enumeration: bump fires at 7 —
    proved. -/
theorem battery3i_coverage :
    guardCoverage m3i inputs3 statesFull inputsFull_complete = .proved := by rfl

/-- THE TEETH (worked machine): over the REACHABLE fragment {0,1,2},
    bump is never enabled — the battery REFUTES it, with the dead
    label as witness. The compiler accepted this machine; the battery
    did not. -/
theorem battery3i_teeth :
    guardCoverage m3i inputs3 statesReachable inputsFull_complete
      = .refuted (.dead .bump) := by rfl

/-- Non-vacuity: `n < 3` excludes 7 — the battery's signal is live. -/
theorem battery3i_nonvacuous :
    invariantNonVacuous m3i statesFull = .proved := by rfl

/-- THE TEETH (ghost machine): the never-enabled ghost event,
    refuted. -/
theorem ghost_teeth :
    guardCoverage mGhost ghostInputs ghostStates ghostInputs_complete
      = .refuted (.dead .ghost) := by rfl

/-- The ghost's vacuous invariant — refuted. -/
theorem ghost_vacuous :
    invariantNonVacuous mGhost ghostStates = .refuted .vacuous := by rfl

/-- The ghost's deadlock sweep: the +1 walk never stabilizes within
    any budget — the honest `.unknown` (budget exhaustion is never a
    verdict; 01-core §3). -/
theorem ghost_unknown :
    deadlockFree mGhost ghostInputs 0 8 ghostInputs_complete
      = .unknown .budgetExhausted := by rfl

/-! ## The bridges, exercised -/

/-- THE TEETH'S PROOF CONTENT: via `guardCoverage_refuted`, the
    refuted verdict PROVES the ghost is never enabled — the witness
    is not a string, it is a theorem. -/
theorem ghost_teeth_real :
    ∀ s ∈ ghostStates, mGhost.enabled s .ghost = false :=
  (guardCoverage_refuted mGhost ghostInputs ghostStates ghostInputs_complete .ghost
    ghost_teeth).2

/-- `run_preserves` exercised: the 8-tick loop run ends in state 2,
    and the invariant survives the whole fold. -/
theorem run3i_preserves : m3i.inv 2 := by
  have h : m3i.toMachine.run 0 (List.replicate 8 tick) = some 2 := by rfl
  exact MachineWithInv.run_preserves m3i 0 (by decide) h

/-! ## The three faces -/

/-- THE PROVED FACE: the exploration stabilized over the reachable
    fragment {0,1,2}; the invariant `n < 3` is PROVED on it. -/
theorem provedFace :
    check m3 (fun n => n < 3) inputs3 0 5 = .proved := by rfl

/-- THE REFUTED FACE: the violable invariant `n ≠ 2` — the check
    returns the tape `[tick, tick]` to state 2 as the WITNESS. -/
theorem refutedFace :
    check m3 (fun n => n ≠ 2) inputs3 0 5 = .refuted [tick, tick] 2 := by rfl

/-- THE UNKNOWN FACE: under-fueled (budget 1) — no violation seen, the
    frontier did not stabilize: the honest gap, with its named cause. -/
theorem unknownFace :
    check m3 (fun n => n < 3) inputs3 0 1 = .unknown .budgetExhausted := by rfl

/-! ## The soundness theorems, exercised -/

/-- THE COVERAGE PREMISE, discharged: every step out of a reachable
    state uses a listed input — trivial here (ALL inputs are listed),
    but it is a THEOREM the soundness consumes, not a convention. -/
theorem inputs3_cover : ∀ s i s', m3.Reachable 0 s → m3.step s i s' → i ∈ inputs3 := by
  intro s i s' _ _
  cases i <;> simp [inputs3]

/-- SOUNDNESS EXERCISED: state 5 is in the TYPE but not in the
    reachable fragment — `check_proved` + the coverage premise prove
    its unreachability. Not an enumeration: the theorem does the work. -/
theorem unreachable_5 : ¬ m3.Reachable 0 5 := by
  intro h
  have h5 := check_proved m3 (fun n => n < 3) inputs3 0 5 provedFace inputs3_cover 5 h
  simp at h5

/-- Same for state 7 — the bump's home state, never reachable. -/
theorem unreachable_7 : ¬ m3.Reachable 0 7 := by
  intro h
  have h7 := check_proved m3 (fun n => n < 3) inputs3 0 5 provedFace inputs3_cover 7 h
  simp at h7

/-- REFUTED WITNESS EXERCISED: the refuted verdict's tape RUNS to the
    bad state — via `check_refuted`, not by re-computing. -/
theorem witness_runs : m3.run 0 [tick, tick] = some 2 :=
  (check_refuted m3 (fun n => n ≠ 2) inputs3 0 5 refutedFace).1

/-! ## The execution + observer pins -/

/-- The execution witness for the two-tick run (built by `run_exec` —
    the run tie, as data). -/
def exec2 : Exec m3 0 2 :=
  .step (i := tick) (s := 0) (s' := 1) (by rfl)
    (.step (i := tick) (s := 1) (s' := 2) (by rfl) .here)

/-- The record projection, pinned: the audit trail of the run. -/
theorem exec2_record : exec2.record = [(tick, 1), (tick, 2)] := by rfl

/-- THE RUN TIE, pinned: the successful run's witnessing execution
    (built by `run_exec` from the run proof) satisfies the tape tie. -/

def runExe : Exec m3 0 2 :=
  Exec.run_exec m3 0 (t := [tick, tick]) (by rfl)

theorem run_tie_run : m3.run 0 runExe.tape = some 2 := runExe.exec_run

/-- The tape tie, pinned via the projection law. -/
theorem exec2_run : m3.run 0 exec2.tape = some 2 := exec2.exec_run

/-- An observer over step records: the post-states only. -/
def stateOnly : Kit.Observer (TInput × Nat) Nat := ⟨fun p => p.2⟩

/-- The cited law, exercised: equivalence under an observer is
    REFLEXIVE (Kit.Observer.equiv_refl, cited — never re-proved). -/
theorem exec2_equiv_refl : exec2.equivUnder stateOnly exec2 :=
  Exec.equivUnder_refl stateOnly exec2

/-- FINITE STATES ≠ FINITE EXECUTIONS: eight ticks run fine — the
    mod-3 cycle loops forever. -/
theorem loop_runs : m3.run 0 (List.replicate 8 tick) = some 2 := by rfl

/-! ## The fusion bridges (Machines.Stream + Machines.Fusion) -/

/-- The additive structure for the Int machines: `Kit.intAdd` — the
    full-ladder instance (Kit.Change), consumed explicitly. -/
def gInt : Kit.Additive Int Int := Kit.intAdd

/-- A concrete Int stream: the squares. -/
def sq : Machines.Stream Int := fun t => (t : Int) * (t : Int)

/-- The SABOTAGED convention: `Dbad` zeroes the first entry instead of
    carrying the initial value — the iso breaks (the negative
    control's instrument). -/
def Dbad : Machines.Stream Int → Machines.Stream Int :=
  fun s t => match t with
    | 0 => 0
    | t + 1 => s (t + 1) - s t

/-- The init-carrying stream the sabotage needs (first entry ≠ 0). -/
def sq5 : Machines.Stream Int := fun t => 5 + (t : Int) * (t : Int)

/-- The worked machine over Int states — the SAME transition table as
    `step3` (the mod-3 wheel, the 7-bump, the reset; mod-3 arithmetic
    on Int). -/
def step3i : Int → TInput → Option Int
  | 7, .bump => some 10
  | _, .bump => none
  | s, .tick => some ((s + 1) % 3)
  | _, .reset => some 0

def m3z : Machine Int TInput := ⟨step3i⟩

def insTickI : Machines.Stream TInput := fun _ => tick

/-- The inc/dec walk machine: the net-zero control's fixture. -/
inductive ZInput where
  | inc | dec
deriving DecidableEq, Repr, BEq

def stepZ : Int → ZInput → Option Int
  | s, .inc => some (s + 1)
  | s, .dec => some (s - 1)

def mZ : Machine Int ZInput := ⟨stepZ⟩

/-- Alternating inc/dec input stream: every two ticks the NET change
    is zero — but the run VISITS state 1 (03 §7: net-zero ≠ nothing
    happened). -/
def insZ : Machines.Stream ZInput :=
  fun t => if t % 2 = 0 then .inc else .dec

/-- The mod-3 observer: sees only `n % 3` — states 0 and 3 are
    indistinguishable through it. -/
def mod3obs : Kit.Observer Int Int := ⟨fun n => n % 3⟩

/-- The tick/reset-only machine: states 0 and 3 are EXACTLY
    tick-agreeing (the deterministic-bisim fixture — bump would
    separate them, so it is not in this label set). -/
inductive RInput where
  | tick | reset
deriving DecidableEq, Repr, BEq

def step3r : Int → RInput → Option Int
  | s, .tick => some ((s + 1) % 3)
  | _, .reset => some 0

def m3r : Machine Int RInput := ⟨step3r⟩

def insTickR : Machines.Stream RInput := fun _ => .tick

/-! ### The dI iso, exercised -/

/-- THE ISO VALUE'S both round trips (Kit.Correspondence.Iso, consumed
    as a value — the carrier discipline). -/
theorem dI_round_trips :
    (Machines.dI gInt).to ((Machines.dI gInt).inv sq) = sq
    ∧ (Machines.dI gInt).inv ((Machines.dI gInt).to sq) = sq :=
  ⟨(Machines.dI gInt).to_inv sq, (Machines.dI gInt).inv_to sq⟩

/-- Differentiation of the squares, pinned: the journal [0,1,3,5,7]. -/
theorem d_sq : List.map (Machines.D gInt sq) [0, 1, 2, 3, 4] = [0, 1, 3, 5, 7] := by
  decide

/-- Both composites reconstruct the squares, pinned (the theorems are
    `Machines.I_D`/`Machines.D_I`; the pin is the VALUES). -/
theorem roundTrip_sq :
    List.map (Machines.I gInt (Machines.D gInt sq)) [0, 1, 2, 3, 4] = [0, 1, 4, 9, 16]
    ∧ List.map (Machines.D gInt (Machines.I gInt sq)) [0, 1, 2, 3, 4]
        = [0, 1, 4, 9, 16] := by
  decide

/-- THE SABOTAGE (the convention is load-bearing): with the
    zero-initial `D'`, integration does NOT reconstruct —
    `I (Dbad sq5) 0 = 0 ≠ 5 = sq5 0`. -/
theorem dbad_breaks_iso : Machines.I gInt (Dbad sq5) 0 ≠ sq5 0 := by decide

/-! ### The journal / replay bridges on the worked machine -/

/-- The worked machine's journal under constant ticks: the init
    snapshot 0, then the net changes 1, 1, −2 cycling — pinned. Its
    journal differentiates its run (`journal_eq_D_run`). -/
theorem journal3 : List.map (Fusion.journal gInt m3z insTickI 0) [0, 1, 2, 3, 4, 5, 6]
    = [0, 1, 1, -2, 1, 1, -2] := by decide

/-- Its replay integrates back to the state stream 0,1,2,0,… —
    pinned (the theorem is `Fusion.replay_eq_run`; the pin is the
    VALUES). -/
theorem replay3 : List.map (Fusion.replay gInt m3z insTickI 0) [0, 1, 2, 3, 4, 5, 6]
    = [0, 1, 2, 0, 1, 2, 0] := by decide

/-- The bridge theorem itself, at the value level. -/
theorem replay3_eq_run : Fusion.replay gInt m3z insTickI 0
    = Fusion.stateStream m3z insTickI 0 := Fusion.replay_eq_run gInt m3z insTickI 0

/-! ### THE TRICHOTOMY TRIPWIRE (03 §7 as tests): net-zero ≠ nothing happened -/

/-- The alternating inc/dec run's journal: the net change is ZERO
    after every two ticks — pinned. -/
theorem netZero_journal : List.map (Fusion.journal gInt mZ insZ 0) [0, 1, 2, 3, 4]
    = [0, 1, -1, 1, -1] := by decide

/-- THE TRIPWIRE: that journal is NOT the empty run's journal — the
    events happened. -/
theorem netZero_journal_notTrivial :
    List.map (Fusion.journal gInt mZ insZ 0) [0, 1, 2, 3, 4] ≠ [0, 0, 0, 0, 0] := by
  decide

/-- ... and the replay is NOT the empty run's replay: state 1 was
    visited. The journal is EVENTS, the net is the DELTA — never
    collapsed (signed addition commutes but is not idempotent). -/
theorem netZero_replay_visited :
    List.map (Fusion.replay gInt mZ insZ 0) [0, 1, 2, 3, 4] = [0, 1, 0, 1, 0]
    ∧ List.map (Fusion.replay gInt mZ insZ 0) [0, 1, 2, 3, 4] ≠ [0, 0, 0, 0, 0] := by
  decide

/-! ### Bisimulation as stream equality (observer-parameterized) -/

/-- The observer premise holds for states 0 and 3 under `mod3obs`:
    tick sees 1 = 1; reset sees 0 = 0; bump: both hold, both ≡ 0. -/
theorem bisim03_mod3 : ∀ l : TInput,
    mod3obs.see (m3z.tick l 0) = mod3obs.see (m3z.tick l 3) := by
  intro l; cases l <;> decide

/-- THE NEGATIVE CONTROL: under the IDENTITY observation the premise
    FAILS — bump separates 0 from 3 (the coarseness is real). -/
theorem bisim03_id_fails : ¬ ∀ l : TInput, m3z.tick l 0 = m3z.tick l 3 := by
  intro h
  have hb := h bump
  have h0 : m3z.tick bump 0 = 0 := by decide
  have h3 : m3z.tick bump 3 = 3 := by decide
  rw [h0, h3] at hb
  omega

/-- The response streams coincide, pinned in values: from 0 and from
    3, the observed post-tick states are 1,2,0,1 on the same input
    stream (`respStream_equiv`'s content, at the value level). -/
theorem respStream03 :
    List.map (Fusion.respStream mod3obs m3z insTickI 0) [0, 1, 2, 3]
      = List.map (Fusion.respStream mod3obs m3z insTickI 3) [0, 1, 2, 3]
    ∧ List.map (Fusion.respStream mod3obs m3z insTickI 0) [0, 1, 2, 3] = [1, 2, 0, 1] := by
  decide

/-- The exact-agreement fixture: 0 ~ 3 exactly for the tick/reset
    machine (one-step tick-agreement — the deterministic bisimulation). -/
theorem bisim03r : ∀ l : RInput, m3r.tick l 0 = m3r.tick l 3 := by
  intro l; cases l <;> decide

/-- The stream-level bisimulation theorem, exercised:
    `bisim_iff_respStreams`'s forward direction. -/
theorem respStreams03r :
    Fusion.respStateStream m3r insTickR 0 = Fusion.respStateStream m3r insTickR 3 :=
  (Fusion.bisim_iff_respStreams m3r 0 3).mp bisim03r insTickR

/-- THE TRACE BISIMULATION, exercised: identical observed response
    traces on the same tape (`respTrace_tick_agree`). -/
theorem respTrace03r :
    Fusion.respTrace mod3obs m3r 0 [.tick, .tick]
      = Fusion.respTrace mod3obs m3r 3 [.tick, .tick] :=
  Fusion.respTrace_tick_agree mod3obs m3r 0 3 bisim03r [.tick, .tick]

/-! ### The Exec tie -/

/-- The two-tick execution over the Int machine (witness-carrying). -/
def exec2z : Exec m3z 0 2 :=
  .step (i := tick) (s := 0) (s' := 1) (by rfl)
    (.step (i := tick) (s := 1) (s' := 2) (by rfl) .here)

/-- THE TRACE TIE, pinned: the trace of the execution's tape is the
    initial state followed by the record's post-states
    (`traceStates_exec`'s content, at the value level). -/
theorem exec2z_trace : Fusion.traceStates m3z 0 exec2z.tape = [0, 1, 2] := by decide

/-- The observed response trace IS the record's observed image
    (`respTrace_exec`, exercised as data). -/
theorem exec2z_respTrace :
    Fusion.respTrace mod3obs m3z 0 exec2z.tape
      = exec2z.record.map (fun p : TInput × Int => mod3obs.see p.2) :=
  Fusion.respTrace_exec mod3obs m3z 0 2 exec2z

/-! ## THE GRADUATION (16-surface §5.1): Exec ≅ the runnable tapes -/

/-- The runnable tape for the two-tick run (the subtype's run equation
    discharged by the run's own value). -/
def rt2 : Exec.RunnableTapes m3 0 := ⟨⟨2, [tick, tick]⟩, by rfl⟩

/-- THE ISO'S RECONSTRUCTION, pinned in values: the two-tick tape
    reconstructs THE two-tick execution (the run tie, as data — the
    witnesses are `rfl`, the lookups determined by `step?`). -/
theorem Exec.execIso_to_rt2 : (Exec.execIso m3 0).to rt2 = ⟨2, exec2⟩ := by rfl

/-- THE ISO'S round trips (Kit.Correspondence's carrier discipline —
    the laws are the ISO's FIELDS, cited, never re-proved). -/
theorem Exec.execIso_round_trips :
    (Exec.execIso m3 0).to ((Exec.execIso m3 0).inv ⟨2, exec2⟩) = ⟨2, exec2⟩
      ∧ (Exec.execIso m3 0).inv ((Exec.execIso m3 0).to rt2) = rt2 :=
  ⟨(Exec.execIso m3 0).to_inv _, (Exec.execIso m3 0).inv_to _⟩

/-- THE TEETH (the unrepresentability): the refused tape's run is
    `none` — the refusal is data, and a tape outside the runnable
    subtype's image has NO element to name. -/
theorem Exec.bumpRefused : ¬ ∃ fin, m3.run 0 [bump] = some fin := by
  rintro ⟨fin, hf⟩
  rw [show m3.run 0 [bump] = none from rfl] at hf
  simp at hf

/-! ## The suites -/

def specFaces : Spec := Spec.ofList "verdict-faces"
  (fun _ => do
    let v1 := check m3 (fun n => n < 3) inputs3 0 5
    assert (match v1 with | .proved => true | _ => false) "PROVED face wrong"
    let v2 := check m3 (fun n => n ≠ 2) inputs3 0 5
    assert (match v2 with
            | .refuted t b => t == [tick, tick] && b == 2
            | _ => false) "REFUTED face wrong (tape or bad state)"
    let v3 := check m3 (fun n => n < 3) inputs3 0 1
    assert (match v3 with
            | .unknown r => r == ExploreReason.budgetExhausted
            | _ => false) "UNKNOWN face wrong (cause or verdict)")
  [ ("sabotage-proved-hides-refutation", fun _ =>
      assert (match check m3 (fun n => n ≠ 2) inputs3 0 5 with
              | .proved => true | _ => false) "control"),
    ("sabotage-budget-laundered-as-verdict", fun _ =>
      assert (match check m3 (fun n => n < 3) inputs3 0 1 with
              | .proved => true | _ => false) "control"),
    ("sabotage-witness-denied", fun _ =>
      assert (m3.run 0 [tick, tick] = none) "control") ]
  1 42

def specTies : Spec := Spec.ofList "ties-and-soundness"
  (fun _ => do
    assert (exec2.record == [(tick, 1), (tick, 2)]) "record projection wrong"
    assert (m3.run 0 exec2.tape == some 2) "tape tie wrong"
    assert (m3.run 0 (List.replicate 8 tick) == some 2) "loop pin wrong"
    assert ((Exec.execObs stateOnly).see exec2
        == (Exec.execObs stateOnly).see exec2) "observer sees wrong"
    -- runtime exercise of check_refuted: the COMPUTED verdict's witness runs
    match check m3 (fun n => n ≠ 2) inputs3 0 5 with
    | .refuted t b =>
        assert (m3.run 0 t == some b) "witness does not run"
        assert (b == 2) "wrong bad state"
    | _ => .error "expected refuted")
  [ ("sabotage-record", fun _ =>
      assert (exec2.record == ([] : List (TInput × Nat))) "control"),
    ("sabotage-loop", fun _ =>
      assert (m3.run 0 (List.replicate 8 tick) == none) "control") ]
  1 43

def specBattery : Spec := Spec.ofList "conformance-battery"
  (fun _ => do
    assert (deadlockFree m3i inputs3 0 5 inputsFull_complete matches .proved)
      "deadlock-freedom verdict wrong"
    assert (guardCoverage m3i inputs3 statesFull inputsFull_complete matches .proved)
      "guard-coverage verdict wrong (full enumeration)"
    assert (guardCoverage m3i inputs3 statesReachable inputsFull_complete
        matches .refuted (.dead .bump))
      "TEETH BLUNTED: dead bump not refuted"
    assert (invariantNonVacuous m3i statesFull matches .proved)
      "non-vacuity verdict wrong"
    assert (guardCoverage mGhost ghostInputs ghostStates ghostInputs_complete
        matches .refuted (.dead .ghost))
      "TEETH BLUNTED: ghost not refuted"
    assert (invariantNonVacuous mGhost ghostStates matches .refuted .vacuous)
      "vacuous invariant not refuted"
    assert (deadlockFree mGhost ghostInputs 0 8 ghostInputs_complete
        matches .unknown .budgetExhausted)
      "budget gap not honest unknown")
  [ ("sabotage-teeth-blunted", fun _ =>
      assert (guardCoverage mGhost ghostInputs ghostStates ghostInputs_complete
        matches .proved) "control"),
    ("sabotage-deadlock-gap-laundered", fun _ =>
      assert (deadlockFree mGhost ghostInputs 0 8 ghostInputs_complete
        matches .proved) "control"),
    ("sabotage-vacuity-passed", fun _ =>
      assert (invariantNonVacuous mGhost ghostStates matches .proved) "control") ]
  1 44

def specFusion : Spec := Spec.ofList "fusion-bridges"
  (fun _ => do
    assert (List.map (Machines.D gInt sq) [0, 1, 2, 3, 4] == [0, 1, 3, 5, 7])
      "D wrong"
    assert (List.map (Machines.I gInt (Machines.D gInt sq)) [0, 1, 2, 3, 4]
        == [0, 1, 4, 9, 16]) "I ∘ D wrong"
    assert (List.map (Machines.D gInt (Machines.I gInt sq)) [0, 1, 2, 3, 4]
        == [0, 1, 4, 9, 16]) "D ∘ I wrong"
    assert (List.map (Fusion.journal gInt m3z insTickI 0) [0, 1, 2, 3, 4, 5, 6]
        == [0, 1, 1, -2, 1, 1, -2]) "journal wrong"
    assert (List.map (Fusion.replay gInt m3z insTickI 0) [0, 1, 2, 3, 4, 5, 6]
        == [0, 1, 2, 0, 1, 2, 0]) "replay wrong"
    assert (List.map (Fusion.journal gInt mZ insZ 0) [0, 1, 2, 3, 4]
        == [0, 1, -1, 1, -1]) "net-zero journal wrong"
    assert (!(List.map (Fusion.journal gInt mZ insZ 0) [0, 1, 2, 3, 4]
        == [0, 0, 0, 0, 0])) "NET-ZERO LAUNDERED: journal ≠ the empty run's"
    assert (List.map (Fusion.replay gInt mZ insZ 0) [0, 1, 2, 3, 4] == [0, 1, 0, 1, 0])
      "net-zero replay erased the run"
    assert (List.map (Fusion.respStream mod3obs m3z insTickI 0) [0, 1, 2, 3] == [1, 2, 0, 1])
      "respStream wrong"
    assert (List.map (Fusion.respStream mod3obs m3z insTickI 3) [0, 1, 2, 3] == [1, 2, 0, 1])
      "bisimilar response wrong")
  [ ("sabotage-zero-init-convention", fun _ =>
      -- the zero-initial D' breaks the iso: I (Dbad sq5) 0 = 0 ≠ 5
      assert (Machines.I gInt (Dbad sq5) 0 == sq5 0) "control"),
    ("sabotage-net-zero-erases-history", fun _ =>
      assert (List.map (Fusion.replay gInt mZ insZ 0) [0, 1, 2, 3, 4]
        == [0, 0, 0, 0, 0]) "control"),
    ("sabotage-bisim-coarsened", fun _ =>
      assert (m3z.tick bump 0 == m3z.tick bump 3) "control") ]
  1 45

def specMachine : Spec := Spec.ofList "machine-entourage"
  (fun _ => do
    -- the generated table stack, runtime-pinned
    assert (wheelTrans == [(wheel.Label.tick, wheel.State.s0, wheel.State.s1),
        (wheel.Label.tick, wheel.State.s1, wheel.State.s2),
        (wheel.Label.tick, wheel.State.s2, wheel.State.s0),
        (wheel.Label.reset, wheel.State.s0, wheel.State.s0),
        (wheel.Label.reset, wheel.State.s1, wheel.State.s0),
        (wheel.Label.reset, wheel.State.s2, wheel.State.s0)]) "generated table wrong"
    assert (wheelTableStep? .tick .s1 == some .s2) "generated lookup wrong (tick)"
    assert (wheelTableStep? .reset .s2 == some .s0) "generated lookup wrong (reset)"
    -- the battery registration, runtime-pinned: over lamp all three
    -- checks PROVE; over wheel the vacuous `True` invariant is REFUTED
    assert (lamp.battery lamp.State.off 4 == [("deadlock-freedom",
        Testing.BatteryVerdict.proved), ("guard-coverage", Testing.BatteryVerdict.proved),
        ("invariant-non-vacuity", Testing.BatteryVerdict.proved)])
      "generated battery wrong (lamp)"
    assert (wheel.battery wheel.State.s0 4 == [("deadlock-freedom",
        Testing.BatteryVerdict.proved), ("guard-coverage", Testing.BatteryVerdict.proved),
        ("invariant-non-vacuity", Testing.BatteryVerdict.refuted Testing.BatteryReason.vacuous)])
      "generated battery wrong (wheel: vacuity not refuted)")
  [ ("sabotage-table-drift", fun _ =>
      assert (wheelTableStep? wheel.Label.tick wheel.State.s1
        == some wheel.State.s0) "control"),
    ("sabotage-vacuity-passed", fun _ =>
      assert (match (wheel.battery wheel.State.s0 4).getLast? with
        | some (_, .proved) => true | _ => false) "control") ]
  1 46

def specGraduation : Spec := Spec.ofList "exec-graduation"
  (fun _ => do
    -- the reconstruction's AUDIT trail: the reconstructed execution IS exec2's
    assert (((Exec.execIso m3 0).to rt2).2.record == [(tick, 1), (tick, 2)])
      "reconstruction wrong (record drifted)"
    -- the projection's round trip: the tape survives both legs
    assert (((Exec.execIso m3 0).inv ((Exec.execIso m3 0).to rt2)).1.2 == [tick, tick])
      "tape projection wrong"
    assert (m3.run 0 ((Exec.execIso m3 0).inv ((Exec.execIso m3 0).to rt2)).1.2 == some 2)
      "reconstructed tape does not run")
  [ ("sabotage-reconstruction-erases-steps", fun _ =>
      assert (((Exec.execIso m3 0).to rt2).2.record == ([] : List (TInput × Nat))) "control"),
    ("sabotage-refusal-laundered", fun _ =>
      assert (m3.run 0 [bump] == some 2) "control"),
    ("sabotage-tape-drift", fun _ =>
      assert (((Exec.execIso m3 0).inv ((Exec.execIso m3 0).to rt2)).1.2 == [tick, tick, tick])
        "control") ]
  1 48

def main : IO UInt32 :=
  mainOfSuites [("Machines", [specFaces, specTies, specBattery, specFusion, specMachine, specCoalg, specGraduation, specClosure, specSession])]

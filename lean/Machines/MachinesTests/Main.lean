/-
# Machines Tests — executable checks

The package rule (from Flatland): what is not yet proved gets an executable
check. Here:

1. **Machine.run**: a counter machine — the invariant survives a trace;
   a disabled event rejects the run.

Run: `lake build MachinesTests && .lake/build/bin/MachinesTests`
-/
import Machines
import TestKit

open Machines
open TestKit

-- ── 1. The counter machine ──────────────────────────────────────────────

-- count up to `max`; the invariant is `s ≤ max` — the parameterized
-- machine! form (the DSL covers this case; safety auto-discharges via
-- machine_safety). @[reducible] on the generated def, so
-- `(counterMachine 2).State` unfolds during elaboration.
machine! counterMachine (max : Nat) where
  State: Nat
  Inv: fun s => s ≤ max
  event: increment guard: (fun s => decide (s < max)) action: (fun s _ => s + 1)

def machineTrace : CheckResult := Id.run do
  let m := counterMachine 2
  -- two increments succeed and land at 2 with the invariant intact
  match m.run 0 [.increment, .increment] with
  | none => return .error "run rejected a legal trace"
  | some (tr, fin) =>
    if fin != 2 then return .error s!"final state {fin} ≠ 2"
    if tr.length != 2 then return .error s!"trace length {tr.length} ≠ 2"
  -- the third increment is rejected (guard fails at 2)
  match m.run 2 [.increment] with
  | some _ => return .error "run accepted a disabled event"
  | none => return .ok ()

-- ── Dsl: machine! generates Label + spec + machine; default safety tactic ──

namespace DslTest

structure Door where
  isOpen : Bool
  locked : Bool
deriving Repr, BEq, DecidableEq

open Machines.Dsl

-- a locked door is never open: `locked → !open`. unlock requires locked;
-- open requires unlocked; both auto-discharged by machine_safety (simp_all).
-- W2.3 proof-of-pattern: the `states:` clause makes machine! generate the
-- whole finite-state entourage — `doorStates`, `doorTrans` (the transition
-- table, computed from the machine), `doorTableStep?` + the agreement
-- theorem `doorTableStep?_eq_step?`, and the `DecidablePred door.Inv`
-- instance — nothing hand-written. (`pairCounter` below stays clause-less:
-- the regression control proving clause-less machines are untouched.)
machine! door where
  State: Door
  Inv: fun s => s.locked → !s.isOpen
  states: [⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩]
  event: unlock guard: (fun s => s.locked) action: (fun s _ => { s with locked := false })
  event: open_ guard: (fun s => !s.locked && !s.isOpen) action: (fun s _ => { s with isOpen := true })
  event: close guard: (fun s => s.isOpen) action: (fun s _ => { s with isOpen := false })
  event: lock guard: (fun s => !s.isOpen) action: (fun s _ => { s with isOpen := false, locked := true })

-- The generated tie theorem, consumed (a table row read through the
-- machine's own `step?`). (Membership by `simp`, not `decide`: core's
-- `Decidable (a ∈ l)` wants `LawfulBEq` keyed to the derived `BEq`, which
-- Door doesn't carry.)
example : door.step? ⟨false, true⟩ .unlock = some ⟨false, false⟩ := by
  rw [← doorTableStep?_eq_step? _ _ (by simp [doorStates])]; rfl

-- ── The entourage unexpanders (pp-only — `Machines.Dsl.entourageUnexp`):
-- the generated names RENDER as the machine's possessive phrase, since the
-- author wrote `machine! door … where …`. The guillemets are the printer's
-- own escaping of the display abbreviation — the honesty mark (these are
-- NOT re-typeable names, and the render doesn't pretend otherwise).

/-- info: «door's states» : List Door -/
#guard_msgs in
#check (doorStates : List Door)

/-- info: «door's table» door.Label.unlock { isOpen := false, locked := true } : Option Door -/
#guard_msgs in
#check (doorTableStep? .unlock ⟨false, true⟩ : Option Door)

/-- info: «door's table = step?» : ∀ (e : door.Label), ∀ s ∈ «door's states», «door's table» e s = door.step? s e -/
#guard_msgs in
#check (doorTableStep?_eq_step? : ∀ (e : door.Label) (s : Door),
  s ∈ doorStates → doorTableStep? e s = door.step? s e)

/-- error: Type mismatch
  «door's transitions»
has type
  List (door.Label × Door × Door)
but is expected to have type
  List Bool
-/
#guard_msgs in
example : List Bool := doorTrans

def dslSmoke : CheckResult := do
  -- run a valid sequence: unlock, open, close, lock — ends locked-and-closed
  _ ← match door.run ⟨false, true⟩ [.unlock, .open_, .close, .lock] with
    | none => .error "valid run rejected"
    | some (tr, fin) =>
      if tr.length == 4 && fin.locked && !fin.isOpen
      then pure ()
      else .error s!"bad final state: {repr fin}"
  -- guard rejection: open_ while locked is rejected, observably
  _ ← match door.run ⟨false, true⟩ [.open_] with
    | none => pure ()
    | some _ => .error "invalid open-while-locked accepted"
  -- the generated table: exactly the 7 enabled (event, from, to) triples
  -- (unlock×2, open_×1, close×2, lock×2 — computed, not hand-copied)
  _ ← assert (doorTrans.length == 7)
    s!"doorTrans has {doorTrans.length} rows, expected 7"
  -- the generated table lookup EXECUTES the machine's step? over the whole
  -- enumerated space (the executable shadow of doorTableStep?_eq_step?)
  _ ← assert (door.labels.all fun l => doorStates.all fun s =>
        doorTableStep? l s == door.step? s l)
    "doorTableStep? disagrees with door.step?"
  pure ()

-- a conjunction invariant: simp_all;omega CANNOT close this (verified
-- 2026-08 — omega loses the s.y ≤ s.x conjunct through the record update);
-- the grind fallback in machine_safety carries it
structure Pair2 where
  x : Nat
  y : Nat
deriving Repr, BEq

machine! pairCounter where
  State: Pair2
  Inv: fun s => s.x ≤ 10 ∧ s.y ≤ s.x
  event: bumpX guard: (fun s => s.x < 10) action: (fun s _ => ⟨s.x + 1, s.y⟩)
  event: bumpY guard: (fun s => s.y < s.x) action: (fun s _ => ⟨s.x, s.y + 1⟩)

def dslConj : CheckResult := do
  match pairCounter.run ⟨0, 0⟩ [.bumpX, .bumpX, .bumpY] with
  | none => .error "valid run rejected"
  | some (_, fin) =>
    if fin == ⟨2, 1⟩ then pure () else .error s!"bad final: {repr fin}"

/-- The conformance battery the door machine inherits (Machines.Testing):
    deadlock-freedom + guard coverage + invariant non-vacuity over the full
    4-state space. Labels, the state space, the completeness proof, and the
    `DecidablePred` instance are ALL GENERATED by machine! — one line. -/
def doorConformance : CheckResult :=
  TestKit.allOf (Machines.Testing.conformance door door.labels doorStates
    door.labels_complete)

-- NEGATIVE CONTROL for the conformance battery: a machine with a dead
-- event (guard never satisfiable) must fail guard-coverage.
machine! broken where
  State: Nat
  Inv: fun _ => True
  event: tick guard: (fun _ => true) action: (fun s _ => s + 1)
  event: dead guard: (fun s => s > 0 ∧ s < 0) action: (fun s _ => s)
    safety: (by intro s h; simp at h)

def conformanceControl : CheckResult :=
  match Machines.Testing.guardCoverage broken broken.labels [0, 1, 2] broken.labels_complete with
  | .error _ => .ok ()
  | .ok () => .error "dead event not caught — the battery is vacuous"

-- THE CARDINALITY GATE the old positional grammar baked into the parser
-- (State first, exactly once) — now an elaboration error with the same
-- force. (The clause-KEYWORD typo surface — `Statez:`, `eventz:` — is
-- NOT upgradable here: a term-led clause swallows an unknown word by
-- juxtaposition, so machine! carries no catch-all. See the limit note
-- on the clause kit in Machines.Dsl.)
/-- error: machine!: missing `State:` clause — the machine's state type -/
#guard_msgs in
machine! noState where
  Inv: fun _ => True
  event: tick guard: (fun _ => true) action: (fun s _ => s)

end DslTest

-- ── 4. Convergent certificates: count-down, cap-minus-fill, close-only ──

namespace ConvTest

open Machines
open Machines.Dsl

-- The count-down idiom machine: a Nat state, the stepDown event subtracts
-- 3 under the guard `s ≥ 3`. Variant (via `Convergent.countDown`) is the
-- state itself. (plain comment: doc comments cannot precede machine! —
-- the custom command rejects them)
machine! countDownThree where
  State: Nat
  Inv: fun _ => True
  event: stepDown guard: (fun s => decide (s ≥ 3)) action: (fun s _ => s - 3)

/-- The stepDown action literally subtracts 3. -/
theorem cd_down_step (s : Nat)
    (h : (countDownThree.event countDownThree.Label.stepDown).guard s = true) :
    (countDownThree.event countDownThree.Label.stepDown).action s h = s - 3 := by
  simp [countDownThree.spec]

/-- The guard `s ≥ 3` is the count-down lower bound. -/
theorem cd_guard_lb (s : Nat)
    (h : (countDownThree.event countDownThree.Label.stepDown).guard s = true) : 3 ≤ s := by
  simpa [countDownThree.spec] using (of_decide_eq_true h)

/-- The count-down certificate: variant = the state itself, each event
    decreases it by 3 (omega at the decrease). -/
def countDownConv : Convergent countDownThree :=
  Convergent.countDown countDownThree (fun s => s) (fun _ => 3)
    (by intro s l h; cases l; exact cd_down_step s h)
    (by intro s l _h; cases l; omega)
    (by intro s l h; cases l; exact cd_guard_lb s h)

/-- The counter machine's increment fills exactly one. -/
theorem counter_inc (max s : Nat)
    (h : ((counterMachine max).event counterMachine.Label.increment).guard s = true) :
    s + 1 ≤ ((counterMachine max).event counterMachine.Label.increment).action s h := by
  simp [counterMachine.spec]

/-- The counter's guard `s < max` keeps the post-state inside the cap — the
    machine invariant `s ≤ max` read at the action. -/
theorem counter_bounded (max s : Nat)
    (h : ((counterMachine max).event counterMachine.Label.increment).guard s = true) :
    s + 1 ≤ max := by
  have hs : s < max := by
    simpa [counterMachine.spec] using (of_decide_eq_true h)
  omega

/-- The counter's cap-minus-fill certificate: variant = `max - s`, each
    increment spends one. The door machine by contrast is NOT convergent
    (see `door_is_not_convergent` below) — the counter is the convergent
    budget shape. -/
def counterConv (max : Nat) : Convergent (counterMachine max) :=
  Convergent.capMinusFill (counterMachine max) (fun s => s) max
    (by intro s l h; cases l; exact counter_inc max s h)
    (by intro s l h; cases l; simpa [counterMachine.spec] using counter_bounded max s h)

-- The close-only machine: a door with the single `slam` event (the door's
-- NOT convergent — a close-only fragment is). Variant: open = 1, closed = 0.
machine! closeOnly where
  State: Bool
  Inv: fun _ => True
  event: slam guard: (fun b => b) action: (fun _ _ => false)

/-- The close-only certificate: variant `if open then 1 else 0`; the action
    closes, taking 1 to 0. -/
def closeOnlyConv : Convergent closeOnly :=
  ⟨fun b => if b then 1 else 0, by
    intro b l h
    cases l
    have hg : b = true := by simpa [closeOnly.spec] using h
    subst hg
    simp [closeOnly.spec]⟩

/-- The door's lock event is a self-loop at the locked-closed state: an
    infinite run witness, the reason the door machine is NOT convergent. -/
def doorLockSteps : Nat → DslTest.Door := fun _ => ⟨false, true⟩

theorem door_infinite_run : Machine.InfiniteRun DslTest.door doorLockSteps := by
  intro n
  refine ⟨DslTest.door.Label.lock, ?_⟩
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

/-- The door machine has NO convergence certificate: a convergent machine
    cannot have an infinite run (`Convergent.terminates`). This is why the
    task's proposed door variant (locked 2 / open 1 / closed 0) fails — the
    `lock` self-loop at locked-closed is enabled yet does not decrease.
    The convergent analogues exercised above are the counter (cap-minus-
    fill) and the close-only fragment. -/
theorem door_is_not_convergent : ¬ Nonempty (Convergent DslTest.door) := by
  intro h
  obtain ⟨c⟩ := h
  exact Convergent.terminates c doorLockSteps door_infinite_run

/-- The run-length bound, at proof level: a successful counter run of 3
    steps from 0 has 3 ≤ 5 = variant 0. -/
example : ∀ (tr : Machine.Trace (counterMachine 5)) (fin : Nat),
    (counterMachine 5).run 0 (List.replicate 3 counterMachine.Label.increment) = some (tr, fin) →
    3 ≤ 5 := by
  intro tr fin h
  have hle := Convergent.run_length_bound (counterConv 5) 0
    (List.replicate 3 counterMachine.Label.increment) tr fin h
  omega

/-- Executable checks: the certificate numerics and the guard rejections. -/
def convergentSmoke : CheckResult := Id.run do
  -- count-down: 10 → 7 → 4 → 1 in three steps; a fourth from 1 is rejected
  match countDownThree.run 10 [.stepDown, .stepDown, .stepDown] with
  | none => return .error "count-down rejected a legal run"
  | some (tr, fin) =>
    if fin != 1 then return .error s!"count-down final state {fin} ≠ 1"
    if tr.length != 3 then return .error s!"count-down trace length {tr.length} ≠ 3"
  match countDownThree.run 1 [.stepDown] with
  | some _ => return .error "count-down accepted a below-threshold step"
  | none => pure ()
  -- counter: five increments reach the cap; the sixth is rejected (the
  -- run-length bound: any successful run has length ≤ 5 = variant 0)
  match (counterMachine 5).run 0 (List.replicate 5 counterMachine.Label.increment) with
  | none => return .error "counter rejected a legal run"
  | some (_, fin) => if fin != 5 then return .error s!"counter final {fin} ≠ 5"
  match (counterMachine 5).run 0 (List.replicate 6 counterMachine.Label.increment) with
  | some _ => return .error "counter accepted an over-cap run"
  | none => pure ()
  -- close-only: an open door slams closed; slamming a closed door is rejected
  match closeOnly.run true [.slam] with
  | none => return .error "close-only rejected a legal slam"
  | some (_, fin) => if fin != false then return .error "close-only did not close"
  match closeOnly.run false [.slam] with
  | some _ => return .error "close-only slammed a closed door"
  | none => pure ()
  -- the door's lock self-loop is a legal run of arbitrary length (the
  -- infinite-run witness behind `door_is_not_convergent`)
  match DslTest.door.run ⟨false, true⟩ (List.replicate 5 DslTest.door.Label.lock) with
  | none => return .error "door lock self-loop rejected"
  | some _ => return .ok ()

end ConvTest

-- ── 5. Sync primitives (Machines.Sync): the contract theorems as checks ──

namespace SyncTest

open Machines.Sync

/-- The latch contract: run to completion, verify the closed-count_down
    rejection and the wait-stability theorems hold on the executable path. -/
def latchChecks : CheckResult := do
  -- full countdown + wait: completes
  match (latch 3).run ⟨3, 0⟩ [.countDown, .countDown, .countDown, .wait] with
  | none => .error "valid latch run rejected"
  | some (_, fin) =>
    if fin.count == 0 && fin.arrived == 3 then pure ()
    else .error s!"bad latch final: {repr fin}"
  -- count_down past zero is rejected (the contract theorem, executable)
  match (latch 1).run ⟨1, 0⟩ [.countDown, .countDown] with
  | none => pure ()
  | some _ => .error "count_down past zero accepted"
  -- wait before completion is rejected
  match (latch 2).run ⟨2, 0⟩ [.wait] with
  | none => pure ()
  | some _ => .error "wait at count>0 accepted"

/-- The mpsc contract: capacity bound + closed rejection. -/
def mpscChecks : CheckResult := do
  -- send up to capacity, recv, send again: works
  match (mpsc Nat).run ⟨[], 2, false⟩ [.send 1, .send 2, .recv, .send 3] with
  | none => .error "valid mpsc run rejected"
  | some _ => pure ()
  -- send past capacity: rejected
  match (mpsc Nat).run ⟨[], 2, false⟩ [.send 1, .send 2, .send 3] with
  | none => pure ()
  | some _ => .error "send past capacity accepted"
  -- send after close: rejected
  match (mpsc Nat).run ⟨[1], 5, false⟩ [.close, .send 2] with
  | none => pure ()
  | some _ => .error "send after close accepted"

/-- The oneshot contract: exactly-once send, recv-after-send. -/
def oneshotChecks : CheckResult := do
  match (oneshot Nat).run .empty [.send 42, .recv] with
  | none => .error "valid oneshot run rejected"
  | some _ => pure ()
  match (oneshot Nat).run .empty [.send 1, .send 2] with
  | none => pure ()
  | some _ => .error "double send accepted"
  match (oneshot Nat).run .empty [.recv] with
  | none => pure ()
  | some _ => .error "recv before send accepted"

/-- The barrier contract: all parties arrive before proceed. -/
def barrierChecks : CheckResult := do
  match barrier.run ⟨0, 2, false⟩ [.arrive, .arrive, .proceed] with
  | none => .error "valid barrier run rejected"
  | some (_, fin) =>
    if fin.released then pure () else .error "barrier not released after full arrival"
  match barrier.run ⟨0, 2, false⟩ [.proceed] with
  | none => pure ()
  | some _ => .error "proceed before release accepted"

/-- The semaphore contract: acquire/release bounding. -/
def semChecks : CheckResult := do
  match semaphore.run ⟨2, 2⟩ [.acquire, .acquire, .release, .acquire] with
  | none => .error "valid semaphore run rejected"
  | some _ => pure ()
  match semaphore.run ⟨1, 1⟩ [.acquire, .acquire] with
  | none => pure ()
  | some _ => .error "acquire at zero permits accepted"
  match semaphore.run ⟨1, 1⟩ [.release] with
  | none => pure ()
  | some _ => .error "release past capacity accepted"

/-- The mpsc channel over the SAMPLED conformance battery (W2.3(d)):
    `send` carries a Nat payload, so no finite label enumeration exists
    (machine! generates none for payload machines) — the caller supplies
    the label sample (one per constructor shape) and the state enumeration. -/
instance : DecidablePred (mpsc Nat).Inv :=
  fun s => inferInstanceAs (Decidable (s.buf.length ≤ s.cap))

def mpscConformance : CheckResult :=
  TestKit.allOf (Machines.Testing.conformanceOver (mpsc Nat)
    [.send 0, .recv, .close]
    [⟨[], 1, false⟩, ⟨[0], 1, false⟩, ⟨[0], 1, true⟩, ⟨[0, 0], 1, false⟩])

/-- NEGATIVE CONTROL for the sampled battery: over an all-closed state
    enumeration the sampled `send` never fires — guard-coverage must catch
    it (a vacuous battery would pass). -/
def mpscConformanceControl : CheckResult :=
  match Machines.Testing.guardCoverageOver (mpsc Nat) [.send 0] [⟨[], 1, true⟩] with
  | .error _ => .ok ()
  | .ok () => .error "dead sampled event not caught — the battery is vacuous"

end SyncTest

-- ── 6. LinearMachine: machines over change groups (Machines.LinearMachine) ──

namespace LinearTest

open Machines

/-- Raw-form Int lemmas: `Int.add_assoc` etc. are stated over `+`, whose
    elaborated head (`HAdd.hAdd`) does not syntactically match the raw
    `Int.add` applications that `patch`/`step?` reduce to. -/
theorem iadd_assoc (a b c : Int) : Int.add (Int.add a b) c = Int.add a (Int.add b c) := by
  show a + b + c = a + (b + c)
  rw [Int.add_assoc]

theorem iadd_comm (a b : Int) : Int.add a b = Int.add b a := by
  show a + b = b + a
  rw [Int.add_comm]

theorem imul_add (a b c : Int) : Int.mul (Int.add a b) c = Int.add (Int.mul a c) (Int.mul b c) := by
  show (a + b) * c = a * c + b * c
  rw [Int.add_mul]

-- Int carries mathlib's `AddCommGroup` — the bridge group instance.

-- A translation-equivariant counter on `Int`: bump adds 1. The linearity
-- law holds with the IDENTITY delta transform: `(s + δ) + 1 = (s + 1) + δ`
-- — a constant offset persists through the dynamics.
machine! deltaCounter where
  State: Int
  Inv: fun _ => True
  event: bump guard: (fun _ => true) action: (fun s _ => s + 1)

instance : LinearMachine deltaCounter where
  eventDelta := fun _ δ => δ
  linear := by
    intro s δ l
    cases l
    have hg : ∀ x : Int, (deltaCounter.event deltaCounter.Label.bump).guard x = true :=
      fun _ => rfl
    rw [Machine.step?_eq, dif_pos (hg _), Machine.step?_eq, dif_pos (hg _), patchOpt]
    congr 1
    show Int.add (Int.add s δ) 1 = Int.add (Int.add s 1) δ
    rw [iadd_assoc, iadd_comm δ 1, ← iadd_assoc]

-- A machine whose delta transform is NOT the identity: doubling scales
-- the delta (`eventDelta _ δ = δ * 2`), since `(s + δ) * 2 = s * 2 + δ * 2`.
machine! doubler where
  State: Int
  Inv: fun _ => True
  event: double guard: (fun _ => true) action: (fun s _ => s * 2)

instance : LinearMachine doubler where
  eventDelta := fun _ δ => δ * 2
  linear := by
    intro s δ l
    cases l
    have hg : ∀ x : Int, (doubler.event doubler.Label.double).guard x = true :=
      fun _ => rfl
    rw [Machine.step?_eq, dif_pos (hg _), Machine.step?_eq, dif_pos (hg _), patchOpt]
    congr 1
    show Int.mul (Int.add s δ) 2 = Int.add (Int.mul s 2) (Int.mul δ 2)
    rw [imul_add]

/-- THE THEOREM at the doubler: the batch run of the patched machine equals
    the batch run of the base machine corrected by the pure delta chain. -/
theorem doublerIncremental (s₀ δ : Int) (trace : List doubler.Label) :
    doubler.runState (patch s₀ δ) trace =
      (doubler.runState s₀ trace).map (fun fin => patch fin (doubler.deltaChain δ trace)) :=
  incremental_run_equiv doubler s₀ δ trace

/-- Executable checks: batch vs incremental on both machines. -/
def linearSmoke : CheckResult := do
  -- counter, batch: 0 → 1 → 2 → 3
  match deltaCounter.runState 0 [.bump, .bump, .bump] with
  | none => .error "counter batch run rejected"
  | some fin => if fin != 3 then .error s!"counter batch final {fin} ≠ 3"
  -- counter, incremental: the identity delta transform passes δ through
  let Δc := deltaCounter.deltaChain 1 [.bump, .bump, .bump]
  if Δc != 1 then .error s!"counter delta chain {Δc} ≠ 1"
  match deltaCounter.runState (patch 0 1) [.bump, .bump, .bump] with
  | none => .error "counter incremental run rejected"
  | some fin => if fin != 4 then .error s!"counter incremental final {fin} ≠ 4"
  -- the delta-only step consumes no state: the transform is the identity
  if deltaCounter.incrementalStep 7 deltaCounter.Label.bump != 7 then
    .error "counter incrementalStep wrong"
  -- doubler: batch 3 → 6 → 12; the incremental run from (3, δ=1) — state 4 —
  -- gives 16, and batch-final + chain = 12 + 4 = 16: they agree
  match doubler.runState 3 [.double, .double] with
  | none => .error "doubler batch run rejected"
  | some base =>
    let Δ := doubler.deltaChain 1 [.double, .double]
    if Δ != 4 then .error s!"doubler delta chain {Δ} ≠ 4"
    match doubler.runState (patch 3 1) [.double, .double] with
    | none => .error "doubler incremental run rejected"
    | some fin =>
      if fin != 16 then .error s!"doubler incremental final {fin} ≠ 16"
      if base + Δ != fin then .error s!"doubler chain {base}+{Δ} ≠ {fin}"

-- The doubler's incremental-agreement sweep retired as a pair with its
-- sabotage control (T5): `incremental_run_equiv` — applied as
-- `doublerIncremental` above — proves the equation for ALL (start, delta,
-- trace) triples; `linearSmoke` pins the concrete numerics.

end LinearTest

-- ── driver (TestKit) ──────────────────────────────────────────────

/-! ## Sim — the DST core (Machines.Sim): executable checks -/

namespace SimTest

open Machines
open Machines.Sync
open Machines.Sim
open TestKit

/-- An always-enabled add machine — the additive component (the
    `Machines.Sim.addMachine` shape, computable at `Int`). -/
@[reducible]
def intAdd : Machine where
  State := Int
  Label := Int
  Inv := fun _ => True
  event := fun δ =>
    { guard := fun _ => true
    , action := fun s _ => s + δ
    , safety := fun _ _ h => h }

/-- A capped-add machine: `add δ` enabled while the result stays within
    the cap — gives the sim a BLOCKED delivery to exercise. -/
@[reducible]
def cappedAdd : Machine where
  State := Int
  Label := Int
  Inv := fun s => s ≤ 10
  event := fun δ =>
    { guard := fun s => decide (s + δ ≤ 10)
    , action := fun s _ => s + δ
    , safety := by
        intro s h _
        have hle : s + δ ≤ 10 := by simpa using h
        exact hle }

/-- Two replicas of `intAdd` at 0, deltas 3 and 4 in flight to
    replica 1. -/
def twoDelta : SimState intAdd Nat :=
  { comp := fun _ => 0
  , inflight := [{ src := 0, dst := 1, lbl := 3 }, { src := 0, dst := 1, lbl := 4 }]
  , clock := 0 }

/-- 1. Delivery applies the delta at the destination; the queue drains
    (delivered, not lost). -/
def delivery : CheckResult := do
  let fin := runSim [.deliver 0, .deliver 0] twoDelta
  if fin.comp 1 != 7 then .error s!"delivery: comp 1 = {fin.comp 1} ≠ 7"
  else if !fin.inflight.isEmpty then .error "delivery: queue not drained"
  else if fin.clock != 2 then .error s!"delivery: clock {fin.clock} ≠ 2"
  else pure ()

/-- 2. Replay determinism, executed: the same schedule list from the
    same state gives the same final state and trace length — the
    schedule is data, re-evaluation is replay. -/
def replay : CheckResult := do
  let chs : List (Choice intAdd Nat) :=
    [.deliver 0, .fire 1 3, .tick, .deliver 0]
  let a := runSim chs twoDelta
  let b := runSim chs twoDelta
  if a.comp 1 != b.comp 1 || a.clock != b.clock
     || a.inflight.length != b.inflight.length then
    .error "replay: same schedule, different final states"
  else if (simTrace chs twoDelta).length != chs.length + 1 then
    .error "replay: trace length ≠ schedule length + 1"
  else pure ()

/-- 3. Schedule-independence, executed: opposite delivery orders of the
    two deltas reach the SAME state — the CRDT point (`Int`'s
    commutativity standing in for the ZSet group). -/
def scheduleIndependence : CheckResult := do
  let a := runSim [.deliver 0, .deliver 0] twoDelta
  let b := runSim [.deliver 1, .deliver 0] twoDelta
  if a.comp 1 != b.comp 1 then
    .error s!"orders diverged: {a.comp 1} vs {b.comp 1}"
  else if a.comp 1 != 7 then .error s!"converged to {a.comp 1} ≠ 7"
  else pure ()

/-- 4. Blocked delivery is a NO-OP: at the cap, `add 3` cannot fire —
    the message STAYS in flight, the state and clock are untouched
    (conservation's blocked path). -/
def blockedStays : CheckResult := do
  let σ : SimState cappedAdd Nat :=
    { comp := fun _ => 10
    , inflight := [{ src := 0, dst := 1, lbl := 3 }]
    , clock := 0 }
  let fin := stepSim (.deliver 0) σ
  if fin.comp 1 != 10 then .error "blocked delivery changed the state"
  else if fin.inflight.isEmpty then .error "blocked delivery DROPPED the message"
  else if fin.clock != 0 then .error "blocked delivery ticked the clock"
  else pure ()

/-- 5. Component reuse: the sim's components are ANY Core machines —
    here a `Machines.Sync.mpsc` channel replica receives a `send 7`
    through the queue. -/
def mpscComponent : CheckResult := do
  let σ : SimState (mpsc Nat) Nat :=
    { comp := fun _ => ⟨[], 2, false⟩
    , inflight := [{ src := 0, dst := 1, lbl := .send 7 }]
    , clock := 0 }
  let fin := stepSim (.deliver 0) σ
  if fin.comp 1 == ⟨[7], 2, false⟩ then pure ()
  else .error s!"mpsc delivery wrong: {repr (fin.comp 1)}"

/-- 6. NEGATIVE CONTROL for the no-loss theorem: a buggy step that
    DROPS the message on "delivery" (erases without applying) loses it —
    the message vanishes from the queue while the destination is
    unchanged. The control passes only when the loss is DETECTED. -/
def buggyDropControl : CheckResult := do
  -- the buggy stepSim: erase on delivery, never apply the event
  let buggyStep (ch : Choice intAdd Nat) (σ : SimState intAdd Nat) :
      SimState intAdd Nat :=
    match ch with
    | .deliver i =>
        match σ.inflight[i]? with
        | none => σ
        | some _ => { σ with inflight := σ.inflight.eraseIdx i, clock := σ.clock + 1 }
    | _ => stepSim ch σ
  let σ : SimState intAdd Nat :=
    { comp := fun _ => 0, inflight := [{ src := 0, dst := 1, lbl := 5 }], clock := 0 }
  let honest := stepSim (.deliver 0) σ
  let buggy := buggyStep (.deliver 0) σ
  -- honest: delivered (applied at dst, queue drained)
  if honest.comp 1 != 5 || !honest.inflight.isEmpty then
    .error "control broken: honest step did not deliver"
  -- buggy: the message is gone from the queue AND the destination never
  -- changed — vanished without effect = LOST. Detected?
  else if buggy.inflight.isEmpty && buggy.comp 1 == 0 && buggy.comp 1 != honest.comp 1 then
    pure ()  -- the drop-bug is caught: message lost, not delivered
  else
    .error "drop-bug NOT caught — the no-loss check is vacuous"

def simChecks : List (String × CheckResult) :=
  [("sim-delivery", delivery)
  , ("sim-replay-determinism", replay)
  , ("sim-schedule-independence", scheduleIndependence)
  , ("sim-blocked-stays", blockedStays)
  , ("sim-mpsc-component", mpscComponent)
  , ("sim-no-loss-control", buggyDropControl)]

end SimTest

/-! ## Session types — the WIT conversation choreography (Machines.Session) -/

namespace TypedSessTest

open Machines.Session

/-- Any payload universe works: the same facts hold of `Nat` payloads —
    the layer is GENERIC (the schema-lang tie instantiates
    `P := SchemaLang.Ty`; Machines owns the mechanism). The `P :=
    String` demo instance (`gatewayProto`) was deleted — the real
    conversation is pinned in `SchemaLang.Session` + `wit/gateway.wit`. -/
def natProto : TProtocol Nat := [(.snd, 64), (.rcv, 7)]

/-- Deriving, not stating: the peer's script is COMPUTED by the
    unifier — `instIsDualOf` fixes `theirs := tdual mine`, so the two
    sides of a conversation cannot drift apart by construction. -/
def peerOf (mine : TProtocol Nat) : TProtocol Nat := tdual mine

def typedChecks : CheckResult := do
  -- the typed dual is an involution for ANY payload universe
  _ ← assertEq "tdual involution (Nat payloads)" (tdual (tdual natProto)) natProto
  -- the typed dual keeps the PAYLOAD sequence (generic `tdual_types`)
  _ ← assertEq "tdual keeps payloads" ((tdual natProto).map (·.2))
      (natProto.map (·.2))
  -- directions oppose pairwise (the typed lockstep condition)
  _ ← assertEq "tdual directions oppose"
      (List.all (List.zip (natProto.map (·.1)) ((tdual natProto).map (·.1)))
        (fun x => x.1 != x.2)) true
  -- the session machine is payload-generic: it walks the Nat-payload
  -- script directly (mid-protocol liveness at ANY universe)
  let midOk := (List.finRange natProto.length).all (fun i =>
    (session natProto).enabled i.val i)
  _ ← assert midOk "typed mid-protocol liveness"
  -- the agreeing peer, derived: it IS the dual
  _ ← assertEq "derived peer is the dual" (peerOf natProto)
      (tdual natProto)
  .ok ()

/-- Positive half: the hand-written dual of the gateway conversation
    ELABORATES — instance search unifies the script against the dual of
    the original. A gate that rejects everything is as vacuous as one
    that accepts everything. -/
theorem peerElaborates : IsDualOf [(.rcv, "u64"), (.snd, "option<user>")]
                                 [(.snd, "u64"), (.rcv, "option<user>")] :=
  instIsDualOf [(Dir.snd, "u64"), (Dir.rcv, "option<user>")]

-- THE ELABORATION-ERROR PIN (direction half): a peer whose direction
-- does not flip is a TYPE error — instance search fails at elaboration
-- (no runtime check exists to miss). The docstring below pins the exact
-- failure; a mismatched message fails this module's BUILD.
/-- error: failed to synthesize instance of type class
  IsDualOf [(Dir.rcv, "u64"), (Dir.rcv, "option<user>")] [(Dir.snd, "u64"), (Dir.rcv, "option<user>")]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (inferInstance : IsDualOf [(.rcv, "u64"), (.rcv, "option<user>")]
                                 [(.snd, "u64"), (.rcv, "option<user>")])

-- THE ELABORATION-ERROR PIN (payload half): a peer whose PAYLOAD
-- differs at any position is equally a type error.
/-- error: failed to synthesize instance of type class
  IsDualOf [(Dir.rcv, "u64"), (Dir.snd, "string")] [(Dir.snd, "u64"), (Dir.rcv, "option<user>")]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (inferInstance : IsDualOf [(.rcv, "u64"), (.snd, "string")]
                                 [(.snd, "u64"), (.rcv, "option<user>")])

end TypedSessTest

/-! ## guestlang_solver — the OPEN discharge macro (W6.8): a package-local
    rung extends it via `macro_rules`, no edit to Machines. -/

namespace SolverTest

/-- Scratch proposition the default ladder CANNOT close. -/
inductive Latched : Nat → Prop where
  | ofZero : Latched 0

/-- The package-local rung: one `macro_rules` line against the shared
    syntax. Backtracking keeps every other rung reachable — this closer
    fails fast on non-`Latched` goals. -/
macro_rules | `(tactic| guestlang_solver) => `(tactic| exact Latched.ofZero)

-- The custom rung fires: the default ladder (simp_all/omega/grind/trivial)
-- cannot close `Latched 0`.
example : Latched 0 := by guestlang_solver

-- The default ladder still fires: the custom rung fails fast on an
-- arithmetic goal and falls through to omega.
example (n : Nat) (h : n ≤ 2) : n ≤ 5 := by guestlang_solver

-- `machine_safety` is the same solver: the custom rung serves the DSL's
-- default discharge too.
example : Latched 0 := by machine_safety

end SolverTest

-- ── 7. Fusion bridges (Machines.Fusion): the dbsp-machine cluster ──

namespace FusionTest

open Machines
open Machines.Fusion

-- The D/I iso: both directions ARE the landed laws (nothing re-proved —
-- the pin makes the iso's fields name the theorems).
#check @Machines.Fusion.dI

example {a : Type} [AddCommGroup a] (s : Dbsp.Stream a) :
    (Machines.Fusion.dI a).to ((Machines.Fusion.dI a).inv s) = s :=
  Dbsp.derivative_integral s

example {a : Type} [AddCommGroup a] (s : Dbsp.Stream a) :
    (Machines.Fusion.dI a).inv ((Machines.Fusion.dI a).to s) = s :=
  Dbsp.integral_derivative s

/-- The iso EXECUTES: D then I on a concrete Int stream recovers it —
the journal/replay round trip, numerically. -/
def fusionIso : CheckResult :=
  let s : Dbsp.Stream Int := fun t => (t * t : Int)
  let iso := Machines.Fusion.dI Int
  let ts := [0, 1, 2, 5, 9]
  assert (ts.all (fun t => iso.to (iso.inv s) t == s t && iso.inv (iso.to s) t == s t))
    "I∘D / D∘I diverged on the sample"

-- The convergence bridge: the settle machine's cascade terminates AT
-- the dbsp fixpoint (the trivially-stabilizing rule R := id pins it).
#check @Machines.Fusion.settle_reaches_seminaive
#check @Machines.Fusion.settle_run_bounded

example :
    ∃ tr, (Machines.Fusion.settleMachine (fun (_ : Int) (s : Int) => s) 7).run ((0 : Int), 3)
      (List.replicate 3 ()) = some (tr, (Dbsp.seminaive (fun (_ : Int) (s : Int) => s) 7, 0)) :=
  Machines.Fusion.settle_reaches_seminaive (fun (_ : Int) (s : Int) => s) 7 3 rfl

-- The bisimulation bridge fixture: a machine with a genuine bisimilar
-- pair of DISTINCT states — 0 and 5 both reset to 0 on the next tick
-- and agree forever after.
machine! resetToZero where
  State: Int
  Inv: fun _ => True
  event: reset guard: (fun s => decide (s != 0)) action: (fun _ _ => 0)

-- tick-agreement over the (single-ctor) label enumeration, DECIDED —
-- the finite-machine decidability note, executed:
example : (0 : Int) ≠ 5 ∧
    resetToZero.tick resetToZero.Label.reset 0
      = resetToZero.tick resetToZero.Label.reset 5 :=
  ⟨by decide, rfl⟩

-- NEGATIVE CONTROL: the door machine's closed/unlocked vs closed/locked
-- states are distinguished by open_ (tick-agreement FAILS) — the bridge
-- is not vacuously true.
example : DslTest.door.tick DslTest.door.Label.open_ ⟨false, false⟩
    ≠ DslTest.door.tick DslTest.door.Label.open_ ⟨false, true⟩ := by
  decide

-- The stream consequence, decided: the response streams of the bisimilar
-- pair are EQUAL at every sampled time under the all-reset input.
def fusionBisim : CheckResult :=
  let ins : Dbsp.Stream resetToZero.Label := fun _ => resetToZero.Label.reset
  let ts := [0, 1, 2, 5, 11]
  let same := ts.all (fun t =>
    respStream resetToZero 0 ins t == respStream resetToZero 5 ins t)
  -- the DOOR pair's streams really diverge (the negative control, streams)
  let dins : Dbsp.Stream DslTest.door.Label := fun _ => DslTest.door.Label.open_
  let doorDiverges :=
    respStream DslTest.door ⟨false, false⟩ dins 0
      != respStream DslTest.door ⟨false, true⟩ dins 0
  assert (same && doorDiverges) "bisim response-stream check failed"

def fusionChecks : List (String × CheckResult) :=
  [("fusion-d/i-iso", fusionIso)
  , ("fusion-bisim-streams", fusionBisim)]

end FusionTest

def main : IO UInt32 := do
  let code ← TestKit.mainOfChecks "Machines" ([
    ("machine-trace", machineTrace),
    ("dsl-door", DslTest.dslSmoke),
    ("dsl-conj", DslTest.dslConj),
    ("dsl-conformance", DslTest.doorConformance),
    ("dsl-conformance-control", DslTest.conformanceControl),
    ("convergent-smoke", ConvTest.convergentSmoke),
    ("sync-latch", SyncTest.latchChecks),
    ("sync-mpsc", SyncTest.mpscChecks),
    ("sync-oneshot", SyncTest.oneshotChecks),
    ("sync-barrier", SyncTest.barrierChecks),
    ("sync-semaphore", SyncTest.semChecks),
    ("sync-mpsc-conformance", SyncTest.mpscConformance),
    ("sync-mpsc-conformance-control", SyncTest.mpscConformanceControl),
    ("linear-machine", LinearTest.linearSmoke)
    , ("session-typed", TypedSessTest.typedChecks)
    ] ++ SimTest.simChecks ++ FusionTest.fusionChecks)
  return code


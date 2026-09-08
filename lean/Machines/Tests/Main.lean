/-
# Machines Tests — executable checks

The package rule (from Flatland): what is not yet proved gets an executable
check. Here:

1. **Dag differential**: `reachesFuel`-based `checkAcyclic` vs a reference
   boolean transitive closure — exhaustive over all DAGs on 3 nodes
   (8 dep-lists per node ⇒ 8³ = 512 DAGs). This is the completeness evidence
   for `reachesFuel` until the proof lands (Foundations.lean documents the
   gap); two independent implementations must agree.
2. **Machine.run**: a counter machine — the invariant survives a trace;
   a disabled event rejects the run.
3. **ReprOp** smoke: the SmallVec-buffer ↔ zset-map abstraction, with the
   square PROVED (the kit dogfooding itself).

Run: `lake build MachinesTests && .lake/build/bin/MachinesTests`
-/
import Machines
import TestKit

open Machines
open TestKit

-- ── 1. Dag differential ─────────────────────────────────────────────────

/-- Reference reachability: boolean transitive closure by n relaxations —
    independent of `reachesFuel`. -/
def refReaches {n : Nat} (d : Dag n) (a b : Fin n) : Bool := Id.run do
  let nodes := List.finRange n
  let mut reach : Array (Array Bool) :=
    nodes.toArray.map fun v =>
      nodes.toArray.map fun w => decide (w ∈ d.deps v)
  for _ in [0 : n] do
    reach := reach.map fun row =>
      row.zipIdx.map fun (rij, j) =>
        rij || (List.finRange n).any (fun k => row[k.val]! && reach[k.val]![j]!)
  return reach[a]![b]!

/-- The DAG on 3 nodes whose dep-lists are the three mask bits. -/
def dagOfMasks (m0 m1 m2 : Nat) : Dag 3 :=
  ⟨fun v =>
    let mask := if v.val = 0 then m0 else if v.val = 1 then m1 else m2
    (List.finRange 3).filter (fun w => (mask >>> w.val) &&& 1 == 1)⟩

/-- All 512 DAGs on 3 nodes. -/
def allDags3 : List (Dag 3) :=
  (List.range 512).map fun i => dagOfMasks ((i / 64) % 8) ((i / 8) % 8) (i % 8)

/-- `checkAcyclic` must agree with "no self-reach in the reference closure"
    on every small DAG. -/
def dagDifferential : CheckResult := Id.run do
  for d in allDags3 do
    let checked := d.checkAcyclic
    let reference := !((List.finRange 3).any (fun v => refReaches d v v))
    if checked != reference then
      return .error s!"disagreement: checkAcyclic={checked} ref={reference}"
  return .ok ()

/-- topoSort? on a known DAG puts deps first. -/
def topoSmoke : CheckResult := Id.run do
  -- 0 ← 1 ← 2 (each depends on the previous)
  let d : Dag 3 := ⟨fun v =>
    if h : v.val = 0 then [] else [⟨v.val - 1, by have hv := v.isLt; omega⟩]⟩
  match d.topoSort? with
  | none => return .error "topoSort? rejected a DAG"
  | some l =>
    match l.map (·.val) with
    | [0, 1, 2] => return .ok ()
    | _ => return .error s!"unexpected order: {l.map (·.val)}"

-- ── 2. The counter machine ──────────────────────────────────────────────

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

-- ── 3. ReprOp: buffer ↔ zset-map ───────────────────────────────────────

/-- The hot delta buffer (unordered, may contain canceling entries) denotes
    a weight map. NOTE: the zset semantics SUMS all entries for a key —
    a shadowing lookup would be a different (wrong) semantics, and the
    square would not commute. Two buffers denote the same zset — no inverse;
    the law lives on the operation. -/
instance bufDenotes : Denotes (List (Nat × Int)) (Nat → Int) where
  abs buf := fun k => ((buf.filter (fun e => e.1 == k)).map (·.2)).sum

theorem filter_sum_push (buf : List (Nat × Int)) (k : Nat) (w : Int) (k' : Nat) :
    (((k, w) :: buf).filter (fun e => e.1 == k') |>.map Prod.snd).sum
      = ((buf.filter (fun e => e.1 == k') |>.map Prod.snd)).sum + (if k' == k then w else 0) := by
  rw [List.filter_cons]
  by_cases h : (k == k') = true
  · rw [if_pos h]
    rw [List.map_cons, List.sum_cons]
    have hk : k' = k := (beq_iff_eq.mp h).symm
    subst hk
    rw [if_pos (beq_self_eq_true k')]
    omega
  · have h2 : ¬ ((k' == k) = true) := fun hc => h (by
      rw [beq_iff_eq] at hc ⊢
      exact hc.symm)
    rw [if_neg h, if_neg h2]
    simp

/-- push onto the buffer ≡ add the weight. The square, proved. -/
def bufferPush (k : Nat) (w : Int) : ReprOp (List (Nat × Int)) (Nat → Int) where
  opR := fun buf => (k, w) :: buf
  opA := fun f k' => f k' + (if k' == k then w else 0)
  respects := by
    intro buf
    funext k'
    exact filter_sum_push buf k w k'

def reprOpSmoke : CheckResult :=
  let buf : List (Nat × Int) := [(1, 10), (2, 20), (1, -4)]
  let pushed := (bufferPush 3 7).opR buf
  let f := Denotes.abs buf
  let g := Denotes.abs pushed
  -- keys 1/2 unchanged; key 3 gains 7; and the SUM semantics shows through:
  -- key 1 has entries 10 and -4, so f 1 = 6
  assert (f 1 == 6 && g 1 == f 1 && g 2 == f 2 && g 3 == f 3 + 7) "square failed on samples"

-- ── Dsl: machine! generates Label + spec + machine; default safety tactic ──

namespace DslTest

structure Door where
  isOpen : Bool
  locked : Bool
deriving Repr, BEq

open Machines.Dsl

-- a locked door is never open: `locked → !open`. unlock requires locked;
-- open requires unlocked; both auto-discharged by machine_safety (simp_all).
machine! door where
  State: Door
  Inv: fun s => s.locked → !s.isOpen
  event: unlock guard: (fun s => s.locked) action: (fun s _ => { s with locked := false })
  event: open_ guard: (fun s => !s.locked && !s.isOpen) action: (fun s _ => { s with isOpen := true })
  event: close guard: (fun s => s.isOpen) action: (fun s _ => { s with isOpen := false })
  event: lock guard: (fun s => !s.isOpen) action: (fun s _ => { s with isOpen := false, locked := true })

def dslSmoke : CheckResult := do
  -- run a valid sequence: unlock, open, close, lock — ends locked-and-closed
  match door.run ⟨false, true⟩ [.unlock, .open_, .close, .lock] with
  | none => .error "valid run rejected"
  | some (tr, fin) =>
    if tr.length == 4 && fin.locked && !fin.isOpen
    then pure ()
    else .error s!"bad final state: {repr fin}"
  -- guard rejection: open_ while locked is rejected, observably
  match door.run ⟨false, true⟩ [.open_] with
  | none => pure ()
  | some _ => .error "invalid open-while-locked accepted"

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
    4-state space. The labels list is GENERATED by machine! — one line. -/
def doorConformance : CheckResult :=
  TestKit.allOf (Machines.Testing.conformance door door.labels
    ([⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩] : List Door))

-- NEGATIVE CONTROL for the conformance battery: a machine with a dead
-- event (guard never satisfiable) must fail guard-coverage.
machine! broken where
  State: Nat
  Inv: fun _ => True
  event: tick guard: (fun _ => true) action: (fun s _ => s + 1)
  event: dead guard: (fun s => s > 0 ∧ s < 0) action: (fun s _ => s)
    safety: (by intro s h; simp at h)

def conformanceControl : CheckResult :=
  match Machines.Testing.guardCoverage broken broken.labels [0, 1, 2] with
  | .error _ => .ok ()
  | .ok () => .error "dead event not caught — the battery is vacuous"

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
  match (barrier 2).run ⟨0, 2, false⟩ [.arrive, .arrive, .proceed] with
  | none => .error "valid barrier run rejected"
  | some (_, fin) =>
    if fin.released then pure () else .error "barrier not released after full arrival"
  match (barrier 2).run ⟨0, 2, false⟩ [.proceed] with
  | none => pure ()
  | some _ => .error "proceed before release accepted"

/-- The semaphore contract: acquire/release bounding. -/
def semChecks : CheckResult := do
  match (semaphore 2).run ⟨2, 2⟩ [.acquire, .acquire, .release, .acquire] with
  | none => .error "valid semaphore run rejected"
  | some _ => pure ()
  match (semaphore 1).run ⟨1, 1⟩ [.acquire, .acquire] with
  | none => pure ()
  | some _ => .error "acquire at zero permits accepted"
  match (semaphore 1).run ⟨1, 1⟩ [.release] with
  | none => pure ()
  | some _ => .error "release past capacity accepted"

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

end LinearTest

-- ── driver (TestKit) ────────────────────────────────────────────────────

def main : IO UInt32 :=
  TestKit.mainOfChecks "Machines" [
    ("dag-differential", dagDifferential),
    ("topo-smoke", topoSmoke),
    ("machine-trace", machineTrace),
    ("repr-op-smoke", reprOpSmoke),
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
    ("linear-machine", LinearTest.linearSmoke)
  ]


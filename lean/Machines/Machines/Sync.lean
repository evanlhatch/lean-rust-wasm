/-
# Machines.Sync — the asyncband primitives as machines

The general contracts of the sync primitives (notes/asyncbound.md's table),
each a `Machine` whose invariant IS the contract. The content is the legal-
event relation, not the scheduling — scheduling is the runtime's job; the
contract is what makes the runtime correct.

The primitives modeled (the subset flatland and sibling projects actually
use; the table's full surface grows on demand):

- **Latch** — one-way countdown (the epoch boundary). Contract: `count +
  arrived = cap` — a count-down past zero is impossible BY the invariant.
- **mpsc::bounded** — the delta channels. Contract: `buf.length ≤ cap`
  (capacity) + closed rejects sends (the no-drop-unless-closed discipline).
- **oneshot** — exactly-once signal (init/ready flags). Contract: send from
  empty only, recv from sent only.
- **Barrier** — all participants arrive before any proceeds (multi-world
  tick-all). Contract: two-phase, `arrived ≤ parties`, release only at full
  arrival.
- **Semaphore** — permit bounding (worker concurrency). Contract: `permits
  ≥ 0`, acquire only when available.

Deliberately NOT modeled: Mutex/RwLock/Condvar (flatland's sim is single-
threaded by design; the ownership wall means no shared mutable state), the
blocking bridge (a runtime concern), FairShare/singleflight (cold-path
coalescing — a scheduling policy, not a contract). These are the primitives
whose CONTRACT is load-bearing for the offload architecture.
-/

import Machines.Core

namespace Machines.Sync

open Machines

-- ═══ Latch ═══

/-- Latch state: remaining count + total arrivals. -/
structure LatchState where
  count : Nat
  arrived : Nat
deriving Repr, BEq

/-- Latch events. -/
inductive LatchEvent where
  | countDown
  | wait
deriving Repr, BEq

/-- The contract: `count + arrived = cap` — the sum is invariant, so a
    count-down past zero is impossible (the guard would need count = 0,
    which forces arrived = cap, which forces count + arrived = cap + 1). -/
def LatchInv (cap : Nat) (s : LatchState) : Prop :=
  s.count + s.arrived = cap

/-- The latch machine's event spec. -/
def latchSpec (cap : Nat) : LatchEvent → EventSpec LatchState (LatchInv cap)
  | .countDown =>
    { guard := fun s => decide (s.count > 0)
    , action := fun s _ => { s with count := s.count - 1, arrived := s.arrived + 1 }
    , safety := by
        intro s h hinv
        simp only [decide_eq_true_eq] at h
        unfold LatchInv at hinv ⊢
        simp only at hinv ⊢
        omega }
  | .wait =>
    { guard := fun s => decide (s.count = 0)
    , action := fun s _ => s
    , safety := by intro s h hinv; exact hinv }

/-- The latch machine. -/
@[reducible] def latch (cap : Nat) : Machine := {
  State := LatchState, Label := LatchEvent, Inv := LatchInv cap, event := latchSpec cap }

/-- count_down enabled iff incomplete. -/
theorem latch_countDown_enabled (cap : Nat) (s : LatchState) :
    (latch cap).enabled s .countDown = true ↔ s.count > 0 := by
  simp [Machine.enabled, latch, latchSpec]

/-- wait at count=0 is a no-op (the completed latch is stable). -/
theorem latch_wait_stable (cap : Nat) (s : LatchState) (h : s.count = 0) :
    (latch cap).step? s .wait = some s := by
  simp [Machine.step?, latch, latchSpec, h]

/-- count_down at count=0 is rejected (can't count past zero). -/
theorem latch_countDown_closed (cap : Nat) (s : LatchState) (h : s.count = 0) :
    (latch cap).step? s .countDown = none := by
  simp [Machine.step?, latch, latchSpec, h]

-- ═══ mpsc::bounded ═══

/-- Channel state: the buffer, capacity, closed flag. -/
structure MpscState (α : Type) where
  buf : List α
  cap : Nat
  closed : Bool
deriving Repr

/-- Channel events. -/
inductive MpscEvent (α : Type) where
  | send (v : α)
  | recv
  | close

/-- The contract: the buffer never exceeds capacity. (Closed-rejects-send is
    the guard's job; the invariant is the capacity bound.) -/
def MpscInv (s : MpscState α) : Prop := s.buf.length ≤ s.cap

/-- The mpsc machine's event spec. -/
def mpscSpec (α : Type) : MpscEvent α → EventSpec (MpscState α) MpscInv
  | .send v =>
    { guard := fun s => decide (s.buf.length < s.cap) && !s.closed
    , action := fun s _ => { s with buf := s.buf ++ [v] }
    , safety := by
        intro s h hinv
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
        obtain ⟨hlt, hcl⟩ := h
        unfold MpscInv at hinv ⊢
        simp only at hinv ⊢
        rw [List.length_append, List.length_singleton]
        omega }
  | .recv =>
    { guard := fun s => !s.buf.isEmpty
    , action := fun s _ => { s with buf := s.buf.tail }
    , safety := by
        intro s h hinv
        unfold MpscInv at hinv ⊢
        simp only at hinv ⊢
        have ht : s.buf.tail.length ≤ s.buf.length := by
          cases s.buf with
          | nil => simp
          | cons _ _ => simp
        omega }
  | .close =>
    { guard := fun _ => true
    , action := fun s _ => { s with closed := true }
    , safety := by intro s h hinv; exact hinv }

/-- The mpsc machine. -/
@[reducible] def mpsc (α : Type) : Machine := {
  State := MpscState α, Label := MpscEvent α, Inv := MpscInv, event := mpscSpec α }

/-- Send at full capacity is rejected (backpressure = rejection in the model;
    the runtime's blocking-wait is scheduling, not semantics). -/
theorem mpsc_send_full_rejected (α : Type) (s : MpscState α) (h : s.buf.length = s.cap) (v : α) :
    (mpsc α).step? s (.send v) = none := by
  simp [Machine.step?, mpsc, mpscSpec, h]

/-- A closed channel rejects sends. -/
theorem mpsc_closed_rejected (α : Type) (s : MpscState α) (h : s.closed = true) (v : α) :
    (mpsc α).step? s (.send v) = none := by
  simp [Machine.step?, mpsc, mpscSpec, h]

-- ═══ oneshot ═══

/-- Oneshot state: empty → sent → received. -/
inductive OneshotState (α : Type) where
  | empty | sent (v : α) | received (v : α)
deriving Repr

/-- Oneshot events. -/
inductive OneshotEvent (α : Type) where
  | send (v : α) | recv

/-- The oneshot machine's event spec (the contract is the state machine
    itself: send from empty only, recv from sent only). -/
def oneshotSpec (α : Type) : OneshotEvent α → EventSpec (OneshotState α) (fun _ => True)
  | .send v =>
    { guard := fun s => match s with | .empty => true | _ => false
    , action := fun s _ => match s with | .empty => .sent v | _ => s
    , safety := by intro s h _; trivial }
  | .recv =>
    { guard := fun s => match s with | .sent _ => true | _ => false
    , action := fun s _ => match s with | .sent v => .received v | _ => s
    , safety := by intro s h _; trivial }

/-- The oneshot machine. -/
@[reducible] def oneshot (α : Type) : Machine := {
  State := OneshotState α, Label := OneshotEvent α, Inv := fun _ => True, event := oneshotSpec α }

/-- Send fires exactly once (a second send is rejected). -/
theorem oneshot_send_once (α : Type) (v w : α) :
    (oneshot α).step? (.sent v) (.send w) = none := by
  simp [Machine.step?, oneshot, oneshotSpec]

/-- Recv before send is rejected. -/
theorem oneshot_recv_needs_sent (α : Type) :
    (oneshot α).step? (.empty (α := α)) .recv = none := by
  simp [Machine.step?, oneshot, oneshotSpec]

-- ═══ Barrier ═══

/-- Barrier state: arrivals toward the party count; released when full. -/
structure BarrierState where
  arrived : Nat
  parties : Nat
  released : Bool
deriving Repr, BEq

/-- Barrier events. -/
inductive BarrierEvent where
  | arrive
  | proceed
deriving Repr, BEq

/-- The contract: arrivals never exceed the party count; proceed only after
    release (full arrival). -/
def BarrierInv (s : BarrierState) : Prop :=
  s.arrived ≤ s.parties ∧ (s.released → s.arrived = s.parties)

/-- The barrier machine's event spec. -/
def barrierSpec : BarrierEvent → EventSpec BarrierState BarrierInv
  | .arrive =>
    { guard := fun s => decide (s.arrived < s.parties)
    , action := fun s _ =>
        let arrived' := s.arrived + 1
        { s with arrived := arrived', released := arrived' == s.parties }
    , safety := by
        intro s h hinv
        simp only [decide_eq_true_eq] at h
        unfold BarrierInv at hinv ⊢
        obtain ⟨hle, hrel⟩ := hinv
        constructor
        · -- (arrived+1) ≤ parties, from arrived < parties
          show s.arrived + 1 ≤ s.parties
          omega
        · intro hreleased
          -- released means arrived' == parties, i.e. arrived + 1 = parties
          show s.arrived + 1 = s.parties
          simp only [beq_iff_eq] at hreleased
          omega }
  | .proceed =>
    { guard := fun s => s.released
    , action := fun s _ => s
    , safety := by intro s h hinv; exact hinv }

/-- The barrier machine. -/
@[reducible] def barrier (parties : Nat) : Machine where
  State := BarrierState
  Label := BarrierEvent
  Inv := BarrierInv
  event := barrierSpec

/-- Arrive at full count is rejected (no over-arrival). -/
theorem barrier_arrive_full_rejected (s : BarrierState) (h : s.arrived = s.parties) :
    (barrier s.parties).step? s .arrive = none := by
  simp [Machine.step?, barrier, barrierSpec, h]

-- ═══ Semaphore ═══

/-- Semaphore state: available permits. -/
structure SemState where
  permits : Nat
  cap : Nat
deriving Repr, BEq

/-- Semaphore events. -/
inductive SemEvent where
  | acquire | release
deriving Repr, BEq

/-- The contract: permits never exceed capacity. -/
def SemInv (s : SemState) : Prop := s.permits ≤ s.cap

/-- The semaphore machine's event spec. -/
def semSpec : SemEvent → EventSpec SemState SemInv
  | .acquire =>
    { guard := fun s => decide (s.permits > 0)
    , action := fun s _ => { s with permits := s.permits - 1 }
    , safety := by
        intro s h hinv
        simp only [decide_eq_true_eq] at h
        unfold SemInv at hinv ⊢
        simp only at hinv ⊢
        omega }
  | .release =>
    { guard := fun s => decide (s.permits < s.cap)
    , action := fun s _ => { s with permits := s.permits + 1 }
    , safety := by
        intro s h hinv
        simp only [decide_eq_true_eq] at h
        unfold SemInv at hinv ⊢
        simp only at hinv ⊢
        omega }

/-- The semaphore machine. -/
@[reducible] def semaphore (cap : Nat) : Machine where
  State := SemState
  Label := SemEvent
  Inv := SemInv
  event := semSpec

/-- Acquire at zero permits is rejected. -/
theorem sem_acquire_empty_rejected (s : SemState) (h : s.permits = 0) :
    (semaphore s.cap).step? s .acquire = none := by
  simp [Machine.step?, semaphore, semSpec, h]

/-- Release at full capacity is rejected (permit conservation). -/
theorem sem_release_full_rejected (s : SemState) (h : s.permits = s.cap) :
    (semaphore s.cap).step? s .release = none := by
  simp [Machine.step?, semaphore, semSpec, h]

-- ═══ the liveness reading: blocking is bounded waiting ═══

/-- A blocked mpsc send (full buffer) becomes enabled after a recv — the
    progress property that makes backpressure live, not just safe. -/
theorem mpsc_blocked_send_unblocks (α : Type) (s : MpscState α) (v : α)
    (hfull : s.buf.length = s.cap) (hne : s.buf ≠ []) (hopen : s.closed = false) :
    ∃ s', (mpsc α).step? s .recv = some s' ∧
          (mpsc α).enabled s' (.send v) = true := by
  cases hbuf : s.buf with
  | nil => exact absurd hbuf hne
  | cons b bs =>
    refine ⟨{ buf := bs, cap := s.cap, closed := s.closed }, ?_, ?_⟩
    · simp [Machine.step?, mpsc, mpscSpec, hbuf]
    · simp [Machine.enabled, mpsc, mpscSpec, hopen]
      have : bs.length < s.cap := by
        have h1 : s.buf.length = bs.length + 1 := by rw [hbuf]; simp
        omega
      exact this

/-- A blocked semaphore acquire (no permits) becomes enabled after a
    release — bounded waiting. -/
theorem sem_blocked_acquire_unblocks (s : SemState)
    (hzero : s.permits = 0) (hroom : 0 < s.cap) :
    ∃ s', (semaphore s.cap).step? s .release = some s' ∧
          (semaphore s.cap).enabled s' .acquire = true := by
  refine ⟨{ s with permits := s.permits + 1 }, ?_, ?_⟩
  · simp [Machine.step?, semaphore, semSpec, hzero]
    omega
  · simp [Machine.enabled, semaphore, semSpec, hzero]

/-- A blocked latch wait (incomplete) becomes enabled after the final
    count_down — the epoch boundary's progress property. -/
theorem latch_blocked_wait_unblocks (cap : Nat) (s : LatchState)
    (hinv : LatchInv cap s) (hone : s.count = 1) :
    ∃ s', (latch cap).step? s .countDown = some s' ∧
          (latch cap).enabled s' .wait = true := by
  refine ⟨{ s with count := s.count - 1, arrived := s.arrived + 1 }, ?_, ?_⟩
  · simp [Machine.step?, latch, latchSpec, hone]
  · simp [Machine.enabled, latch, latchSpec, hone]

end Machines.Sync

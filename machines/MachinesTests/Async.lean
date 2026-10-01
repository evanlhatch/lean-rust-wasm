/-
# MachinesTests.Async — the asyncband models' pins + the mandatory controls

Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5). Suites (one per E5 family group):

1. `asyncband-mutex` — the battery's free reach (all three verdicts
   PROVED for the mutex), the Explore face pinned (`.both`'s
   unreachability as the PROVED verdict), the guard refusal pinned.
   Controls: the broken sibling (`mutexBad` — `lock2` fires from
   `held1`, REACHING `.both`) is REFUTED with the running tape witness
   (the laundering control denies it), and the fuel-0 budget gap is
   the honest UNKNOWN (never a verdict — the laundering control
   denies that too).
2. `asyncband-coordination` — the semaphore's bound + the waitgroup's
   release-⟺-zero law, batteries pinned. Controls: the unguarded
   release sibling (`semBad`) IS refuted with the witness count 3
   (the laundering control denies it), and the wait-at-one refusal
   (the underflow guard is load-bearing — `Nat` truncation would
   silently absorb it).
3. `asyncband-channels` — the oneshot's single-send, the mpsc's
   bounded backpressure + full-buffer refusal, the once-cell's
   no-re-init; batteries pinned over the finite payload universe.
   Controls: each refusal denied (the second send, the over-cap send,
   the re-init).
4. `asyncband-watch` — the coalescing law's value pins + the concrete
   schedule pair (the hyperproperty instantiated: same last send,
   different interleavings, same delivery). Controls: the hypothesis
   is load-bearing BOTH ways — "any send" (not the last) does NOT
   determine the delivery, and differing summaries deliver
   differently (the relation is not trivially satisfied).

Theorem citations: the census discipline — every `Machines.Async`
theorem is referenced here (the `example` block + the `#print axioms`
pins).

Axiom self-check: the pins below name the allowed axioms exactly
(the same discipline as MachinesTests.Axioms, kept in this lane's
own file).
-/

import Machines
import TestingKit.Spec
import TestingKit.Harness

open Machines Machines.Async Machines.Testing TestingKit

namespace MachinesTests.Async

/-! ## The mutex family -/

/-- The broken sibling (the negative control's substrate): `lock2`
    also fires from `held1` — landing on `.both`. The checker MUST
    catch it (a refutation with a running tape witness). -/
def mutexBad : Machine mutex.State mutex.Label := ⟨fun s i =>
  match s, i with
  | .held1, .lock2 => some .both
  | s, i => mutex.toMachine.step? s i⟩

/-- The broken sibling's Explore verdict: `.both` IS reached, by the
    tape `[lock1, lock2]` — REFUTED, the trichotomy's second face. -/
def mutexBadCheck : Machines.Verdict mutex.State mutex.Label :=
  Machines.check mutexBad (fun s => !decide (s = .both)) mutex.labels .free 4

def specAsyncMutex : Spec := Spec.ofList "asyncband-mutex"
  (fun _ => do
    -- the battery's free reach: all three checks PROVE for the mutex
    assert (mutex.battery .free 4 == [("deadlock-freedom", BatteryVerdict.proved),
        ("guard-coverage", BatteryVerdict.proved),
        ("invariant-non-vacuity", BatteryVerdict.proved)]) "battery wrong"
    -- the Explore face: `.both`'s unreachability as the PROVED verdict
    -- (the full label coverage premise — `mutex.labels` is complete
    -- by the generated proof)
    assert (mutexCheck == Machines.Verdict.proved) "explore verdict wrong"
    -- the guard face of the exclusion: lock2 cannot fire from held1
    assert (mutex.step? .held1 .lock2 == none) "lock2 fired from held1"
    -- the broken sibling's verdict IS the refutation, with the witness
    -- count as data (the trichotomy's second face)
    assert (match mutexBadCheck with | .refuted _ .both => true | _ => false)
      "broken mutex not refuted at .both")
  [ ("sabotage-exclusion-denied", fun _ =>
      -- the refutation LAUNDERED into a proof — the broken sibling
      -- would have to look clean
      assert (mutexBadCheck == Machines.Verdict.proved) "control"),
    ("sabotage-budget-laundered", fun _ =>
      -- the budget gap LAUNDERED into a verdict: fuel 0 explores
      -- nothing; the honest answer is `.unknown`, never a verdict
      assert (mutexCheck == Machines.Verdict.unknown
          Machines.ExploreReason.budgetExhausted) "control") ]
  1 60

/-! ## The coordination family: the semaphore + the waitgroup -/

def semInputs : List SemLabel := [.acquire, .release]

theorem semInputs_complete : ∀ i, i ∈ semInputs := by
  intro i; cases i <;> simp [semInputs]

def wgInputs : List WgLabel := [.add, .done, .wait]

theorem wgInputs_complete : ∀ i, i ∈ wgInputs := by
  intro i; cases i <;> simp [wgInputs]

/-- The broken sibling: release is UNGUARDED — the count rides past
    the cap. The checker MUST refute with the witness count 3. -/
def semBad : Machine Nat SemLabel := ⟨fun s i =>
  match i with
  | .release => some (s + 1)
  | .acquire => if s = 0 then none else some (s - 1)⟩

def semBadCheck : Machines.Verdict Nat SemLabel :=
  Machines.check semBad (fun s => decide (s ≤ 2)) semInputs 0 4

def specAsyncCoord : Spec := Spec.ofList "asyncband-coordination"
  (fun _ => do
    -- the semaphore: deadlock-freedom + guard-coverage + non-vacuity
    -- over the enumerated counter range (3 violates the bound)
    assert (deadlockFree sem semInputs 0 4 semInputs_complete
        == BatteryVerdict.proved) "sem deadlock wrong"
    assert (guardCoverage sem semInputs [0, 1, 2, 3] semInputs_complete
        == BatteryVerdict.proved) "sem coverage wrong"
    assert (invariantNonVacuous sem [0, 1, 2, 3]
        == BatteryVerdict.proved) "sem vacuity wrong"
    -- the waitgroup: the two live checks (the `True` invariant skips
    -- the non-vacuity check, per Testing.lean's own note). The add
    -- event is an unbounded walk (no upper guard), so the reachable
    -- fragment never stabilizes within any budget — the deadlock sweep
    -- answers the honest `.unknown` (the mGhost precedent; the wedge
    -- is impossible — add is ALWAYS enabled — but the sweep cannot
    -- cover the fragment, and it says so)
    assert (deadlockFree wg wgInputs 0 4 wgInputs_complete
        == BatteryVerdict.unknown Machines.ExploreReason.budgetExhausted)
      "wg deadlock wrong"
    assert (guardCoverage wg wgInputs [0, 1, 2, 3] wgInputs_complete
        == BatteryVerdict.proved) "wg coverage wrong"
    -- the release-⟺-zero law at the data level
    assert (wg.step? 0 .wait == some 0) "wait at zero blocked"
    assert (wg.step? 1 .wait == none) "wait at one proceeded"
    -- the broken sibling IS refuted, with the witness count as data
    assert (match semBadCheck with | .refuted _ 3 => true | _ => false)
      "broken semaphore not refuted at 3")
  [ ("sabotage-bound-laundered", fun _ =>
      -- the refutation LAUNDERED into a proof: the unguarded release
      -- would have to look clean
      assert (semBadCheck == Machines.Verdict.proved) "control"),
    ("sabotage-wait-at-one", fun _ =>
      -- the underflow guard denied: wait must NOT complete at one
      assert (wg.step? 1 .wait == some 1) "control") ]
  1 61

/-! ## The channel families: oneshot + mpsc + once-cell -/

def onceInputs : List OnceLabel := [.get, .init .a, .init .b]

theorem onceInputs_complete : ∀ i, i ∈ onceInputs := by
  intro i
  cases i with
  | get => simp [onceInputs]
  | init v => cases v <;> simp [onceInputs]

def specAsyncChan : Spec := Spec.ofList "asyncband-channels"
  (fun _ => do
    -- the oneshot's single-send + empty-recv refusals (the guard-level
    -- laws, pinned at data)
    assert (oneshot.step? (some 5) (.send 3) == none) "second send fired"
    assert (oneshot.step? none (.recv (α := Nat)) == none) "empty recv fired"
    -- the mpsc: the battery's free reach over the finite payload
    -- universe (the over-cap buffer [.a,.b,.c] gives non-vacuity)
    assert (deadlockFree mpsc mpscInputs [] 4 mpscInputs_complete
        == BatteryVerdict.proved) "mpsc deadlock wrong"
    assert (guardCoverage mpsc mpscInputs [[], [.a], [.a, .b], [.a, .b, .a]]
        mpscInputs_complete == BatteryVerdict.proved) "mpsc coverage wrong"
    assert (invariantNonVacuous mpsc [[], [.a], [.a, .b], [.a, .b, .a]]
        == BatteryVerdict.proved) "mpsc vacuity wrong"
    -- the full-buffer refusal (the backpressure's face)
    assert (mpsc.step? [.a, .b] (.send .a) == none) "over-cap send fired"
    -- the once-cell: the two live checks + the no-re-init refusal
    assert (deadlockFree onceCell onceInputs none 4 onceInputs_complete
        == BatteryVerdict.proved) "once deadlock wrong"
    assert (guardCoverage onceCell onceInputs [none, some .a]
        onceInputs_complete == BatteryVerdict.proved) "once coverage wrong"
    assert (onceCell.step? (some .a) (.init .b) == none) "re-init fired")
  [ ("sabotage-single-send-denied", fun _ =>
      -- the second send MUST be refused
      assert (oneshot.step? (some 5) (.send 3) == some (some 3)) "control"),
    ("sabotage-backpressure-denied", fun _ =>
      -- the over-cap send MUST be refused
      assert (mpsc.step? [.a, .b] (.send .a) == some [.a, .b, .a]) "control"),
    ("sabotage-once-denied", fun _ =>
      -- the re-init MUST be refused
      assert (onceCell.step? (some .a) (.init .b) == some (some .b)) "control") ]
  1 62

/-! ## The watch family: the coalescing + the hyperproperty -/

def specAsyncWatch : Spec := Spec.ofList "asyncband-watch"
  (fun _ => do
    -- the coalescing: the delivered value is the LAST send
    assert (watchRun [.send 7, .send 9, .recv, .send 3, .recv] == some 3)
      "coalescing wrong"
    -- the hold face: recv at `none` waits (the totaled semantics)
    assert (watchRun [.recv, .recv] == none) "hold wrong"
    -- THE SCHEDULE PAIR (the hyperproperty instantiated): the same
    -- last send (1), different recv interleavings — the same delivery
    assert (watchRun [.send 2, .send 1, .recv]
        == watchRun [.send 2, .recv, .send 1, .recv]) "schedule pair wrong")
  [ ("sabotage-any-send-blind", fun _ =>
      -- the claim is about the LAST send, not ANY send: these two
      -- tapes differ in delivery (1-then-2 vs 2-then-1, no recv
      -- between)
      assert (watchRun [.send 1, .send 2, .recv]
        == watchRun [.send 2, .send 1, .recv]) "control"),
    ("sabotage-summary-blind", fun _ =>
      -- the hypothesis is load-bearing the other way: DIFFERING
      -- summaries must deliver differently (the relation is not
      -- trivially satisfied)
      assert (watchRun [.send 1, .recv] == watchRun [.send 2, .recv])
        "control") ]
  1 63

/-! ## The theorem citations (the census discipline) -/

example : ∀ (s : mutex.State) (i : mutex.Label),
    mutex.toMachine.step? s i = some .both → False := mutex_step_not_both
example : ∀ (s : mutex.State), mutex.toMachine.Reachable .free s → s ≠ .both :=
  mutex_excl
example : ∀ (s : Nat), sem.toMachine.Reachable 0 s → s ≤ 2 := sem_bound
example : ∀ (n : Nat), wg.enabled n .wait = true ↔ n = 0 := wg_wait_iff_zero
example : wg.step? 0 .done = none := wg_done_refused_at_zero
example : ∀ (v u : Nat), oneshot.step? (some v) (.send u) = none :=
  oneshot_send_full_refused
example : oneshot.step? (none : Option Nat) (.recv (α := Nat)) = none :=
  oneshot_recv_empty_refused 0
example : ∀ (s : List Pay), mpsc.toMachine.Reachable [] s → s.length ≤ 2 :=
  mpsc_bounded
example : ∀ (s : List Pay) (p : Pay), s.length = 2 →
    mpsc.step? s (.send p) = none := mpsc_full_blocks_send
example : ∀ (v u : Pay), onceCell.step? (some v) (.init u) = none :=
  once_init_refused_after
example : onceCell.step? none .get = none := once_get_refused_before
example : ∀ (t : List OnceLabel) {s : Option Pay},
    onceCell.toMachine.run (some Pay.a) t = some s → s.isSome = true :=
  once_persists Pay.a
example : ∀ (s : List (Fin 2)), pool.toMachine.Reachable [] s → s.Nodup :=
  pool_state_ok
example : ∀ (s : List (Fin 2)), h0 ∈ s →
    pool.toMachine.step? s .acquire0 = none := pool_no_double_checkout
example : ∀ (s : List (Fin 2)), h1 ∈ s →
    pool.toMachine.step? s .acquire1 = none := pool_acquire1_refused
example : ∀ (t : List PoolLabel) (s : List (Fin 2)),
    pool.toMachine.run [] t = some s → h0 ∈ s →
    pool.toMachine.run s [.acquire0, .acquire0] = none :=
  pool_no_double_checkout_run
example : sendOf (.send 3 : WatchLabel) = some 3 := rfl
example : ∀ (t : List WatchLabel) (init : Option Nat),
    ∃ s, watch.toMachine.run init t = some s := watch_run_total
example : ∀ (t : List WatchLabel) (init s : Option Nat),
    watch.toMachine.run init t = some s →
    s = (lastSend? t).orElse (fun _ => init) := watch_run_last
example : ∀ t : List WatchLabel, watchRun t = lastSend? t := watch_factor
example : Kit.Noninterfering watchRun (Kit.agreeOn lastSend?)
    (Kit.agreeOn id) := watch_schedule_independent

/-! ## The axiom self-check -/

/-- info: 'Machines.Async.mutex_excl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Async.mutex_excl

/-- info: 'Machines.Async.watch_schedule_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Async.watch_schedule_independent

end MachinesTests.Async

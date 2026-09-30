/-
# Machines.Async — the asyncband models (E5)

The machine models of the asyncband primitive FAMILIES (E5's honest
subset, landed deeply rather than all thinly). Each family is a
`MachineWithInv` (Events.lean) over its states + labels, with the
safety invariant PROVED — never asserted — and the conformance
battery's free reach (16 §5.7: deadlock-freedom + guard-coverage +
non-vacuity verdicts by construction) exercised per machine.

## The families landed

- **locks — Mutex**: the `machine!` macro's clause grammar FITS here
  (finite enumerated state space, payload-free labels) — the four
  states include the violation `.both`, the invariant EXCLUDES it, and
  mutual exclusion is a THEOREM: no step lands on `.both`
  (`mutex_step_not_both`), so no reachable state holds it
  (`mutex_excl`). The Explore trichotomy's faces all fire on this
  family (the tests pin PROVED / REFUTED-with-witness / UNKNOWN).
- **coordination — Semaphore, WaitGroup**: hand-built with a reason
  (the m3i precedent): the counter is a `Nat`, outside `machine!`'s
  enumerated states. The semaphore's bound is
  `reachable_preserves`'s INSTANCE (`sem_bound`) — the guards
  discharge the safety POs, the framework law lifts them to every
  reachable state. The waitgroup's content is the guard structure
  (done requires arrival; wait requires zero — `wg_wait_iff_zero`).
- **coalescing — OnceCell**: hand-built (payload labels). The once law
  is initialization MONOTONICITY: from an initialized state, every
  successful run ends initialized (`once_persists`) — a re-init
  cannot fire.
- **channels — oneshot, mpsc, watch**: hand-built (payload labels —
  the Dsl exclusion's first consumer moment). The oneshot's
  single-send law is guard-level (a send is refused in EVERY full
  state — stronger than the reachable reading). The mpsc's bounded
  backpressure is the buffer invariant as a theorem (`mpsc_bounded`)
  + the full-buffer refusal (`mpsc_full_blocks_send`). The watch's
  coalescing is the LATEST-STATE semantics: the receiver's delivered
  value is the last send (`watch_factor`) — whence the
  schedule-independence claim below.
- **pool**: the effects' resource discipline's instance at the machine
  face (D7): the state is the checked-out set with the nodup+universe
  invariant (`pool_state_ok` — Effects.Resource's split shape, CITED
  in prose, never imported — the cone stays Machines'); the
  no-double-checkout law is the guard refusal
  (`pool_no_double_checkout`, `pool_no_double_checkout_run`) — exactly
  the accounting the effect row cannot express
  (`Effects.row_blind_to_double_spend`'s machine face).

## The schedule-independence claim (the Kit.Hyper trigger — FIRED)

`watch_schedule_independent`: two watch executions agreeing on the
coalesced summary (the LAST send) deliver the same value — whatever
the interleaving of the recvs and the superseded sends. The claim is a
genuine hyperproperty: the quantified object is the EXECUTION PAIR
(`Kit.Noninterfering`'s two-run carrier), not a single execution — a
one-run invariant cannot state it. It rides Kit.Hyper's flagship type
(`Noninterfering`, `agreeOn`, `noninterfering_of_factor`) — NO new
machinery; the 07 parked-table trigger fires (Hyper's first consumer;
the header + the row are updated in this landing). The hypothesis is
load-bearing (the tests pin the differing-summary witness), and the
mpsc's FIFO is honestly NOT schedule-independent in this sense (the
delivery order IS the send order — a named exclusion below).

## The conformance seam (the NAMED next step)

The Rust-side duel — model executions ≡ asyncband behavior — is NOT
this item: the asyncband crate is not a dependency yet. The duel lands
when it is; the models + the invariants are THIS item's content. The
duel's shape is already fixed by 15-patterns #1 (the tested-agreement
tier over the model's `step?` vs the crate's observed behavior).

## The five questions (notes/v3/01-core.md)

- **Root**: TraceModel (01-core §3) — each family's behavior is the
  SET of its executions over the authoritative `step?`; choice lives
  in the input tape (the payload labels ARE the tape's vocabulary).
- **Carrier grade**: pattern #1 — the EventSpec family is the spec
  reading, the derived `step?` the checker, `step_iff`/`toMachine` the
  ties; every invariant is `reachable_preserves`'s instance or a
  guard-level theorem, never a parallel proof.
- **Spine reading**: none — a substrate; the duel + the surface words
  instantiate it.
- **Ladder rung**: the guard-level laws are rung-3 decides at the call
  sites; the run-level theorems (`once_persists`, `watch_run_last`,
  `watch_factor`) are small hand inductions (rung 6); the
  schedule-independence claim is a CITATION
  (`noninterfering_of_factor`).
- **Gate rows**: the axiom report pins in MachinesTests.Async (every
  theorem cited there); the battery + Explore verdicts are the
  runtime pins.

## Named exclusions (each lands with its consumer)

- **RwLock/Condvar**: the counted-readers + wait-queue state needs the
  sampled battery (payload labels); lands with the first consumer that
  needs them (the blocking adapter's).
- **Barrier/Phaser/Latch/Shutdown**: the barrier's release-⟺-all-
  arrived is the wg law's shape (`wg_wait_iff_zero`); the phaser's
  phase arithmetic lands with a consumer.
- **Once/OnceMap/LazyCell/singleflight**: singleflight is 02 §3's
  determinacy shape — lands with the determinacy lane's consumer;
  OnceMap with the table lane's.
- **mpmc/spmc/broadcast**: the multi-consumer receivers need the
  sampled battery + the per-receiver cursors; the FIFO delivery-order
  claim (the mpsc's) is honestly order-DEPENDENT — it is a session
  discipline (Machines.Session), not a hyperproperty.
- **Completion, the blocking adapter**: the duel's seam (above).
- NO fairness, NO POR, NO vector clocks (08 §10's standing guard).

Core-only: no mathlib, no Batteries (the cone rule). Imports
Machines.Dsl (the battery registration + the entourage) + Kit.Hyper
(the schedule-independence carrier — the fired trigger).
-/

import Machines.Dsl
import Kit.Hyper

namespace Machines.Async

/-! ## The payload universe (the Session.Pay precedent)

The channels' payload labels need a finite universe for the battery's
completeness premise — a two-value universe, the session lane's
discipline. -/

/-- The finite payload universe for the battery-complete channels. -/
inductive Pay where
  | a | b
deriving DecidableEq, Repr, BEq

open Pay

/-! ## Family 1 — the Mutex (the `machine!` clause grammar fits) -/

/- THE mutex: four states — the violation `.both` is IN the enum and
EXCLUDED by the invariant (non-vacuity has something to exclude), and
no step lands there (the theorems below). (A block comment: `machine!`
is a custom command — it carries no docstring, the wheel/lamp
precedent.) -/
machine! mutex where
  states: [free, held1, held2, both]
  Inv: fun s => s ≠ .both
  event: lock1   guard: (fun s => s = .free)   action: (fun _ _ => .held1)
  event: lock2   guard: (fun s => s = .free)   action: (fun _ _ => .held2)
  event: unlock1 guard: (fun s => s = .held1)  action: (fun _ _ => .free)
  event: unlock2 guard: (fun s => s = .held2)  action: (fun _ _ => .free)

/-- No transition lands on `.both` — the violation is not merely
    unreachable, it is UNSTEPPABLE-TO (the stronger, honest shape). -/
theorem mutex_step_not_both (s : mutex.State) (i : mutex.Label)
    (h : mutex.toMachine.step? s i = some .both) : False := by
  cases s <;> cases i <;>
    simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, mutex.spec] at h

/-- THE mutual-exclusion invariant: no reachable state holds both
    threads. `reachable_preserves`'s sibling — proved directly over the
    reachable view (the invariant's exclusion is the point). -/
theorem mutex_excl (s : mutex.State) (h : mutex.toMachine.Reachable .free s) :
    s ≠ .both := by
  induction h with
  | here => intro hc; cases hc
  | step i hs _ _ =>
      intro hc
      apply mutex_step_not_both _ i
      rw [← hc]
      exact hs

/-- The Explore face: `.both`'s unreachability as the trichotomy's
    PROVED verdict (full label coverage — `mutexLabels` is complete by
    the generated proof). The tests pin the REFUTED and UNKNOWN faces
    on the broken sibling. -/
def mutexCheck : Machines.Verdict mutex.State mutex.Label :=
  Machines.check mutex.toMachine (fun s => !decide (s = .both)) mutexLabels .free 4

/-! ## Family 2 — the Semaphore (hand-built: the Nat counter) -/

/-- The semaphore's labels: acquire (down) + release (up). -/
inductive SemLabel where
  | acquire | release
deriving DecidableEq, Repr, BEq

/-- THE semaphore: the permit count, cap 2. The invariant (count ≤ cap)
    is discharged per-step by the guards (the safety POs) and lifted to
    every reachable state by the framework law (`sem_bound`). Hand-
    built with a reason (the m3i precedent): the state is a `Nat`,
    outside `machine!`'s enumerated states. -/
def sem : MachineWithInv Nat SemLabel where
  inv := fun n => n ≤ 2
  event := fun l => match l with
    | .acquire =>
        { guard := fun n => decide (0 < n)
        , action := fun n _ => n - 1
        , safety := by intro n _ hn; show n - 1 ≤ 2; omega }
    | .release =>
        { guard := fun n => decide (n < 2)
        , action := fun n _ => n + 1
        , safety := by
            intro n h hn
            have h' : n < 2 := decide_eq_true_eq.mp h
            show n + 1 ≤ 2
            omega }

instance : DecidablePred sem.inv := fun n => inferInstanceAs (Decidable (n ≤ 2))

/-- THE semaphore's bound: every reachable count is within the cap —
    the guards discharge the per-step POs, `reachable_preserves` lifts
    them (the framework law CITED, never re-proved). -/
theorem sem_bound (s : Nat) (h : sem.toMachine.Reachable 0 s) : s ≤ 2 :=
  sem.reachable_preserves 0 (by omega) h

/-! ## Family 3 — the WaitGroup (hand-built: the Nat counter) -/

/-- The waitgroup's labels: add (arrive), done (leave), wait (block
    until zero). -/
inductive WgLabel where
  | add | done | wait
deriving DecidableEq, Repr, BEq

/-- THE waitgroup: the arrival counter. Hand-built with a reason (the
    m3i precedent) AND with an honestly-`True` invariant: the content
    is the GUARD structure — done requires arrival, wait requires
    zero — so the battery's non-vacuity check is SKIPPED per
    Testing.lean's own note (call the two live checks directly). -/
def wg : MachineWithInv Nat WgLabel where
  inv := fun _ => True
  event := fun l => match l with
    | .add =>
        { guard := fun _ => true
        , action := fun n _ => n + 1
        , safety := by intros; trivial }
    | .done =>
        { guard := fun n => decide (0 < n)
        , action := fun n _ => n - 1
        , safety := by intros; trivial }
    | .wait =>
        { guard := fun n => decide (n = 0)
        , action := fun n _ => n
        , safety := by intros; trivial }

/-- THE waitgroup's release condition: a wait completes ⟺ the counter
    is zero (the barrier's release-⟺-all-arrived law's wg face). -/
theorem wg_wait_iff_zero (n : Nat) :
    wg.enabled n .wait = true ↔ n = 0 := by
  simp [MachineWithInv.enabled, wg]

/-- The done-guard's teeth: `done` is refused at zero — the departure
    cannot precede the arrival (the underflow is the guard's, not the
    type's: `Nat` truncation would silently absorb it). -/
theorem wg_done_refused_at_zero : wg.step? 0 .done = none := by
  simp [MachineWithInv.step?_eq, wg]

/-! ## Family 4 — the oneshot channel (hand-built: payload labels) -/

/-- The oneshot is GENERIC in the payload type `α` (the theorems hold
    for every payload; the tests instantiate `Nat`). -/
variable {α : Type}

/-- The oneshot's labels: `send v` (payload — the Dsl exclusion's
    first consumer moment) or `recv`. -/
inductive OneLabel (α : Type) where
  | recv | send (v : α)
deriving DecidableEq, Repr, BEq

/-- THE oneshot: `none` = empty, `some v` = full. The invariant is
    honestly `True` (the content is the guard structure); the battery
    is NOT run on this machine — the payload labels have no complete
    finite enumeration (Testing.lean's named exclusion; the sampled
    battery lands with its consumer). -/
def oneshot : MachineWithInv (Option α) (OneLabel α) where
  inv := fun _ => True
  event := fun l => match l with
    | .recv =>
        { guard := fun s => s.isSome
        , action := fun _ _ => none
        , safety := by intros; trivial }
    | .send v =>
        { guard := fun s => s.isNone
        , action := fun _ _ => some v
        , safety := by intros; trivial }

/-- THE single-send law: a send is refused in EVERY full state — the
    second send cannot fire. Guard-level, hence STRONGER than the
    reachable reading (no state at all admits it). -/
theorem oneshot_send_full_refused (v u : α) :
    oneshot.step? (some v) (.send u) = none := by
  simp [MachineWithInv.step?_eq, oneshot]

/-- The receive-side refusal: an empty oneshot delivers nothing — the
    recv is disabled, not a silent value. -/
theorem oneshot_recv_empty_refused (u : α) :
    oneshot.step? none (.recv (α := α)) = none := by
  simp [MachineWithInv.step?_eq, oneshot]

-- note: `u` is the recv's (absent) payload witness — the recv label
-- carries no payload; the binder documents the empty state's refusal

/-! ## Family 5 — the mpsc channel (hand-built: bounded FIFO) -/

/-- The mpsc's labels: `send p` (payload from the universe) or `recv`. -/
inductive MpscLabel where
  | recv | send (p : Pay)
deriving DecidableEq, Repr, BEq

/-- THE bounded mpsc: the buffer, cap 2, FIFO (send appends, recv
    drops the head). The invariant (length ≤ cap) IS the bounded
    backpressure — discharged per-step by the send guard, lifted to
    every reachable state by the framework law (`mpsc_bounded`). -/
def mpsc : MachineWithInv (List Pay) MpscLabel where
  inv := fun s => s.length ≤ 2
  event := fun l => match l with
    | .send p =>
        { guard := fun s => decide (s.length < 2)
        , action := fun s _ => s ++ [p]
        , safety := by
            intro s h hs
            have h2 : (s ++ [p]).length = s.length + 1 := by simp
            have h3 : s.length < 2 := decide_eq_true_eq.mp h
            omega }
    | .recv =>
        { guard := fun s => decide (s ≠ [])
        , action := fun s _ => s.tail
        , safety := by
            intro s h hs
            have h2 : s.tail.length = s.length - 1 := List.length_tail s
            omega }

instance : DecidablePred mpsc.inv := fun s =>
  inferInstanceAs (Decidable (s.length ≤ 2))

/-- The battery-complete label enumeration (the finite payload
    universe makes this possible). -/
def mpscInputs : List MpscLabel := [.recv, .send .a, .send .b]

theorem mpscInputs_complete : ∀ i, i ∈ mpscInputs := by
  intro i; cases i <;> simp [mpscInputs]

/-- THE bounded-backpressure law: every reachable buffer is within the
    cap — `reachable_preserves`'s instance (the framework law CITED). -/
theorem mpsc_bounded (s : List Pay) (h : mpsc.toMachine.Reachable [] s) :
    s.length ≤ 2 :=
  mpsc.reachable_preserves [] (by simp) h

/-- The backpressure's refusal face: a full buffer blocks the send. -/
theorem mpsc_full_blocks_send (s : List Pay) (p : Pay) (h : s.length = 2) :
    mpsc.step? s (.send p) = none := by
  simp [MachineWithInv.step?_eq, mpsc, h]

/-! ## Family 6 — the OnceCell (hand-built: payload labels) -/

/-- The once-cell's labels: `get` or `init v`. -/
inductive OnceLabel where
  | get | init (v : Pay)
deriving DecidableEq, Repr, BEq

/-- THE once-cell: `none` = uninitialized, `some v` = initialized.
    The invariant is honestly `True` (the content is the guard
    structure + the monotonicity theorem below); the battery runs the
    two live checks only (the non-vacuity skip, documented above). -/
def onceCell : MachineWithInv (Option Pay) OnceLabel where
  inv := fun _ => True
  event := fun l => match l with
    | .get =>
        { guard := fun s => s.isSome
        , action := fun s _ => s
        , safety := by intros; trivial }
    | .init v =>
        { guard := fun s => s.isNone
        , action := fun _ _ => some v
        , safety := by intros; trivial }

/-- THE once law, refusal face: initialization is refused in every
    initialized state — no re-init. -/
theorem once_init_refused_after (v u : Pay) :
    onceCell.step? (some v) (.init u) = none := by
  simp [MachineWithInv.step?_eq, onceCell]

/-- The get-side refusal: an uninitialized cell has nothing to get. -/
theorem once_get_refused_before : onceCell.step? none .get = none := by
  simp [MachineWithInv.step?_eq, onceCell]

/-- THE once law, run face: from an initialized state, every
    successful run ends initialized — initialization is MONOTONE
    (a re-init cannot fire mid-run; the run would fail instead). -/
theorem once_persists (v : Pay) :
    ∀ (t : List OnceLabel) {s : Option Pay},
      onceCell.toMachine.run (some v) t = some s → s.isSome = true := by
  intro t
  induction t with
  | nil => intro s h; rw [Machine.run_nil] at h; simp at h; simp [h]
  | cons i rest ih =>
      intro s h
      rw [Machine.run_cons, Option.bind_eq_some_iff] at h
      obtain ⟨s₀, hstep, hrun⟩ := h
      have hinv : s₀.isSome = true := by
        cases i with
        | get =>
            have : s₀ = some v := by
              simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, onceCell] at hstep
              exact Option.some.inj hstep
            simp [this]
        | init u =>
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, onceCell] at hstep
      exact ih hinv hrun

/-! ## Family 7 — the Pool (the effects' resource discipline's instance) -/

/-- The pool's labels: `acquire h` (checkout) or `release h` (return). -/
inductive PoolLabel where
  | acquire (h : Nat) | release (h : Nat)
deriving DecidableEq, Repr, BEq

/-- THE pool: the state is the CHECKED-OUT set (a list with the
    nodup+universe invariant — Effects.Resource's split shape at the
    machine face: the checkout = the live handle, the release = the
    split; D7's discipline CITED in prose, never imported — the cone
    stays Machines'). `acquire` refuses an already-checked-out handle;
    the invariant makes the accounting the effect row cannot express
    (`Effects.row_blind_to_double_spend`'s machine face). -/
def pool : MachineWithInv (List Nat) PoolLabel where
  inv := fun s => s.Nodup ∧ s.all (fun h => decide (h < 2)) = true
  event := fun l => match l with
    | .acquire h =>
        { guard := fun s => decide (h ∉ s ∧ h < 2)
        , action := fun s _ => h :: s
        , safety := by
            intro s hg hs
            simp only [decide_eq_true_eq] at hg
            exact ⟨List.nodup_cons.mpr ⟨hg.1, hs.1⟩,
              by simp [List.all_cons, hg.2, hs.2]⟩ }
    | .release h =>
        { guard := fun s => decide (h ∈ s)
        , action := fun s _ => s.erase h
        , safety := by
            intro s hg hs
            exact ⟨hs.1.erase h,
              List.all_eq_true.mpr fun x hx =>
                hs.2 x (List.mem_of_mem_erase hx)⟩ }

instance : DecidablePred pool.inv := fun s =>
  inferInstanceAs (Decidable (s.Nodup ∧ s.all (fun h => decide (h < 2)) = true))

/-- The pool's battery-complete label enumeration. -/
def poolInputs : List PoolLabel :=
  [.acquire 0, .acquire 1, .release 0, .release 1]

theorem poolInputs_complete : ∀ i, i ∈ poolInputs := by
  intro i; cases i <;> simp [poolInputs]

/-- THE pool's state discipline: every reachable checked-out set is
    duplicate-free AND within the handle universe —
    `reachable_preserves`'s instance (the framework law CITED). The
    nodup half is the resource discipline's content; the universe half
    is what makes the release guard sound. -/
theorem pool_state_ok (s : List Nat) (h : pool.toMachine.Reachable [] s) :
    s.Nodup ∧ ∀ h, h ∈ s → h < 2 := by
  have hin := pool.reachable_preserves [] ⟨List.Nodup.nil, by simp⟩ h
  exact ⟨hin.1, fun h hm => decide_eq_true_eq.mp (List.all_eq_true.mp hin.2 h hm)⟩

/-- THE no-double-checkout law: with `h` checked out, a second acquire
    of `h` is refused — the guard IS the accounting (the effect row's
    blindness, repaired at the machine face). -/
theorem pool_no_double_checkout (s : List Nat) (h : Nat) (hm : h ∈ s) :
    pool.toMachine.step? s (.acquire h) = none := by
  simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, pool, hm]

/-- The run face: no successful run checks out the same handle twice
    in a row — the second acquire cannot fire, so the run FAILS
    (the refusal is observable, never silent). -/
theorem pool_no_double_checkout_run (t : List PoolLabel) (s : List Nat)
    (hr : pool.toMachine.run [] t = some s) (hm : h ∈ s) :
    pool.toMachine.run s [.acquire h, .acquire h] = none := by
  rw [Machine.run_cons, pool_no_double_checkout s h hm]
  simp

/-! ## Family 8 — the watch channel (the coalescing + the Hyper claim) -/

/-- The watch's labels: `send v` (never blocks, OVERWRITES) or `recv`
    (never consumes, never blocks: at `none` it HOLDS — the Fusion
    totalized reading, blocked = hold; every run succeeds). -/
inductive WatchLabel where
  | recv | send (v : Nat)
deriving DecidableEq, Repr, BEq

/-- THE watch channel: the coalescing semantics — the state IS the
    latest value; a send overwrites; a recv observes without
    consuming. The invariant is honestly `True` (the content is the
    coalescing law `watch_factor` + the hyperproperty below). -/
def watch : MachineWithInv (Option Nat) WatchLabel where
  inv := fun _ => True
  event := fun l => match l with
    | .send v =>
        { guard := fun _ => true
        , action := fun _ _ => some v
        , safety := by intros; trivial }
    | .recv =>
        { guard := fun _ => true
        , action := fun s _ => s
        , safety := by intros; trivial }

/-- The schedule-free summary of a watch execution: the LAST send's
    payload (the coalesced value). Two schedules agreeing here agree
    on everything the receiver can see. -/
def sendOf : WatchLabel → Option Nat
  | .send v => some v
  | .recv => none

/-- The last send in a tape (`none` if there is none) — the
    schedule-free summary. -/
def lastSend? : List WatchLabel → Option Nat
  | [] => none
  | .send v :: t => (lastSend? t).orElse (fun _ => some v)
  | .recv :: t => lastSend? t

/-- Every watch run succeeds (both guards are total: sends overwrite,
    recvs hold) — the totaled semantics' premise. -/
theorem watch_run_total : ∀ (t : List WatchLabel) (init : Option Nat),
    ∃ s, watch.toMachine.run init t = some s := by
  intro t
  induction t with
  | nil => intro _; exact ⟨_, rfl⟩
  | cons i rest ih =>
      intro init
      obtain ⟨s, hs⟩ := ih init
      refine ⟨s, ?_⟩
      cases i with
      | recv =>
          have hstep : watch.toMachine.step? init .recv = some init := by
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, watch]
          rw [Machine.run_cons, hstep, Option.bind_some]
          exact hs
      | send v =>
          have hstep : watch.toMachine.step? init (.send v) = some (some v) := by
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, watch]
          rw [Machine.run_cons, hstep, Option.bind_some]
          exact hs

/-- THE COALESCING LAW: the state a watch run ends in is exactly the
    last send (or the initial state when nothing was sent) — the
    arrival order of superseded sends and the interleaving of recvs
    are INVISIBLE in the outcome. -/
theorem watch_run_last : ∀ (t : List WatchLabel) (init s : Option Nat),
    watch.toMachine.run init t = some s →
    s = (lastSend? t).orElse (fun _ => init) := by
  intro t
  induction t with
  | nil =>
      intro init s h
      rw [Machine.run_nil] at h
      simp at h
      simp [h]
  | cons i rest ih =>
      intro init s h
      rw [Machine.run_cons, Option.bind_eq_some_iff] at h
      obtain ⟨s₀, hstep, hrun⟩ := h
      cases i with
      | recv =>
          have hs₀ : s₀ = init := by
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, watch] at hstep
            exact Option.some.inj hstep
          rw [ih s₀ s hrun, hs₀, lastSend?]
      | send v =>
          have hs₀ : s₀ = some v := by
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, watch] at hstep
            exact Option.some.inj hstep
          rw [ih s₀ s hrun, hs₀, lastSend?]
          cases hl : lastSend? rest <;> simp [hl]

/-- The delivered value: the totaled run from the empty cell (every
    run succeeds — `watch_run_total`). -/
def watchRun (t : List WatchLabel) : Option Nat :=
  (watch.toMachine.run none t).getD none

/-- The coalescing law at the delivered-value face (the factor the
    hyperproperty cites): the delivered value IS the last send (or
    `none`). -/
theorem watch_factor (t : List WatchLabel) :
    watchRun t = (lastSend? t).orElse (fun _ => none) := by
  obtain ⟨s, hs⟩ := watch_run_total t none
  rw [watchRun, hs]
  exact watch_run_last t none s hs

/-- THE SCHEDULE-INDEPENDENCE CLAIM (E5's hook; 07's Kit.Hyper trigger,
    FIRED): two watch executions agreeing on the coalesced summary —
    the last send — deliver the same value, WHATEVER the interleaving
    of the recvs and the superseded sends. A genuine hyperproperty: the
    quantified object is the EXECUTION PAIR (`Noninterfering`'s two-run
    carrier), not a single execution — a one-run invariant cannot
    state it. Rides Kit.Hyper's flagship type; the extract
    (`watch_factor`) is data; NO new machinery. -/
theorem watch_schedule_independent :
    Kit.Noninterfering watchRun (Kit.agreeOn lastSend?) (Kit.agreeOn id) :=
  Kit.noninterfering_of_factor (fun o => o.getD none) (fun t => by
    simpa [watch_factor, Option.orElse] using (watch_factor t).symm)

end Machines.Async

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

## The channels' infinite faces (the coinductive consumers — this landing)

The landed coinductive foundation (`Machines.Live`) gets its first
asyncband consumers: the channels' infinite producer/consumer
interactions as the coinductive runs (the Park induction), the
LIVENESS — a blocked consumer eventually receives UNDER THE FAIRNESS
ASSUMPTION (the fairness-as-data discipline: the datum is supplied,
never derived; the drain-only stream admits NO `Fairness` value —
the honest tooth) — and the battery's LIVENESS ROW: the waitgroup's
unbounded `add` walk is the sweep's honest `.unknown` AND a
coinductively-known infinite run, conjunctly (the UNKNOWN face says
"the sweep cannot cover", never "nothing is known"; the Explore
bridge's honest gap is the gap, the coinductive proof covers the
infinite face the budget cannot).

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
module

public import Machines.Dsl
public import Machines.Live
public import Kit.Hyper
public import Kit.Observer
@[expose] public section


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
  Machines.check mutex.toMachine (fun s => !decide (s = .both)) mutex.labels .free 4

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
  sem.reachable_preserves 0 (by show (0 : Nat) ≤ 2; omega) h

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

instance : DecidablePred wg.inv := fun _ => isTrue trivial

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

/- The oneshot is GENERIC in the payload type `α` (the theorems hold
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
theorem oneshot_recv_empty_refused (_u : α) :
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
            have h2 : s.tail.length = s.length - 1 := List.length_tail
            show s.tail.length ≤ 2
            omega }

instance : DecidablePred mpsc.inv := fun s =>
  inferInstanceAs (Decidable (s.length ≤ 2))

/-- The battery-complete label enumeration (the finite payload
    universe makes this possible). -/
def mpscInputs : List MpscLabel := [.recv, .send .a, .send .b]

theorem mpscInputs_complete : ∀ i, i ∈ mpscInputs := by
  intro i
  cases i with
  | recv => simp [mpscInputs]
  | send p => cases p <;> simp [mpscInputs]

/-- THE bounded-backpressure law: every reachable buffer is within the
    cap — `reachable_preserves`'s instance (the framework law CITED). -/
theorem mpsc_bounded (s : List Pay) (h : mpsc.toMachine.Reachable [] s) :
    s.length ≤ 2 :=
  mpsc.reachable_preserves [] (by decide) h

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

instance : DecidablePred onceCell.inv := fun _ => isTrue trivial

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
  | nil =>
      intro s h
      rw [Machine.run_nil] at h
      have hs' : s = some v := (Option.some.inj h).symm
      simp [hs']
  | cons i rest ih =>
      intro s h
      rw [Machine.run_cons, Option.bind_eq_some_iff] at h
      obtain ⟨s₀, hstep, hrun⟩ := h
      cases i with
      | get =>
          have hget : s₀ = some v := by
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, onceCell] at hstep
            exact hstep.symm
          rw [hget] at hrun
          exact ih hrun
      | init u =>
          simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, onceCell] at hstep

/-! ## Family 7 — the Pool (the effects' resource discipline's instance) -/

/-- The pool's handles: the FINITE universe `Fin 2` — the battery's
    completeness premise needs a complete label enumeration, and the
    universe half of the pool discipline rides the TYPE (the earlier
    draft carried it in the invariant; the type is the honest home). -/
def h0 : Fin 2 := 0
def h1 : Fin 2 := 1

/-- The pool's labels: acquire/release PER HANDLE — payload-free (the
    battery's completeness premise), the universe in the state type. -/
inductive PoolLabel where
  | acquire0 | acquire1 | release0 | release1
deriving DecidableEq, Repr, BEq

/-- THE pool: the state is the CHECKED-OUT set (a list with the
    nodup+universe invariant — Effects.Resource's split shape at the
    machine face: the checkout = the live handle, the release = the
    split; D7's discipline CITED in prose, never imported — the cone
    stays Machines'). `acquire` refuses an already-checked-out handle;
    the invariant makes the accounting the effect row cannot express
    (`Effects.row_blind_to_double_spend`'s machine face). -/
def pool : MachineWithInv (List (Fin 2)) PoolLabel where
  inv := fun s => s.Nodup
  event := fun l => match l with
    | .acquire0 =>
        { guard := fun s => !decide (h0 ∈ s)
        , action := fun s _ => h0 :: s
        , safety := by
            intro s hg hs
            have hg' : h0 ∉ s := by
              simp only [Bool.not_eq_true'] at hg
              simpa using hg
            exact List.nodup_cons.mpr ⟨hg', hs⟩ }
    | .acquire1 =>
        { guard := fun s => !decide (h1 ∈ s)
        , action := fun s _ => h1 :: s
        , safety := by
            intro s hg hs
            have hg' : h1 ∉ s := by
              simp only [Bool.not_eq_true'] at hg
              simpa using hg
            exact List.nodup_cons.mpr ⟨hg', hs⟩ }
    | .release0 =>
        { guard := fun s => decide (h0 ∈ s)
        , action := fun s _ => s.erase h0
        , safety := by intro s _ hg; exact hg.erase h0 }
    | .release1 =>
        { guard := fun s => decide (h1 ∈ s)
        , action := fun s _ => s.erase h1
        , safety := by intro s _ hg; exact hg.erase h1 }

instance : DecidablePred pool.inv := fun s =>
  inferInstanceAs (Decidable (s.Nodup))

/-- The pool's battery-complete label enumeration (the payload-free
    per-handle labels make it complete). -/
def poolInputs : List PoolLabel :=
  [.acquire0, .acquire1, .release0, .release1]

theorem poolInputs_complete : ∀ i, i ∈ poolInputs := by
  intro i; cases i <;> simp [poolInputs]

/-- THE pool's state discipline: every reachable checked-out set is
    duplicate-free — `reachable_preserves`'s instance (the framework
    law CITED). The nodup discipline IS the resource accounting's
    content: a released-then-reacquired handle cannot ghost. -/
theorem pool_state_ok (s : List (Fin 2)) (h : pool.toMachine.Reachable [] s) :
    s.Nodup :=
  pool.reachable_preserves [] List.nodup_nil h

/-- THE no-double-checkout law: with `h0` checked out, the acquire of
    `h0` is refused — the guard IS the accounting (the effect row's
    blindness, repaired at the machine face; `h1`'s face is the same
    shape, `pool_acquire1_refused`). -/
theorem pool_no_double_checkout (s : List (Fin 2)) (hm : h0 ∈ s) :
    pool.toMachine.step? s .acquire0 = none := by
  have hd : decide (h0 ∈ s) = true := decide_eq_true_eq.mpr hm
  simp only [MachineWithInv.toMachine, MachineWithInv.step?_eq, pool]
  rw [hd]
  simp

/-- The `h1` face of the refusal (the same shape). -/
theorem pool_acquire1_refused (s : List (Fin 2)) (hm : h1 ∈ s) :
    pool.toMachine.step? s .acquire1 = none := by
  have hd : decide (h1 ∈ s) = true := decide_eq_true_eq.mpr hm
  simp only [MachineWithInv.toMachine, MachineWithInv.step?_eq, pool]
  rw [hd]
  simp

/-- The run face: no successful run checks out the same handle twice
    in a row — the second acquire cannot fire, so the run FAILS
    (the refusal is observable, never silent). -/
theorem pool_no_double_checkout_run (t : List PoolLabel) (s : List (Fin 2))
    (_hr : pool.toMachine.run [] t = some s) (hm : h0 ∈ s) :
    pool.toMachine.run s [.acquire0, .acquire0] = none := by
  rw [Machine.run_cons, pool_no_double_checkout s hm]
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
      cases i with
      | recv =>
          obtain ⟨s, hs⟩ := ih init
          refine ⟨s, ?_⟩
          have hstep : watch.toMachine.step? init .recv = some init := by
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, watch]
          rw [Machine.run_cons, hstep, Option.bind_some]
          exact hs
      | send v =>
          obtain ⟨s, hs⟩ := ih (some v)
          refine ⟨s, ?_⟩
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
      simp [h, lastSend?]
  | cons i rest ih =>
      intro init s h
      rw [Machine.run_cons, Option.bind_eq_some_iff] at h
      obtain ⟨s₀, hstep, hrun⟩ := h
      cases i with
      | recv =>
          have hs₀ : s₀ = init := by
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, watch] at hstep
            exact hstep.symm
          rw [ih s₀ s hrun, hs₀]
          simp only [lastSend?]
      | send v =>
          have hs₀ : s₀ = some v := by
            simp [MachineWithInv.toMachine, MachineWithInv.step?_eq, watch] at hstep
            exact hstep.symm
          rw [ih s₀ s hrun, hs₀]
          cases hl : lastSend? rest <;> simp [hl, lastSend?]

/-- The delivered value: the totaled run from the empty cell (every
    run succeeds — `watch_run_total`). -/
def watchRun (t : List WatchLabel) : Option Nat :=
  Option.getD (watch.toMachine.run none t) none

/-- The coalescing law at the delivered-value face (the factor the
    hyperproperty cites): the delivered value IS the last send (or
    `none` — nothing delivered). -/
theorem watch_factor (t : List WatchLabel) :
    watchRun t = lastSend? t := by
  obtain ⟨s, hs⟩ := watch_run_total t none
  have hres := watch_run_last t none s hs
  show (watch.toMachine.run none t).getD none = lastSend? t
  rw [hs, hres]
  cases hl : lastSend? t <;> simp

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
  Kit.noninterfering_of_factor id watch_factor
/-! ## The channels' infinite faces (the coinductive runs + the fairness liveness) -/

/-- The observers (the identity: the state IS what one step exposes). -/
def payObs : Kit.Observer (List Pay) (List Pay) := ⟨id⟩
def natObs : Kit.Observer Nat Nat := ⟨id⟩
def natOptObs : Kit.Observer (Option Nat) (Option Nat) := ⟨id⟩

/-- The mpsc's coalgebra — the infinite face speaks through the landed
    unfold (`states`/`next`, Coalg.lean). -/
def mpscCoal : Coalgebra (List Pay) MpscLabel (List Pay) :=
  ⟨mpsc.toMachine, payObs⟩

/-- The mpsc's send step (the guard is the cap's). -/
theorem mpsc_send_step (s : List Pay) (p : Pay) (h : s.length < 2) :
    mpscCoal.machine.step? s (.send p) = some (s ++ [p]) := by
  show MachineWithInv.step? mpsc s (MpscLabel.send p) = _
  simp [MachineWithInv.step?_eq, mpsc, show s.length < 2 from h]

/-- The mpsc's recv step (the guard is non-emptiness). -/
theorem mpsc_recv_step (s : List Pay) (h : s ≠ []) :
    mpscCoal.machine.step? s .recv = some s.tail := by
  show MachineWithInv.step? mpsc s MpscLabel.recv = _
  simp [MachineWithInv.step?_eq, mpsc, h]

/-- The mpsc's recv refusal at the empty buffer — THE BLOCK: the
    consumer's blocked face is DATA (never a silent value). -/
theorem mpsc_recv_empty_refused : mpscCoal.machine.step? [] .recv = none := rfl

theorem mpsc_next_send (s : List Pay) (p : Pay) (h : s.length < 2) :
    mpscCoal.next s (.send p) = s ++ [p] := by
  have hobs : mpscCoal.observe s (.send p) = some (s ++ [p], s ++ [p]) := by
    show Option.map (fun s' => (mpscCoal.observer.see s', s'))
      (mpscCoal.machine.step? s (.send p)) = _
    rw [mpsc_send_step s p h]
    rfl
  exact mpscCoal.next_of_some hobs

theorem mpsc_next_recv (s : List Pay) (h : s ≠ []) :
    mpscCoal.next s .recv = s.tail := by
  have hobs : mpscCoal.observe s .recv = some (s.tail, s.tail) := by
    show Option.map (fun s' => (mpscCoal.observer.see s', s'))
      (mpscCoal.machine.step? s .recv) = _
    rw [mpsc_recv_step s h]
    rfl
  exact mpscCoal.next_of_some hobs

theorem mpsc_next_hold (s : List Pay) (i : MpscLabel)
    (h : mpscCoal.machine.step? s i = none) : mpscCoal.next s i = s := by
  have hobs : mpscCoal.observe s i = none := by
    show Option.map (fun s' => (mpscCoal.observer.see s', s'))
      (mpscCoal.machine.step? s i) = none
    rw [h]
    rfl
  exact mpscCoal.next_of_none hobs

/-! ### The mpsc: the fair schedule, the run, the liveness, the unfair tooth -/

/-- THE FAIR SCHEDULE: the producer sends at every even time, the
    consumer recvs at every odd time — the alternation named as DATA.
    The fairness assumption's witness at the channel face. -/
def insAlt : Stream MpscLabel :=
  fun t => if t % 2 = 0 then .send .a else .recv

theorem insAlt_even (t : Nat) (h : t % 2 = 0) : insAlt t = .send .a := by
  show (if t % 2 = 0 then MpscLabel.send Pay.a else MpscLabel.recv) = _
  rw [if_pos h]

theorem insAlt_odd (t : Nat) (h : ¬ t % 2 = 0) : insAlt t = .recv := by
  show (if t % 2 = 0 then MpscLabel.send Pay.a else MpscLabel.recv) = _
  rw [if_neg h]

/-- The fair schedule's state stream: even times EMPTY, odd times
    `[_]` — the alternation as data (the induction the liveness rides). -/
theorem states_mpsc_alt (t : Nat) :
    mpscCoal.states insAlt [] t = if t % 2 = 0 then [] else [.a] := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Coalgebra.states_succ, ih]
      rcases Nat.mod_two_eq_zero_or_one t with h | h
      · rw [if_pos h, insAlt_even t h, mpsc_next_send [] Pay.a (by simp),
          if_neg (show ¬ (t + 1) % 2 = 0 from by omega)]
        rfl
      · rw [if_neg (show ¬ t % 2 = 0 from by omega), insAlt_odd t (by omega),
          mpsc_next_recv [Pay.a] (by simp),
          if_pos (show (t + 1) % 2 = 0 from by omega)]
        rfl

/-- THE FAIRNESS AS DATA, mpsc face: under the fair schedule the buffer
    fires at every time — the producer's send, the consumer's recv. The
    datum the liveness rides; supplied, never derived. -/
theorem fair_mpsc : Fairness mpscCoal insAlt [] := by
  refine ⟨fun t => ?_⟩
  rw [states_mpsc_alt t]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [if_pos h, insAlt_even t h]
    exact ⟨[] ++ [Pay.a], mpsc_send_step [] Pay.a (by simp)⟩
  · rw [if_neg (by omega), insAlt_odd t (by omega)]
    exact ⟨[], mpsc_recv_step [Pay.a] (by simp)⟩

/-- THE ASSUMPTION IS THE RUN, channel face: the fairness datum feeds
    the unfold bridge (`Fairness.infRun`, cited) — the mpsc's infinite
    producer/consumer interaction AS the coinductive run. -/
theorem infRun_mpsc : InfRun mpsc.toMachine insAlt [] := fair_mpsc.infRun

/-- THE LIVENESS (the blocked consumer eventually receives): under the
    fair schedule the consumer's recv — which BLOCKS at the empty
    buffer (`mpsc_recv_empty_refused`, the refusal is data) — receives
    at time 1. -/
theorem mpsc_eventually_nonempty :
    Eventually (fun s : List Pay => s ≠ []) mpscCoal insAlt [] := by
  refine ⟨1, ?_⟩
  rw [states_mpsc_alt 1, if_neg (show ¬ (1 : Nat) % 2 = 0 from by omega)]
  exact List.cons_ne_nil Pay.a []

/-- THE INFINITE FACE (the coinductive liveness): the buffer is
    non-empty INFINITELY OFTEN under the fair schedule — the consumer
    receives forever. The Park induction over the time-indexed face. -/
theorem mpsc_alwaysEventually_nonempty :
    AlwaysEventually (fun s : List Pay => s ≠ []) mpscCoal insAlt [] := by
  apply InfOften.park (fun _ => True) trivial
  intro t _
  refine ⟨1 - t % 2, ?_, trivial⟩
  show (fun s : List Pay => s ≠ [])
    (mpscCoal.states insAlt [] (t + (1 - t % 2)))
  rw [states_mpsc_alt, if_neg (show ¬ (t + (1 - t % 2)) % 2 = 0 from by omega)]
  exact List.cons_ne_nil Pay.a []

/-- THE UNFAIR TOOTH: the drain-only stream — recv every time, the
    consumer's schedule WITHOUT the producer. The buffer holds at `[]`
    forever, and NO `Fairness` value exists (the table refutes the
    assumption outright: the first recv refuses). The liveness does not
    land — the honesty is the point (01-core §3's correction, at the
    channel face). -/
def insDrain : Stream MpscLabel := fun _ => .recv

theorem states_mpsc_hold (t : Nat) : mpscCoal.states insDrain [] t = [] := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Coalgebra.states_succ, ih, show insDrain t = .recv from rfl,
        mpsc_next_hold [] MpscLabel.recv mpsc_recv_empty_refused]

theorem unfair_mpsc_drain : ¬ Fairness mpscCoal insDrain [] := by
  rintro ⟨kf⟩
  obtain ⟨s', h1⟩ := kf 0
  rw [show mpscCoal.states insDrain [] 0 = [] from rfl,
    show insDrain 0 = .recv from rfl, mpsc_recv_empty_refused] at h1
  simp at h1

/-- The run face of the same tooth: NO infinite run under the
drain-only stream (the greatest fixed point sees the refusal —
`InfRun.refuses`, cited). -/
theorem noInfRun_mpsc_drain (h : InfRun mpsc.toMachine insDrain []) :
    False :=
  h.refuses (by
    show mpsc.toMachine.step? [] MpscLabel.recv = none
    exact mpsc_recv_empty_refused)

/-! ### The watch: the producer MAY produce forever -/

/-- The watch's coalgebra (the identity observer). -/
def watchCoal : Coalgebra (Option Nat) WatchLabel (Option Nat) :=
  ⟨watch.toMachine, natOptObs⟩

theorem watch_send_step (s : Option Nat) :
    watchCoal.machine.step? s (.send 7) = some (some 7) := rfl

theorem watch_next_send (s : Option Nat) :
    watchCoal.next s (.send 7) = some 7 := by
  have hobs : watchCoal.observe s (.send 7) = some (some 7, some 7) := by
    show Option.map (fun s' => (watchCoal.observer.see s', s'))
      (watchCoal.machine.step? s (.send 7)) = _
    rw [watch_send_step s]
    rfl
  exact watchCoal.next_of_some hobs

/-- The constant-send schedule (the producer's unbounded supply). -/
def insWatchFor : Stream WatchLabel := fun _ => .send 7

theorem insWatchFor_step (t : Nat) : insWatchFor t = WatchLabel.send 7 := rfl

/-- The watch's state stream under the constant-send schedule: `none`
once, then the latest value forever — the coalescing's totaled face. -/
theorem states_watch (t : Nat) :
    watchCoal.states insWatchFor none t = if t = 0 then none else some 7 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Coalgebra.states_succ, ih]
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [if_pos h, insWatchFor_step t, watch_next_send,
          if_neg (show ¬ (t + 1) = 0 from by omega)]
      · rw [if_neg (show ¬ t = 0 from by omega),
          insWatchFor_step t, watch_next_send,
          if_neg (show ¬ (t + 1) = 0 from by omega)]

/-- THE PRODUCER'S INFINITE FACE, watch: the send NEVER blocks (it
    overwrites — the coalescing semantics), so the producer MAY produce
    forever: the constant-send stream's fairness datum exists, and it
    IS the infinite run (`Fairness.infRun`, cited). -/
theorem fair_watch : Fairness watchCoal insWatchFor none := by
  refine ⟨fun t => ?_⟩
  rw [states_watch t]
  rcases Nat.eq_zero_or_pos t with h | h
  · rw [if_pos h, insWatchFor_step t]
    exact ⟨some 7, watch_send_step none⟩
  · rw [if_neg (by omega), insWatchFor_step t]
    exact ⟨some 7, watch_send_step (some 7)⟩

theorem infRun_watch : InfRun watch.toMachine insWatchFor none := fair_watch.infRun

/-! ### The oneshot: the single-send law's coinductive face -/

/-- The oneshot's coalgebra (the identity observer). -/
def oneCoal : Coalgebra (Option Nat) (OneLabel Nat) (Option Nat) :=
  ⟨oneshot.toMachine, natOptObs⟩

theorem oneshot_send_step_none (v : Nat) :
    oneCoal.machine.step? none (.send v) = some (some v) := rfl

theorem oneshot_next_send_empty (v : Nat) :
    oneCoal.next none (.send v) = some v := by
  have hobs : oneCoal.observe none (.send v) = some (some v, some v) := by
    show Option.map (fun s' => (oneCoal.observer.see s', s'))
      (oneCoal.machine.step? none (.send v)) = _
    rw [oneshot_send_step_none v]
    rfl
  exact oneCoal.next_of_some hobs

theorem oneshot_next_hold_full (v : Nat) :
    oneCoal.next (some v) (.send v) = some v := rfl

/-- THE UNBOUNDED-PRODUCER TOOTH, oneshot: the constant-send stream —
    the producer the single-send law REFUSES. The state stream is
    `none` once, then `some` forever holding (the refusal holds), and
    the run dies: the greatest fixed point sees the second send's
    refusal, so NO infinite run exists. The unbounded producer's honest
    home is the watch (above) or the mpsc under the fair schedule —
    never the oneshot. -/
def insSend : Stream (OneLabel Nat) := fun _ => .send 3

theorem states_oneshot (t : Nat) :
    oneCoal.states insSend none t = if t = 0 then none else some 3 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Coalgebra.states_succ, ih]
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [if_pos h, show insSend t = .send 3 from rfl,
          oneshot_next_send_empty 3, if_neg (show ¬ (t + 1) = 0 from by omega)]
      · rw [if_neg (show ¬ t = 0 from by omega),
          show insSend t = .send 3 from rfl, oneshot_next_hold_full 3,
          if_neg (show ¬ (t + 1) = 0 from by omega)]

theorem noInfRun_oneshot : ¬ InfRun oneshot.toMachine insSend none := by
  intro h
  have hf := states_fires_of_infRun oneCoal h 2
  rw [states_oneshot 2, if_neg (show ¬ (2 : Nat) = 0 from by decide),
    show insSend 2 = .send 3 from rfl] at hf
  have hr : oneCoal.machine.step? (some 3) (.send 3) = none :=
    oneshot_send_full_refused 3 3
  rw [hr] at hf
  simp at hf

/-! ## The battery's liveness row (the coinductive discipline consumes the honest gap) -/

/-- The waitgroup's battery-complete label enumeration (the liveness
    row's sweep premise). -/
def wgInputs : List WgLabel := [WgLabel.add, .done, .wait]

theorem wgInputs_complete : ∀ i, i ∈ wgInputs := by
  intro i; cases i <;> simp [wgInputs]

/-- The waitgroup's coalgebra (the identity observer). -/
def wgCoal : Coalgebra Nat WgLabel Nat := ⟨wg.toMachine, natObs⟩

/-- THE COINDUCTIVE FACE OF THE HONEST GAP: the waitgroup's `add` walk
    is UNBOUNDED — the battery's deadlock sweep can never stabilize
    (the tests pin the `.unknown .budgetExhausted`) — but the
    coinductive discipline DOES know this face: `add` is always
    enabled, the Park induction closes trivially, the infinite run
    EXISTS. -/
theorem wg_add_step (x : Nat) :
    wg.toMachine.step? x WgLabel.add = some (x + 1) := rfl

theorem wg_infRun_add : InfRun wg.toMachine (fun _ => WgLabel.add) 0 := by
  apply InfRun.park (fun is x => ∀ u, is u = WgLabel.add)
  · exact fun u => rfl
  · rintro is x his
    rw [his 0]
    exact ⟨x + 1, wg_add_step x, fun u => his (u + 1)⟩

/-- THE BATTERY'S LIVENESS ROW: the sweep's honest UNKNOWN and the
    coinductive run, CONJUNCTLY — the row the conformance battery gains
    where the coinductive discipline applies. The `.unknown` says "the
    sweep cannot cover the fragment" (the Explore bridge's honest gap,
    `Machines.Live`), never "nothing is known": the coinductive proof
    covers the infinite face the budget cannot. -/
theorem wg_liveness_row :
    Testing.deadlockFree wg wgInputs 0 4 wgInputs_complete
      = Testing.BatteryVerdict.unknown Machines.ExploreReason.budgetExhausted
    ∧ InfRun wg.toMachine (fun _ => WgLabel.add) 0 :=
  ⟨by rfl, wg_infRun_add⟩

end Machines.Async

end -- public section

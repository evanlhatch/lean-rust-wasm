/-
# Machines.Sim — deterministic simulation testing (DST) core

The scheduled machine over `Machines.Core`'s machines: components are
Core machines (ANY `Machine` — the sim is generic in `m`), a message
queue of in-flight deliveries, a clock, and a schedule that is DATA —
a value of `Choice`, never a nondeterministic pick. THE DST PRINCIPLE:
the schedule is an input, so the same schedule gives the same trace
(`simTrace_congr`), always. Replaying is re-evaluating a pure function.

The theorems (the honest fragment):

- `stepSim_det` / `simTrace_congr` / `runSim_congr` — schedule
  determinism: `stepSim` is a pure function of (choice, state); equal
  schedules from equal states give equal traces and equal final states.
- `stepSim_conserves` / `no_loss` — message-queue CONSERVATION: the
  only way a message leaves the queue is `Delivered` — consumed by a
  SUCCESSFUL `Machine.step?` at its destination. A message never
  vanishes: after any schedule it is delivered or still in flight.
  (`stepSim_inflight_sublist`: steps never invent messages either.)
- `schedulable_fires` — no-deadlock (non-stuck) honesty: if some
  component event is enabled somewhere or some in-flight message is
  deliverable, a schedule step EXISTS that fires it (and steps the
  clock — `Fires_clock`). The machine-agnostic half of liveness;
  whether a blocked delivery ever BECOMES enabled is a per-machine
  question — see `Machines.Sync`'s `*_unblocks` theorems.
- `deliver_swap` — the queue diamond: two messages to DISTINCT
  destinations delivered in either order reach the same full state
  (the `compose_commute` diamond, executed through the queue).
- `deliver_order_irrelevant` — the CRDT point, at the sim level: two
  deltas delivered to ONE replica in either arrival order reach the
  SAME state, because additive application is abelian-group addition.

The dbsp wire-up: Machines depends on dbsp (lakefile; direction
Machines → dbsp, no cycle — dbsp requires nothing of Machines), so
`zset_sim_two_replica` ties the queue-executed final state to
`Dbsp.Replicas.applyDeltas` directly, and
`zset_deliver_order_irrelevant` is `Dbsp.Replicas.two_replica_converge`
— the reordering license — REUSED, not re-proved:
`batch_order_irrelevant` IS schedule-independence for batches; the sim
executes it through a concrete schedule pair.

Deliberate scope: the schedule is a LIST of choices (an offline
schedule = the recordable/replayable artifact); no unbounded-liveness
(leads-to) claims — `Schedulable` is stated at the state level, where
the Core's `enabled` is the only notion of pending work. A blocked
delivery is a no-op (conservation), not a stuck step.
-/

import Machines.Core
import Dbsp.Replicas

namespace Machines.Sim

open Machines
open Dbsp

variable {m : Machine} {Pid : Type}
variable [DecidableEq Pid]

/-! ## The model: components + in-flight messages + clock -/

/-- An in-flight message: the sender, the receiver, and the event to
    fire at the receiver — the payload travels INSIDE the label (e.g.
    `Sync.MpscEvent.send v` carries `v`; the Core's `Label` is the wire
    vocabulary, exactly as `Machine.run` consumes it). -/
structure Msg (m : Machine) (Pid : Type) where
  src : Pid
  dst : Pid
  lbl : m.Label

/-- The simulation state: one `m.State` per component, the in-flight
    queue (delivery order = list order), the tick count. -/
structure SimState (m : Machine) (Pid : Type) where
  comp : Pid → m.State
  inflight : List (Msg m Pid)
  clock : Nat

/-- One scheduler decision: deliver the queue's `i`-th message, fire a
    component's local event, or tick the clock. The schedule is a LIST
    of these — data, not a nondeterministic pick. -/
inductive Choice (m : Machine) (Pid : Type) where
  | deliver (i : Nat)
  | fire (p : Pid) (l : m.Label)
  | tick

/-- Point update of one component. -/
def updComp (p : Pid) (f : m.State → m.State) (c : Pid → m.State) : Pid → m.State :=
  fun q => if q = p then f (c q) else c q

theorem updComp_self (p : Pid) (f : m.State → m.State) (c : Pid → m.State) :
    updComp p f c p = f (c p) := by simp [updComp]

theorem updComp_ne {p q : Pid} (h : q ≠ p) (f : m.State → m.State) (c : Pid → m.State) :
    updComp p f c q = c q := by simp [updComp, h]

/-- Point updates to DISTINCT points commute — the algebra behind the
    queue diamond. -/
theorem updComp_comm {p q : Pid} (hne : p ≠ q) (f g : m.State → m.State)
    (c : Pid → m.State) :
    updComp q f (updComp p g c) = updComp p g (updComp q f c) := by
  funext r
  unfold updComp
  by_cases hrq : r = q
  · subst hrq
    have hrp : r ≠ p := fun h => hne h.symm
    simp [hrp]
  · by_cases hrp : r = p
    · subst hrp
      have hrq' : r ≠ q := fun h => hne h
      simp [hrq']
    · simp [hrp, hrq]

/-! ## The step — deterministic by construction -/

/-- One step. TOTAL and DETERMINISTIC: every branch is a pattern on the
    choice value; a blocked delivery (out-of-range index, or the
    destination's guard fails) is a NO-OP — the message stays in flight
    (conservation), the clock does not move (nothing happened). -/
def stepSim (ch : Choice m Pid) (σ : SimState m Pid) : SimState m Pid :=
  match ch with
  | .tick => { σ with clock := σ.clock + 1 }
  | .fire p l =>
      { σ with
        comp := updComp p (fun s => (m.step? s l).getD s) σ.comp
        clock := σ.clock + 1 }
  | .deliver i =>
      match σ.inflight[i]? with
      | none => σ
      | some msg =>
        match m.step? (σ.comp msg.dst) msg.lbl with
        | none => σ
        | some s' =>
          { σ with
            comp := updComp msg.dst (fun _ => s') σ.comp
            inflight := σ.inflight.eraseIdx i
            clock := σ.clock + 1 }

/-- Enqueue: a message enters the queue (at the back). -/
def enqueue (msg : Msg m Pid) (σ : SimState m Pid) : SimState m Pid :=
  { σ with inflight := σ.inflight ++ [msg] }

omit [DecidableEq Pid] in
@[simp] theorem enqueue_inflight (msg : Msg m Pid) (σ : SimState m Pid) :
    (enqueue msg σ).inflight = σ.inflight ++ [msg] := rfl

omit [DecidableEq Pid] in
theorem enqueue_mem (msg : Msg m Pid) (σ : SimState m Pid) :
    msg ∈ (enqueue msg σ).inflight := by simp [enqueue]

/-- A schedule (a list of choices) runs to a final state. -/
def runSim (chs : List (Choice m Pid)) (σ : SimState m Pid) : SimState m Pid :=
  match chs with
  | [] => σ
  | c :: rest => runSim rest (stepSim c σ)

/-- The observable trace: the sequence of states the schedule walks. -/
def simTrace (chs : List (Choice m Pid)) (σ : SimState m Pid) : List (SimState m Pid) :=
  match chs with
  | [] => [σ]
  | c :: rest => σ :: simTrace rest (stepSim c σ)

@[simp] theorem runSim_nil (σ : SimState m Pid) : runSim [] σ = σ := rfl

@[simp] theorem runSim_cons (c : Choice m Pid) (rest : List (Choice m Pid))
    (σ : SimState m Pid) :
    runSim (c :: rest) σ = runSim rest (stepSim c σ) := rfl

@[simp] theorem simTrace_nil (σ : SimState m Pid) : simTrace [] σ = [σ] := rfl

@[simp] theorem simTrace_cons (c : Choice m Pid) (rest : List (Choice m Pid))
    (σ : SimState m Pid) :
    simTrace (c :: rest) σ = σ :: simTrace rest (stepSim c σ) := rfl

-- stepSim's case equations (the delivery branch splits on the queue
-- index and the destination guard; blocked = no-op).

theorem stepSim_tick (σ : SimState m Pid) :
    stepSim .tick σ = { σ with clock := σ.clock + 1 } := rfl

theorem stepSim_fire (p : Pid) (l : m.Label) (σ : SimState m Pid) :
    stepSim (.fire p l) σ =
      { σ with comp := updComp p (fun s => (m.step? s l).getD s) σ.comp
              , clock := σ.clock + 1 } := rfl

theorem stepSim_deliver_none (i : Nat) (σ : SimState m Pid) (h : σ.inflight[i]? = none) :
    stepSim (.deliver i) σ = σ := by simp only [stepSim, h]

/-- A `step?` that returns `none` means the guard was false. -/
theorem step?_none_guard {s : m.State} {l : m.Label} (h : m.step? s l = none) :
    (m.event l).guard s = false := by
  cases hg : (m.event l).guard s with
  | false => rfl
  | true => rw [Machine.step?_eq, dif_pos hg] at h; simp at h

theorem stepSim_deliver_blocked (i : Nat) (σ : SimState m Pid) (msg : Msg m Pid)
    (h : σ.inflight[i]? = some msg)
    (hb : m.step? (σ.comp msg.dst) msg.lbl = none) :
    stepSim (.deliver i) σ = σ := by
  simp only [stepSim, h, Machine.step?_eq]
  rw [dif_neg (by simp [step?_none_guard hb])]

theorem stepSim_deliver (i : Nat) (σ : SimState m Pid) (msg : Msg m Pid) (s' : m.State)
    (h : σ.inflight[i]? = some msg)
    (hd : m.step? (σ.comp msg.dst) msg.lbl = some s') :
    stepSim (.deliver i) σ =
      { σ with comp := updComp msg.dst (fun _ => s') σ.comp
              , inflight := σ.inflight.eraseIdx i
              , clock := σ.clock + 1 } := by
  obtain ⟨hg, hact⟩ := m.step?_eq_some hd
  simp only [stepSim, h, Machine.step?_eq, dif_pos hg, hact]

/-! ## (a) Schedule determinism -/

/-- THE trivial-but-stated core: the step is a pure function of the
    choice and the state. There is no other input to be nondeterministic
    about — the schedule is data. -/
theorem stepSim_det (ch : Choice m Pid) (σ : SimState m Pid) :
    stepSim ch σ = stepSim ch σ := rfl

/-- Same schedule, same trace — determinism as a REPLAY guarantee: two
    runs whose schedule lists and starting states agree produce
    identical traces. (Induction on the schedule; the step function is
    deterministic by `stepSim_det`.) -/
theorem simTrace_congr {chs chs' : List (Choice m Pid)} {σ σ' : SimState m Pid}
    (hchs : chs = chs') (hσ : σ = σ') :
    simTrace chs σ = simTrace chs' σ' := by
  subst hchs; subst hσ; rfl

/-- Same schedule, same final state (the replay checker's contract). -/
theorem runSim_congr {chs chs' : List (Choice m Pid)} {σ σ' : SimState m Pid}
    (hchs : chs = chs') (hσ : σ = σ') :
    runSim chs σ = runSim chs' σ' := by
  subst hchs; subst hσ; rfl

/-- The trace records one state per step plus the start — the
    schedule's length, independent of the components. -/
theorem simTrace_length (chs : List (Choice m Pid)) (σ : SimState m Pid) :
    (simTrace chs σ).length = chs.length + 1 := by
  induction chs generalizing σ with
  | nil => simp
  | cons c rest ih => simp [ih]

/-! ## (b) No loss — queue conservation -/

/-- A helper: erasing index `i` keeps every element except the one AT
    `i`. (The converse of the `getElem?`-membership bridge — the
    direction the conservation proof consumes.) -/
theorem mem_eraseIdx_of_ne {α : Type} {l : List α} {x y : α} :
    ∀ (i : Nat), x ∈ l → l[i]? = some y → x ≠ y → x ∈ l.eraseIdx i := by
  intro i
  induction l generalizing i with
  | nil => intro _ hget _; exact absurd hget (by simp)
  | cons a t ih =>
      intro hmem hget hne
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          rcases List.mem_cons.mp hmem with rfl | hm
          · exact absurd rfl hne
          · simpa using hm
      | succ i' =>
          rcases List.mem_cons.mp hmem with rfl | hm
          · simp
          · have hx : x ∈ t.eraseIdx i' := ih i' hm (by simpa using hget) hne
            simp [hx]

/-- ONE STEP CONSERVES: a message in flight is either still in flight
    after the step, or it was DELIVERED — the choice was `deliver i`
    with the message at index `i` and a SUCCESSFUL `step?` at its
    destination. Deletion happens only on delivery. -/
theorem stepSim_conserves (ch : Choice m Pid) (σ : SimState m Pid) (msg : Msg m Pid)
    (hmem : msg ∈ σ.inflight) :
    msg ∈ (stepSim ch σ).inflight ∨
      ∃ i : Nat, ch = .deliver i ∧ σ.inflight[i]? = some msg ∧
        ∃ s' : m.State, m.step? (σ.comp msg.dst) msg.lbl = some s' := by
  cases ch with
  | tick => exact Or.inl (by rw [stepSim_tick]; exact hmem)
  | fire p l => exact Or.inl (by rw [stepSim_fire]; exact hmem)
  | deliver i =>
      cases hget : σ.inflight[i]? with
      | none => exact Or.inl (by rw [stepSim_deliver_none i σ hget]; exact hmem)
      | some other =>
          cases hstep : m.step? (σ.comp other.dst) other.lbl with
          | none =>
              exact Or.inl (by rw [stepSim_deliver_blocked i σ other hget hstep]; exact hmem)
          | some s' =>
              if heq : other = msg then
                subst heq
                exact Or.inr ⟨i, rfl, hget, s', hstep⟩
              else
                refine Or.inl ?_
                rw [stepSim_deliver i σ other s' hget hstep]
                exact mem_eraseIdx_of_ne i hmem hget (fun h => heq h.symm)

/-- The message's DELIVERY along a schedule: at some step, the choice
    was `deliver i` with the message at index `i` and the destination's
    step? succeeded — the message was consumed by an enabled event. -/
inductive Delivered (m : Machine) (Pid : Type) [DecidableEq Pid] (msg : Msg m Pid) :
    List (Choice m Pid) → SimState m Pid → Prop where
  /-- Delivered at this step. -/
  | here (i : Nat) (rest : List (Choice m Pid)) (σ : SimState m Pid)
      (hget : σ.inflight[i]? = some msg)
      (hst : ∃ s' : m.State, m.step? (σ.comp msg.dst) msg.lbl = some s') :
      Delivered m Pid msg (.deliver i :: rest) σ
  /-- Delivered at some later step. -/
  | there (c : Choice m Pid) (rest : List (Choice m Pid)) (σ : SimState m Pid)
      (h : Delivered m Pid msg rest (stepSim c σ)) :
      Delivered m Pid msg (c :: rest) σ

/-- NO LOSS: after ANY schedule, every initially-queued message is
    either still in flight or was delivered (consumed by a successful
    `step?` at its destination). A message never vanishes. -/
theorem no_loss (chs : List (Choice m Pid)) (σ : SimState m Pid) (msg : Msg m Pid)
    (hmem : msg ∈ σ.inflight) :
    msg ∈ (runSim chs σ).inflight ∨ Delivered m Pid msg chs σ := by
  induction chs generalizing σ with
  | nil => exact Or.inl hmem
  | cons c rest ih =>
      rcases stepSim_conserves c σ msg hmem with hkeep | ⟨i, hch, hget, s', hst⟩
      · rcases ih (stepSim c σ) hkeep with h | h
        · exact Or.inl (by rw [runSim_cons]; exact h)
        · exact Or.inr (Delivered.there c rest σ h)
      · subst hch
        exact Or.inr (Delivered.here i rest σ hget ⟨s', hst⟩)

/-- Steps never INVENT messages: the queue after a step is a sublist of
    the queue before (only `enqueue` adds). -/
theorem stepSim_inflight_sublist (ch : Choice m Pid) (σ : SimState m Pid) :
    List.Sublist (stepSim ch σ).inflight σ.inflight := by
  cases ch with
  | tick => exact List.Sublist.refl _
  | fire p l => exact List.Sublist.refl _
  | deliver i =>
      cases hget : σ.inflight[i]? with
      | none => rw [stepSim_deliver_none i σ hget]
      | some other =>
        cases hstep : m.step? (σ.comp other.dst) other.lbl with
        | none => rw [stepSim_deliver_blocked i σ other hget hstep]
        | some s' =>
            rw [stepSim_deliver i σ other s' hget hstep]
            exact List.eraseIdx_sublist _ _

/-! ## (c) No deadlock — the non-stuck states are steppable -/

/-- A schedule choice FIRES in `σ`: a local event whose guard holds, or
    a delivery whose destination `step?` succeeds. The tick fires
    trivially (it is pure progress). -/
def Fires (ch : Choice m Pid) (σ : SimState m Pid) : Prop :=
  match ch with
  | .tick => True
  | .fire p l => ∃ s' : m.State, m.step? (σ.comp p) l = some s'
  | .deliver i =>
      ∃ msg : Msg m Pid, σ.inflight[i]? = some msg ∧
        ∃ s' : m.State, m.step? (σ.comp msg.dst) msg.lbl = some s'

/-- A state is SCHEDULABLE when some component event is enabled
    somewhere, or some in-flight message is deliverable — the Core's
    `enabled` is the pending-work notion, the queue's deliverability is
    the message notion. -/
def Schedulable (σ : SimState m Pid) : Prop :=
  (∃ p : Pid, ∃ l : m.Label, m.enabled (σ.comp p) l = true) ∨
  (∃ msg : Msg m Pid, msg ∈ σ.inflight ∧
    ∃ s' : m.State, m.step? (σ.comp msg.dst) msg.lbl = some s')

omit [DecidableEq Pid] in
/-- NO DEADLOCK (the honest half): a schedulable state has a schedule
    step that FIRES. Not claimed: that a blocked delivery ever becomes
    enabled (per-machine liveness — `Machines.Sync`'s `*_unblocks`). -/
theorem schedulable_fires (σ : SimState m Pid) (h : Schedulable σ) :
    ∃ ch : Choice m Pid, Fires ch σ := by
  rcases h with ⟨p, l, henable⟩ | ⟨msg, hmem, s', hst⟩
  · have hg : (m.event l).guard (σ.comp p) = true := henable
    refine ⟨.fire p l, ⟨(m.event l).action (σ.comp p) hg, ?_⟩⟩
    rw [Machine.step?_eq, dif_pos hg]
  · obtain ⟨i, hget⟩ := List.getElem?_of_mem hmem
    exact ⟨.deliver i, msg, hget, s', hst⟩

/-- The fired step's effect: a fired delivery consumed its message and
    advanced the destination; a fired local event advanced its
    component. Both step the clock — observable progress. -/
theorem Fires_clock (ch : Choice m Pid) (σ : SimState m Pid) (h : Fires ch σ) :
    (stepSim ch σ).clock = σ.clock + 1 := by
  cases ch with
  | tick => exact rfl
  | fire p l => exact rfl
  | deliver i =>
      have h' : ∃ msg : Msg m Pid, σ.inflight[i]? = some msg ∧
          ∃ s' : m.State, m.step? (σ.comp msg.dst) msg.lbl = some s' := h
      obtain ⟨msg, hget, s', hst⟩ := h'
      rw [stepSim_deliver i σ msg s' hget hst]

/-! ## The queue diamond — two deliveries, either order -/

/-- The QUEUE DIAMOND: two in-flight messages to DISTINCT destinations,
    delivered in either order, reach the SAME full simulation state —
    in-flight queue, clock, and every component. (Same content as
    `Machines.Machine.compose_commute`, executed through the queue:
    each delivery touches only its own destination.) -/
theorem deliver_swap (σ : SimState m Pid) (m₁ m₂ : Msg m Pid)
    (rest : List (Msg m Pid)) (hσ : σ.inflight = m₁ :: m₂ :: rest)
    (hdst : m₁.dst ≠ m₂.dst) (s₁ s₂ : m.State)
    (h₁ : m.step? (σ.comp m₁.dst) m₁.lbl = some s₁)
    (h₂ : m.step? (σ.comp m₂.dst) m₂.lbl = some s₂) :
    stepSim (.deliver 0) (stepSim (.deliver 0) σ)
      = stepSim (.deliver 0) (stepSim (.deliver 1) σ) := by
  have hget0 : σ.inflight[0]? = some m₁ := by rw [hσ]; simp
  have hget1 : σ.inflight[1]? = some m₂ := by rw [hσ]; simp
  -- left schedule: deliver m₁, then m₂ (now at index 0)
  have eL1 : stepSim (.deliver 0) σ
      = ⟨updComp m₁.dst (fun _ => s₁) σ.comp, m₂ :: rest, σ.clock + 1⟩ := by
    rw [stepSim_deliver 0 σ m₁ s₁ hget0 h₁, hσ]
    rfl
  have hL2step : m.step? (updComp m₁.dst (fun _ => s₁) σ.comp m₂.dst) m₂.lbl = some s₂ := by
    rw [updComp_ne (q := m₂.dst) (p := m₁.dst) (fun h => hdst h.symm) _ _]
    exact h₂
  have eL : stepSim (.deliver 0) (stepSim (.deliver 0) σ)
      = ⟨updComp m₂.dst (fun _ => s₂) (updComp m₁.dst (fun _ => s₁) σ.comp), rest,
          σ.clock + 2⟩ := by
    rw [eL1, stepSim_deliver 0 _ m₂ s₂ (by simp) hL2step]
    rfl
  -- right schedule: deliver m₂ (index 1), then m₁ (now at index 0)
  have eR1 : stepSim (.deliver 1) σ
      = ⟨updComp m₂.dst (fun _ => s₂) σ.comp, m₁ :: rest, σ.clock + 1⟩ := by
    rw [stepSim_deliver 1 σ m₂ s₂ hget1 h₂, hσ]
    rfl
  have hR2step : m.step? (updComp m₂.dst (fun _ => s₂) σ.comp m₁.dst) m₁.lbl = some s₁ := by
    rw [updComp_ne (q := m₁.dst) (p := m₂.dst) (fun h => hdst h) _ _]
    exact h₁
  have eR : stepSim (.deliver 0) (stepSim (.deliver 1) σ)
      = ⟨updComp m₁.dst (fun _ => s₁) (updComp m₂.dst (fun _ => s₂) σ.comp), rest,
          σ.clock + 2⟩ := by
    rw [eR1, stepSim_deliver 0 _ m₁ s₁ (by simp) hR2step]
    rfl
  rw [eL, eR, updComp_comm hdst (fun _ => s₂) (fun _ => s₁) σ.comp]

/-! ## The demo — the CRDT point: schedule-independence -/

/-- The additive machine: the label IS the delta; one event family,
    always enabled, adds the delta. The queue-transport component (the
    group shape `Machines.LinearMachine` bridges to `Dbsp.ChangeSpec`;
    at `G := ZSet A` this is a `Dbsp.Replicas` replica collection).
    Reducible so `(addMachine G).State` unfolds to `G` in the record
    literals below (the `compose` precedent). -/
@[reducible]
noncomputable def addMachine (G : Type) [AddCommGroup G] : Machine where
  State := G
  Label := G
  Inv := fun _ => True
  event := fun δ =>
    { guard := fun _ => true
      action := fun s _ => s + δ
      safety := fun _ _ h => h }

theorem addMachine_step {G : Type} [AddCommGroup G] (s δ : G) :
    (addMachine G).step? s δ = some (s + δ) := by
  simp only [Machine.step?]
  rfl

/-- One in-flight delta message. Named so the delivery computations can
    match `updComp`'s point-update patterns syntactically. -/
noncomputable def deltaMsg {G : Type} [AddCommGroup G] (δ : G) (src b : Pid) :
    Msg (addMachine G) Pid :=
  { src := src, dst := b, lbl := δ }

/-- The two-delta queue: every replica starts at `s`; deltas `δ₁ δ₂` in
    flight, both addressed to replica `b`. -/
noncomputable def twoDeltaState {G : Type} [AddCommGroup G] (s δ₁ δ₂ : G)
    (src b : Pid) : SimState (addMachine G) Pid :=
  { comp := fun _ => s
    inflight := [deltaMsg δ₁ src b, deltaMsg δ₂ src b]
    clock := 0 }

/-- Delivering the two deltas through the queue IS the group sum: after
    both deliveries (in queue order), the replica's state is the deltas
    summed over the start — `Dbsp.Replicas.applyDeltas_sum` executed. -/
theorem add_delivered_sum {G : Type} [AddCommGroup G] (s δ₁ δ₂ : G) (src b : Pid) :
    (stepSim (.deliver 0) (stepSim (.deliver 0) (twoDeltaState s δ₁ δ₂ src b))).comp b
      = (s + δ₁) + δ₂ := by
  have h1 : stepSim (.deliver 0)
        ({ comp := fun _ => s
         , inflight := [deltaMsg δ₁ src b, deltaMsg δ₂ src b], clock := 0 } :
          SimState (addMachine G) Pid)
      = ({ comp := updComp b (fun _ => s + δ₁) (fun _ => s)
         , inflight := [deltaMsg δ₂ src b], clock := 1 } :
          SimState (addMachine G) Pid) := by
    rw [stepSim_deliver 0 _ (deltaMsg δ₁ src b) (s + δ₁) (by simp) (addMachine_step s δ₁)]
    rfl
  unfold twoDeltaState
  rw [h1]
  rw [stepSim_deliver 0 _ (deltaMsg δ₂ src b) ((s + δ₁) + δ₂)
      (by simp) (by simp [updComp, deltaMsg])]
  simp [updComp, deltaMsg]

/-- Same, in the SWAPPED arrival order. -/
theorem add_delivered_sum_swap {G : Type} [AddCommGroup G] (s δ₁ δ₂ : G) (src b : Pid) :
    (stepSim (.deliver 0) (stepSim (.deliver 1) (twoDeltaState s δ₁ δ₂ src b))).comp b
      = (s + δ₂) + δ₁ := by
  have h1 : stepSim (.deliver 1)
        ({ comp := fun _ => s
         , inflight := [deltaMsg δ₁ src b, deltaMsg δ₂ src b], clock := 0 } :
          SimState (addMachine G) Pid)
      = ({ comp := updComp b (fun _ => s + δ₂) (fun _ => s)
         , inflight := [deltaMsg δ₁ src b], clock := 1 } :
          SimState (addMachine G) Pid) := by
    rw [stepSim_deliver 1 _ (deltaMsg δ₂ src b) (s + δ₂) (by simp) (addMachine_step s δ₂)]
    rfl
  unfold twoDeltaState
  rw [h1]
  rw [stepSim_deliver 0 _ (deltaMsg δ₁ src b) ((s + δ₂) + δ₁)
      (by simp) (by simp [updComp, deltaMsg])]
  simp [updComp, deltaMsg]

/-- THE CRDT CLAIM, at the sim level: two deltas delivered to ONE
    replica in EITHER arrival order reach the SAME state. Schedule
    independence is group commutativity — the delivery schedule cannot
    change the outcome, only its speed. -/
theorem deliver_order_irrelevant {G : Type} [AddCommGroup G] (s δ₁ δ₂ : G) (src b : Pid) :
    (stepSim (.deliver 0) (stepSim (.deliver 0) (twoDeltaState s δ₁ δ₂ src b))).comp b
      = (stepSim (.deliver 0) (stepSim (.deliver 1) (twoDeltaState s δ₁ δ₂ src b))).comp b := by
  rw [add_delivered_sum, add_delivered_sum_swap]
  abel

/-- The dbsp wire-up (at `G := ZSet A`): the queue-executed final state
    IS `Dbsp.Replicas.applyDeltas` — the sim's delta application is the
    same group sum the replica theory certifies. -/
theorem zset_sim_two_replica {A : Type} (s δ₁ δ₂ : ZSet A) (src b : Pid) :
    (stepSim (.deliver 0) (stepSim (.deliver 0) (twoDeltaState s δ₁ δ₂ src b))).comp b
      = Dbsp.Replicas.applyDeltas s [δ₁, δ₂] := by
  rw [add_delivered_sum]
  show (s + δ₁) + δ₂ = δ₁ + (δ₂ + s)
  abel

/-- The reordering license, REUSED: the queue-executed schedule
    independence IS `Dbsp.Replicas.two_replica_converge` — opposite
    arrival orders converge, because `batch_order_irrelevant` holds for
    the group sum the deliveries perform. Not re-proved: reduced. -/
theorem zset_deliver_order_irrelevant {A : Type} (s δ₁ δ₂ : ZSet A) (src b : Pid) :
    (stepSim (.deliver 0) (stepSim (.deliver 0) (twoDeltaState s δ₁ δ₂ src b))).comp b
      = (stepSim (.deliver 0) (stepSim (.deliver 1) (twoDeltaState s δ₁ δ₂ src b))).comp b := by
  have h1 := zset_sim_two_replica s δ₁ δ₂ src b
  have h2 : (stepSim (.deliver 0) (stepSim (.deliver 1) (twoDeltaState s δ₁ δ₂ src b))).comp b
      = Dbsp.Replicas.applyDeltas s [δ₂, δ₁] := by
    rw [add_delivered_sum_swap]
    show (s + δ₂) + δ₁ = δ₂ + (δ₁ + s)
    abel
  rw [h1, h2, Dbsp.Replicas.two_replica_converge s δ₁ δ₂]

end Machines.Sim

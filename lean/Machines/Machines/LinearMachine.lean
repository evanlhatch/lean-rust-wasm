/-
# Machines.LinearMachine — machines over change groups (the DBSP bridge)

Bridges Machines (guarded state machines, mathlib-free) to the Dbsp
change-structure spec shape (`Dbsp.ChangeSpec`'s `Change`/`Difference`/
`ChangeInversion` — re-declared here, mathlib-free, so the bridge layer
stays pure). Contents:

1. `ChangeGroup` — the MINIMAL commutative group class replacing mathlib's
   `AddCommGroup`: `add`/`zero`/`neg` + the four laws. From it we derive
   the `Dbsp.ChangeSpec`-shaped change structure over the machine state
   (patch = `+`, diff = `new - old`, invert = `-`, noc = `0`), all laws
   proved.
2. `LinearMachine m` — the linearity predicate: a machine RESPECTS its
   change group when stepping a patched state equals patching the stepped
   state by the event's delta transform:
   `step? (patch s δ) l = patchOpt (eventDelta l δ) (step? s l)`.
   The law forces guard stability (`LinearMachine.guard_patch_stable`) —
   a delta can neither enable nor disable an event.
3. `Machine.incrementalStep` / `Machine.deltaChain` — the delta-only
   evaluator: it consumes deltas and labels, never a full state.
4. `incremental_run_equiv` — THE THEOREM: the batch run of the patched
   machine equals the batch run of the base machine corrected by the pure
   delta chain. The incremental evaluator and the batch evaluator agree
   under the group operations.

Deliberately out of scope (per the bridge brief): the full DBSP
incrementality calculus (three-term stream joins, D/I over `Stream`).
The point is the INTERFACE: `Machine` + `ChangeGroup` + the linearity law.
-/

import Machines.Core

namespace Machines

/-! ## ChangeGroup — the minimal group class (mathlib-free) -/

/-- A commutative group, with the laws as class fields. This is the
    mathlib-free stand-in for `AddCommGroup`: Machines does not depend on
    mathlib, and neither does the bridge. -/
class ChangeGroup (α : Type) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : α, add a b = add b a
  zero_add : ∀ a : α, add zero a = a
  neg_add_cancel : ∀ a : α, add (neg a) a = zero

instance ChangeGroup.toAdd (α : Type) [ChangeGroup α] : Add α := ⟨ChangeGroup.add⟩
instance ChangeGroup.toZero (α : Type) [ChangeGroup α] : Zero α := ⟨ChangeGroup.zero⟩
instance ChangeGroup.toNeg (α : Type) [ChangeGroup α] : Neg α := ⟨ChangeGroup.neg⟩

section
variable {α : Type} [ChangeGroup α]

theorem add_assoc (a b c : α) : a + b + c = a + (b + c) :=
  ChangeGroup.add_assoc a b c

theorem add_comm (a b : α) : a + b = b + a :=
  ChangeGroup.add_comm a b

theorem zero_add (a : α) : 0 + a = a :=
  ChangeGroup.zero_add a

theorem neg_add_cancel (a : α) : -a + a = 0 :=
  ChangeGroup.neg_add_cancel a

/-- The right-sided laws, derived from the class fields by commutativity. -/
theorem add_zero (a : α) : a + 0 = a := by
  rw [add_comm, zero_add]

theorem add_neg_cancel (a : α) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

/-! ## Patching: the change structure over the machine state -/

/-- Patch a state by a delta: addition in the change group. The
    `Change.patch` of the Dbsp spec shape. -/
def patch (s δ : α) : α := ChangeGroup.add s δ

theorem patch_zero (s : α) : patch s 0 = s := add_zero s

end

/-! ## The Dbsp.ChangeSpec shape, re-declared (mathlib-free)

Same field names and laws as `Dbsp.ChangeSpec`, so the spec-level reading
carried there transfers verbatim; we only drop the `AddCommGroup`
dependency in favor of `ChangeGroup`. -/

/-- A change structure: changes patch values, with a validity predicate. -/
class Change (α Δα : Type) where
  patch : α → Δα → α
  valid : α → Δα → Prop

/-- Computing the change between two values. -/
class Difference (α Δα : Type) [Change α Δα] where
  diff : α → α → Δα
  diff_valid : ∀ old new, Change.valid old (diff new old)
  diff_correct : ∀ old new, Change.patch old (diff new old) = new

/-- Every change has an inverse: rollback. -/
class ChangeInversion (α Δα : Type) extends Change α Δα where
  invert : Δα → Δα
  valid_invert : ∀ (t : α) (Δt : Δα), Change.valid t Δt →
    Change.valid (Change.patch t Δt) (invert Δt)
  correct_invert : ∀ (t : α) (Δt : Δα), Change.valid t Δt →
    Change.patch (Change.patch t Δt) (invert Δt) = t

/-- The no-op change. -/
class Noc (Δα : Type) where
  noc : Δα

class LawfulNoChange (α Δα : Type) [Noc Δα] [Change α Δα] where
  valid_noc : ∀ t : α, Change.valid t (Noc.noc (Δα := Δα))
  correct_noc : ∀ t : α, Change.patch t (Noc.noc (Δα := Δα)) = t

/-- Every `ChangeGroup` is a change structure over itself — the canonical
    group change structure of `Dbsp.ChangeSpec`, mathlib-free. -/
instance Change.groupSelf (α : Type) [ChangeGroup α] : Change α α where
  patch := Machines.patch
  valid := fun _ _ => True

instance Difference.groupSelf (α : Type) [ChangeGroup α] : Difference α α where
  diff new old := patch new (ChangeGroup.neg old)
  diff_valid := fun _ _ => trivial
  diff_correct := fun old new => by
    show old + (new + -old) = new
    rw [← add_assoc, add_comm old new, add_assoc, add_neg_cancel, add_zero]

instance ChangeInversion.groupSelf (α : Type) [ChangeGroup α] : ChangeInversion α α where
  invert := ChangeGroup.neg
  valid_invert := fun _ _ _ => trivial
  correct_invert := fun t Δt _ => by
    show (t + Δt) + -Δt = t
    rw [add_assoc, add_neg_cancel, add_zero]

instance Noc.groupSelf (α : Type) [ChangeGroup α] : Noc α where
  noc := ChangeGroup.zero

instance LawfulNoChange.groupSelf (α : Type) [ChangeGroup α] : LawfulNoChange α α where
  valid_noc := fun _ => trivial
  correct_noc := fun t => by
    show patch t (ChangeGroup.zero) = t
    exact add_zero t

section
variable {α : Type} [ChangeGroup α]

/-- Rollback of a group delta restores the value (the Dbsp revert law). -/
theorem group_rollback (t Δt : α) : patch (patch t Δt) (-Δt) = t :=
  ChangeInversion.correct_invert t Δt (by trivial)

end

/-! ## LinearMachine — machines that respect their change group -/

/-- Pointwise patching of an optional state: `none` (a disabled step)
    stays `none` — the delta of a disabled event is unobservable. -/
def patchOpt [ChangeGroup α] (δ : α) : Option α → Option α
  | none => none
  | some s => some (patch s δ)

/-- A machine is LINEAR when its event structure respects the change
    group: applying a delta then stepping = stepping then applying the
    event's delta transform. Translation-equivariance of the dynamics —
    the machine-level content of DBSP's linearity. -/
class LinearMachine (m : Machine) [ChangeGroup m.State] where
  /-- The delta transform induced by event `l`: the running delta after
      the event, as a function of the running delta before it. -/
  eventDelta : m.Label → m.State → m.State
  /-- The linearity law. The law ALONE forces the guards to be
      patch-stable (`LinearMachine.guard_patch_stable`) — `none` cannot
      be patched. -/
  linear : ∀ (s δ : m.State) (l : m.Label),
    m.step? (patch s δ) l = patchOpt (eventDelta l δ) (m.step? s l)

theorem step?_eq_none (m : Machine) (s : m.State) (l : m.Label)
    (h : (m.event l).guard s = false) : m.step? s l = none := by
  simp [Machine.step?, h]

theorem step?_eq_true (m : Machine) (s : m.State) (l : m.Label)
    (h : (m.event l).guard s = true) :
    m.step? s l = some ((m.event l).action s h) := by
  simp [Machine.step?, h]

/-- The linearity law forces the guard to be stable under patching: a
    delta can neither enable nor disable an event. -/
theorem LinearMachine.guard_patch_stable (m : Machine) [ChangeGroup m.State]
    [LinearMachine m] (s δ : m.State) (l : m.Label) :
    (m.event l).guard s = (m.event l).guard (patch s δ) := by
  have h := LinearMachine.linear (m := m) (s := s) (δ := δ) (l := l)
  cases hs : (m.event l).guard s with
  | false =>
    have e1 : m.step? s l = none := step?_eq_none m s l hs
    rw [e1] at h
    simp [patchOpt] at h
    cases hp : (m.event l).guard (patch s δ) with
    | false => rfl
    | true =>
      rw [step?_eq_true m (patch s δ) l hp] at h
      simp at h
  | true =>
    have e1 : m.step? s l = some ((m.event l).action s hs) := step?_eq_true m s l hs
    rw [e1] at h
    simp [patchOpt] at h
    cases hp : (m.event l).guard (patch s δ) with
    | true => rfl
    | false =>
      rw [step?_eq_none m (patch s δ) l hp] at h
      simp at h

namespace Machine

/-- The delta-only version of `step?`: the running delta after event `l`
    is the event's delta transform. Consumes no full state. -/
def incrementalStep (m : Machine) [ChangeGroup m.State] [LinearMachine m]
    (Δs : m.State) (l : m.Label) : m.State :=
  LinearMachine.eventDelta l Δs

/-- The delta chain: fold `incrementalStep` over the trace, starting from
    δ. The result is a delta RELATIVE to the batch run's final state —
    translation-equivariant dynamics preserve the offset. -/
def deltaChain (m : Machine) [ChangeGroup m.State] [LinearMachine m]
    (δ : m.State) : List m.Label → m.State
  | [] => δ
  | l :: rest => m.deltaChain (m.incrementalStep δ l) rest

@[simp] theorem deltaChain_nil (m : Machine) [ChangeGroup m.State] [LinearMachine m]
    (δ : m.State) : m.deltaChain δ [] = δ := rfl

@[simp] theorem deltaChain_cons (m : Machine) [ChangeGroup m.State] [LinearMachine m]
    (δ : m.State) (l : m.Label) (rest : List m.Label) :
    m.deltaChain δ (l :: rest) = m.deltaChain (m.incrementalStep δ l) rest := rfl

/-- The batch run, keeping only the final state — the final-state runner:
    same step-rejection behavior as `Machine.run`, one state instead of a
    full trace. -/
def runState (m : Machine) (s : m.State) : List m.Label → Option m.State
  | [] => some s
  | l :: ls =>
    match m.step? s l with
    | none => none
    | some s' => m.runState s' ls

@[simp] theorem runState_nil (m : Machine) (s : m.State) :
    m.runState s [] = some s := rfl

@[simp] theorem runState_cons (m : Machine) (s : m.State) (l : m.Label)
    (ls : List m.Label) :
    m.runState s (l :: ls) =
      match m.step? s l with
      | none => none
      | some s' => m.runState s' ls := rfl

end Machine

/-! ## THE THEOREM — the incremental run agrees with the batch run -/

/-- **The run-level linearity lemma.** Stepping the PATCHED state through
    the trace lands exactly where stepping the base state lands, corrected
    by the pure delta chain — which was computed from the labels alone,
    inspecting no full state. -/
theorem runState_patch_deltaChain (m : Machine) [ChangeGroup m.State] [LinearMachine m]
    (δ : m.State) :
    ∀ (s : m.State) (trace : List m.Label),
      m.runState (patch s δ) trace =
        (m.runState s trace).map (fun fin => patch fin (m.deltaChain δ trace)) := by
  intro s trace
  induction trace generalizing s δ with
  | nil => rfl
  | cons l rest ih =>
    rw [Machine.runState_cons, LinearMachine.linear, Machine.runState_cons]
    cases hstep : m.step? s l with
    | none =>
      -- the event is disabled in the base state: both runs reject (and by
      -- LinearMachine.guard_patch_stable they reject together)
      simp [patchOpt]
    | some s₁ =>
      -- the event fires: the patched run continues from the patched
      -- post-state, and the IH folds the remaining delta transform
      simp only [patchOpt]
      rw [ih (LinearMachine.eventDelta l δ) s₁]
      rfl

/-- **THE THEOREM — `incremental_run_equiv`.** The incremental run (the
    delta chain, consuming only deltas and labels) and the batch run (the
    full-state run) produce related final states: the batch run of the
    patched machine ends at the batch final state patched by the delta
    chain. With a zero initial delta the final states are EQUAL
    (`runState_zero_chain`). -/
theorem incremental_run_equiv (m : Machine) [ChangeGroup m.State] [LinearMachine m]
    (s₀ δ₀ : m.State) (trace : List m.Label) :
    m.runState (patch s₀ δ₀) trace =
      (m.runState s₀ trace).map (fun fin => patch fin (m.deltaChain δ₀ trace)) :=
  runState_patch_deltaChain m δ₀ s₀ trace

/-- Corollary: with a zero initial delta the batch run is unchanged — the
    incremental evaluator reconstructs the batch trajectory exactly. -/
theorem runState_zero_chain (m : Machine) [ChangeGroup m.State] [LinearMachine m]
    (s₀ : m.State) (trace : List m.Label) :
    m.runState (patch s₀ 0) trace = m.runState s₀ trace := by
  rw [patch_zero]

end Machines

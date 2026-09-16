/-
# Machines.LinearMachine — machines over change groups (the DBSP bridge)

Bridges Machines (guarded state machines) to the Dbsp change-structure
spec shape (`Dbsp.ChangeSpec`'s `Change`/`Difference`/`ChangeInversion` —
re-declared here, because Machines does not depend on dbsp; see the TODO
at the classes). Contents:

1. The change-structure classes over mathlib's `AddCommGroup`: from it we
   derive the `Dbsp.ChangeSpec`-shaped change structure over the machine
   state (patch = `+`, diff = `new - old`, invert = `-`, noc = `0`), all
   laws proved by `abel`.
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
The point is the INTERFACE: `Machine` + `AddCommGroup` + the linearity law.
-/

module

public import Machines.Core
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Tactic.Abel
public import Dbsp.ChangeSpec

-- W5.4 module discipline: all declarations public; bodies exposed
-- (defs/instances must reduce across module boundaries).
@[expose] public section

namespace Machines

open Dbsp

/-! ## The Dbsp.ChangeSpec shape, IMPORTED (the dependency landed)

The change-structure classes were re-declared here while Machines did
not depend on dbsp; the dependency direction now allows the import, so
the copies are gone. `Change`/`Difference`/`ChangeInversion`/`Noc`/
`LawfulNoChange` + the `AddCommGroup` `groupSelf` instances all live in
`Dbsp.ChangeSpec`; this module keeps the MACHINES-side aliases
(`patch`/`patch_zero`) and the rest of the linearity story. -/

section
variable {α : Type} [AddCommGroup α]

/-- Patch a state by a delta: addition in the group. The `Change.patch`
    of the Dbsp spec shape — the machines-side alias. -/
def patch (s δ : α) : α := Change.patch s δ

theorem patch_zero (s : α) : patch s 0 = s := by
  change s + 0 = s
  exact add_zero s

/-- Rollback of a group delta restores the value (the Dbsp revert law,
    restated through the local alias). -/
theorem group_rollback (t Δt : α) : patch (patch t Δt) (-Δt) = t := by
  change Change.patch (Change.patch t Δt) (-Δt) = t
  exact Dbsp.group_rollback (α := α) t Δt

end

/-! ## LinearMachine — machines that respect their change group -/

/-- Pointwise patching of an optional state: `none` (a disabled step)
    stays `none` — the delta of a disabled event is unobservable. -/
def patchOpt [AddCommGroup α] (δ : α) : Option α → Option α
  | none => none
  | some s => some (patch s δ)

/-- A machine is LINEAR when its event structure respects the change
    group: applying a delta then stepping = stepping then applying the
    event's delta transform. Translation-equivariance of the dynamics —
    the machine-level content of DBSP's linearity. -/
class LinearMachine (m : Machine) [AddCommGroup m.State] where
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
theorem LinearMachine.guard_patch_stable (m : Machine) [AddCommGroup m.State]
    [LinearMachine m] (s δ : m.State) (l : m.Label) :
    (m.event l).guard s = (m.event l).guard (patch s δ) := by
  have h := LinearMachine.linear (m := m) (s := s) (δ := δ) (l := l)
  cases hs : (m.event l).guard s with
  | false =>
    have e1 : m.step? s l = none := step?_eq_none m s l hs
    rw [e1] at h
    simp only [patchOpt] at h
    cases hp : (m.event l).guard (patch s δ) with
    | false => rfl
    | true =>
      rw [step?_eq_true m (patch s δ) l hp] at h
      simp at h
  | true =>
    have e1 : m.step? s l = some ((m.event l).action s hs) := step?_eq_true m s l hs
    rw [e1] at h
    simp only [patchOpt] at h
    cases hp : (m.event l).guard (patch s δ) with
    | true => rfl
    | false =>
      rw [step?_eq_none m (patch s δ) l hp] at h
      simp at h

namespace Machine

/-- The delta-only version of `step?`: the running delta after event `l`
    is the event's delta transform. Consumes no full state. -/
def incrementalStep (m : Machine) [AddCommGroup m.State] [LinearMachine m]
    (Δs : m.State) (l : m.Label) : m.State :=
  LinearMachine.eventDelta l Δs

/-- The delta chain: fold `incrementalStep` over the trace, starting from
    δ. The result is a delta RELATIVE to the batch run's final state —
    translation-equivariant dynamics preserve the offset. -/
def deltaChain (m : Machine) [AddCommGroup m.State] [LinearMachine m]
    (δ : m.State) : List m.Label → m.State
  | [] => δ
  | l :: rest => m.deltaChain (m.incrementalStep δ l) rest

@[simp] theorem deltaChain_nil (m : Machine) [AddCommGroup m.State] [LinearMachine m]
    (δ : m.State) : m.deltaChain δ [] = δ := rfl

@[simp] theorem deltaChain_cons (m : Machine) [AddCommGroup m.State] [LinearMachine m]
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
theorem runState_patch_deltaChain (m : Machine) [AddCommGroup m.State] [LinearMachine m]
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
theorem incremental_run_equiv (m : Machine) [AddCommGroup m.State] [LinearMachine m]
    (s₀ δ₀ : m.State) (trace : List m.Label) :
    m.runState (patch s₀ δ₀) trace =
      (m.runState s₀ trace).map (fun fin => patch fin (m.deltaChain δ₀ trace)) :=
  runState_patch_deltaChain m δ₀ s₀ trace

/-- Corollary: with a zero initial delta the batch run is unchanged — the
    incremental evaluator reconstructs the batch trajectory exactly. -/
theorem runState_zero_chain (m : Machine) [AddCommGroup m.State] [LinearMachine m]
    (s₀ : m.State) (trace : List m.Label) :
    m.runState (patch s₀ 0) trace = m.runState s₀ trace := by
  rw [patch_zero]

end Machines

end -- @[expose] public section

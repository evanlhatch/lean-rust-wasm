/-
# Machines.Events — the EventSpec/guard layer: the invariant slot, honestly

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/01-core.md §3 (preservation is a THEOREM
over the authoritative transition semantics, never a convention) +
notes/v3/15-patterns.md #9's mined shape (legacy
legacy/lean/Machines/Machines/Core.lean:34-61, ported fresh): actions
are executable functions with the guard PROOF threaded into
construction — an UPDATE…WHERE cannot be constructed without
discharging its guard, and an event cannot be constructed without
discharging its safety obligation.

## The integration judgment (recorded)

The landed `Machine (S I)` (Basic.lean) carries ONLY `step?` — the
minimal TraceModel carrier. The invariant slot does NOT mutate it
(every landed consumer — Trace, Explore, the tests — would pay for a
field it never reads; the leftover rule cuts the other way too).
Instead: `MachineWithInv (S I)` — the EventSpec-family machine whose
events CARRY their safety proof — with `toMachine` as the ONE bridge
down to the landed carrier:

- `step?` is DERIVED from the guards and actions (`dif` on the guard)
  — an event cannot fire past its guard, by construction;
- the relation `step` is the graph of the derived `step?` (the
  Basic.lean discipline, unchanged), so `step_iff` is `Iff.rfl` again;
- every law of the landed carrier — `run`, `Reachable`, `Exec`,
  Explore's battery-grade machinery — is INHERITED by citation
  through `toMachine`, never re-proved. `run_preserves` below rides
  a general preservation lemma stated over the landed `Machine` (the
  lemma's own consumer is this file).

## The seam (CLOSED — the macro landed)

The `machine!` MACRO (15-patterns #9's entourage) is LANDED
(`Machines.Dsl`): one declaration generates the state enum + the Label
inductive + this EventSpec family + the `MachineWithInv` assembly + the
table stack + the tie theorem + the `DecidablePred` instance + the
battery registration. What landed here BEFORE it was the hand-built
layer the macro generates; the safety-PO defaulting this header named
as an exclusion lives in `Machines.Dsl` (`machine_safety`).

## The five questions

- **Root**: TraceModel (01-core §3) — the invariant rides the same
  authoritative transition semantics; preservation is DERIVED (the
  theorems below), never a convention.
- **Carrier grade**: pattern #1 again — the EventSpec family is the
  spec reading; the derived `step?` is the checker; `step_iff` and
  `toMachine` are the ties.
- **Spine reading**: none — a substrate; consumers instantiate it.
- **Ladder rung**: the preservation block is hand theorems (rung 6 —
  quantified relational content over `run`'s recursion); the
  per-machine safety POs are constructor arguments (rung 0 — a
  machine is unconstructible without them).
- **Gate rows**: the axiom report pins in MachinesTests.Axioms.

## Named exclusions

- NO safety-PO defaulting here — the default (`machine_safety`) is the
  `machine!` macro's (Machines.Dsl); hand-built machines discharge the
  PO explicitly (the constructor argument above).
- NO payload-label generalization (legacy's `conformanceOver` sample
  path) — lands with the first payload-machine consumer.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Basic

namespace Machines

/-! ## The event -/

/-- An event: a decidable guard, an action that REQUIRES the guard's
    proof, and the invariant-preservation obligation. The author
    writes state + guard + action; `safety` is the PO slot —
    discharged HERE, at construction (an event whose action can break
    the invariant is unconstructible). The `machine!` macro's
    autoParam defaulting (15-patterns #9) lands at the seam above. -/
structure EventSpec (S : Type) (Inv : S → Prop) where
  guard : S → Bool
  action : (s : S) → guard s = true → S
  safety : ∀ s h, Inv s → Inv (action s h)

/-! ## The machine with the invariant slot -/

/-- A machine with the invariant slot: state type, event labels, the
    invariant, and the event family — one `EventSpec` per label, each
    carrying its own safety proof. The `machine!` macro generates
    these (the seam); hand-built until it lands. -/
structure MachineWithInv (S I : Type) where
  inv : S → Prop
  event : I → EventSpec S inv

namespace MachineWithInv

variable {S I : Type}

/-- Is the event enabled (guard holds) in this state? -/
def enabled (m : MachineWithInv S I) (s : S) (i : I) : Bool :=
  (m.event i).guard s

/-- Execute one event. `none` = not enabled. Total. Derived from the
    family — an event cannot fire past its guard (the UPDATE…WHERE
    discipline: the guard proof is threaded into the action). -/
def step? (m : MachineWithInv S I) (s : S) (i : I) : Option S :=
  if h : (m.event i).guard s = true then some ((m.event i).action s h) else none

/-- The AUTHORITATIVE transition relation (01-core §3) — the graph of
    the derived `step?`, the Basic.lean discipline unchanged. -/
def step (m : MachineWithInv S I) (s : S) (i : I) (s' : S) : Prop :=
  m.step? s i = some s'

/-- THE BRIDGE (15-patterns #1): the relation and the checker agree —
    both directions, by definition (the relation IS the graph). -/
theorem step_iff (m : MachineWithInv S I) (s : S) (i : I) (s' : S) :
    m.step s i s' ↔ m.step? s i = some s' := Iff.rfl

/-! ## The bridge DOWN to the landed carrier -/

/-- The ONE bridge: the EventSpec-family machine viewed as the landed
    `Machine` (Basic.lean). Everything the landed carrier proves —
    run, Reachable, Exec, Explore — this machine inherits by
    citation, never re-proof. -/
def toMachine (m : MachineWithInv S I) : Machine S I := ⟨m.step?⟩

/-! ## The step inversions (the legacy block) -/

/-- Inversion, guard side: a successful step IS the guard proof plus
    the action equation — proof case-splits over the same labels the
    executor does (the no-drift discipline). -/
theorem step?_eq_some (m : MachineWithInv S I) {s : S} {i : I} {s' : S}
    (h : m.step? s i = some s') :
    ∃ hg : (m.event i).guard s = true, (m.event i).action s hg = s' := by
  rw [step?] at h
  split at h
  · next hg => exact ⟨hg, Option.some.inj h⟩
  · next => simp at h

/-- Inversion, disabled side: a disabled guard's step is `none`. -/
theorem step?_eq_none (m : MachineWithInv S I) {s : S} {i : I}
    (h : (m.event i).guard s = false) : m.step? s i = none := by
  simp [step?, h]

/-- The full unfolding (the @[simp] equation the call sites consume). -/
@[simp] theorem step?_eq (m : MachineWithInv S I) (s : S) (i : I) :
    m.step? s i =
      if h : (m.event i).guard s = true then some ((m.event i).action s h) else none :=
  rfl

/-! ## Preservation (the correctness-by-construction payoff) -/

/-- One step preserves the invariant — the EventSpec.safety
    obligation, projected through the derived `step?`. -/
theorem step?_preserves (m : MachineWithInv S I) {s : S} {i : I} {s' : S}
    (h : m.step? s i = some s') (hi : m.inv s) : m.inv s' := by
  rw [step?] at h
  split at h
  · next hg =>
      have hs := (m.event i).safety s hg hi
      rw [← Option.some.inj h]
      exact hs
  · next => simp at h

end MachineWithInv

/-! ## Preservation over the LANDED carrier (the general lemma) -/

namespace Machine

/-- The general preservation law over the landed `Machine`: if every
    successful step preserves `Inv`, the fold preserves `Inv` — the
    invariant holds at the end of every successful run. This is the
    substrate `MachineWithInv.run_preserves` cites; a machine whose
    events all discharge their safety CANNOT reach a bad state
    through `run`. -/
theorem run_preserves (m : Machine S I) (Inv : S → Prop)
    (hstep : ∀ s i s', m.step? s i = some s' → Inv s → Inv s')
    (start : S) (hstart : Inv start) :
    ∀ {t : List I} {fin : S}, m.run start t = some fin → Inv fin := by
  intro t
  induction t generalizing start with
  | nil =>
      intro fin h
      rw [m.run_nil] at h
      have : fin = start := Option.some.inj h.symm
      subst this
      exact hstart
  | cons i rest ih =>
      intro fin h
      rw [m.run_cons, Option.bind_eq_some_iff] at h
      obtain ⟨s₀, hstep₀, hrun⟩ := h
      exact ih s₀ (hstep start i s₀ hstep₀ hstart) hrun

end Machine

namespace MachineWithInv

/-- The fold preserves the invariant: `run_preserves` at the landed
    carrier, fed by `step?_preserves` — the correctness-by-construction
    payoff, inherited by citation through `toMachine`. -/
theorem run_preserves (m : MachineWithInv S I) (start : S) (hstart : m.inv start)
    {t : List I} {fin : S} (h : m.toMachine.run start t = some fin) :
    m.inv fin :=
  m.toMachine.run_preserves m.inv (fun _s _i _s' h' hi => m.step?_preserves h' hi)
    start hstart h

/-- The invariant holds on every REACHABLE state — preservation along
    the reachable view (the fold-level law's relational dual; the
    induction is over the `Reachable` witnesses). -/
theorem reachable_preserves (m : MachineWithInv S I) (init : S)
    (hinit : m.inv init) {s : S} (h : m.toMachine.Reachable init s) :
    m.inv s := by
  induction h with
  | here => exact hinit
  | step i hst _ ih => exact m.step?_preserves hst ih

end MachineWithInv

end Machines

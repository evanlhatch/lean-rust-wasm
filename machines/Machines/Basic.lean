/- 
# Machines.Basic — the machine, its two projections, the reachable view

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/01-core.md §3 (THE TraceModel discipline:
the transition semantics is AUTHORITATIVE — a machine's behavior is the
SET of its executions, with choice/repetition/divergence; traces and
reachability are DERIVED VIEWS; finite states ≠ finite executions) +
notes/v3/15-patterns.md #1 (relation-as-spec + executable checker +
proved bridge — the two readings of one transition CANNOT drift).

## The machine shape (the judgment call, recorded)

The EXECUTABLE half is primary: `Machine.step? : S → I → Option S`.
The RELATION is derived as the graph of `step?` — the mined legacy
discipline (legacy/lean/Machines/Machines/Core.lean: "the Prop relation
is derived from the same definition, so execution and proof case-split
over the same labels and cannot drift"). The bridge `step_iff` is the
pattern-#1 tie; because the relation IS the graph, both bridge
directions hold by definition — honest completeness, not a defaulted
`true`.

Where the doctrine's CHOICE lives in this slice: the input TAPE. One
state admits many executions because the tape can name different
inputs; divergence lives in loops (`tick` cycling the mod-3 machine
forever). This core is a DETERMINISTIC-relations slice — a machine
whose relation is a genuinely nondeterministic relation (relation
primary, `step?` a decidable shadow with pattern-#1's two-constructor
completeness verdict) lands with its first concurrent consumer.

## The five questions

- **Root**: TraceModel (01-core §3) — the behavior side: `Machine` is
  the minimal carrier of "events + order + divergence" at the
  sequential level; choice via tapes, conflict deferred to the
  nondeterministic extension named above.
- **Carrier grade**: pattern #1 — relation (spec reading) + executable
  checker (`step?`, `run`) + the `step_iff` bridge at the structure.
- **Spine reading**: none — Machines is a substrate; consumers
  (the finite model-checking lane, Explore) instantiate it.
- **Ladder rung**: the bridge + run/reachability laws are hand
  theorems at the structure (rung 6, the rung-6-with-reason case: they
  are relational content the kernel cannot decide in general); the
  per-machine faces land as rung-3 decides in the tests.
- **Gate rows**: the axiom report pins in MachinesTests.Axioms (the
  core-triple-only surface over the bridge + the derived-view laws).

## Named exclusions (the doctrine's heavy half waits for consumers)

- NO fairness machinery — fairness is an environment ASSUMPTION, never
  derived from the transition table (01-core §3's correction); lands
  with the liveness lane (08 §10) that needs to assume it.
- NO partial-order reduction, NO vector clocks — 08 §10's guard: the
  heavy half follows its first genuinely-concurrent consumer.
- NO nondeterministic-relation-primary machines — named above.

Core-only: no mathlib, no Batteries (the cone rule).
-/

namespace Machines

/-! ## The machine -/

/-- A machine: states `S`, input labels `I`, and the executable step —
    `none` = the input is disabled in that state (the refusal is honest
    data, never a silent self-loop). -/
structure Machine (S I : Type) where
  step? : S → I → Option S

namespace Machine

variable {S I : Type}

/-- The AUTHORITATIVE transition relation (01-core §3) — the graph of
    `step?`. Both readings of one transition; the bridge below is the
    tie. -/
def step (m : Machine S I) (s : S) (i : I) (s' : S) : Prop :=
  m.step? s i = some s'

/-- THE BRIDGE (15-patterns #1): the relation and the checker agree —
    both directions, by definition (the relation IS the graph; the two
    projections cannot drift). -/
theorem step_iff (m : Machine S I) (s : S) (i : I) (s' : S) :
    m.step s i s' ↔ m.step? s i = some s' := Iff.rfl

/-! ## The run: the fold over an input tape -/

/-- Run the tape from `s`. `none` = some input was disabled (the run is
    REJECTED — invalid tapes are observable, not silent). -/
def run (m : Machine S I) (s : S) : List I → Option S
  | [] => some s
  | i :: t => (m.step? s i).bind (fun s' => run m s' t)

@[simp] theorem run_nil (m : Machine S I) (s : S) : m.run s [] = some s := rfl

@[simp] theorem run_cons (m : Machine S I) (s : S) (i : I) (t : List I) :
    m.run s (i :: t) = (m.step? s i).bind (fun s' => m.run s' t) := rfl

/-- The append law: a run over a concatenated tape is the run of the
    first half feeding the second — tapes compose under bind. -/
theorem run_append (m : Machine S I) (s : S) (t₁ t₂ : List I) :
    m.run s (t₁ ++ t₂) = (m.run s t₁).bind (fun s' => m.run s' t₂) := by
  induction t₁ generalizing s with
  | nil => rfl
  | cons i rest ih => simp [run, Option.bind_assoc, ih]

/-! ## The reachable view -/

/-- Reachability: the DERIVED view of what the executions can visit.
    Note what this does NOT say: finitely many reachable states do not
    mean finitely many executions — the `step` constructor composes
    loops freely (01-core §3's correction). -/
inductive Reachable (m : Machine S I) (init : S) : S → Prop where
  | here : Reachable m init init
  | step : {s s' : S} → (i : I) → m.step s i s' → Reachable m init s →
      Reachable m init s'

/-- Reachability composes along itself (the transitivity the exec-level
    append needs). -/
theorem Reachable.trans {m : Machine S I} {init s₁ s₂ : S}
    (h₁ : Reachable m init s₁) (h₂ : Reachable m s₁ s₂) : Reachable m init s₂ := by
  induction h₂ with
  | here => exact h₁
  | step i h _ ih => exact .step i h ih

/-- One-step run: the tape of length one is just the step lookup.
    (The compositional unit the append law needs.) -/
theorem run_one (m : Machine S I) (s : S) (i : I) : m.run s [i] = m.step? s i := by
  simp [run]

/-- Every reachable state has a witnessing tape. -/
theorem reachable_run {m : Machine S I} {init s : S}
    (h : Reachable m init s) : ∃ t, m.run init t = some s := by
  induction h with
  | here => exact ⟨[], rfl⟩
  | step i hs _ ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t ++ [i], ?_⟩
      rw [run_append, ht, Option.bind_some, run_one]
      exact hs

/-- Every successful run witnesses reachability — the views' converse.
    Together with `reachable_run`: reachable = run-successful, one view
    in two directions. -/
theorem run_reachable {m : Machine S I} : ∀ (start : S) {t : List I} {s : S},
    m.run start t = some s → Reachable m start s := by
  intro start t
  induction t generalizing start with
  | nil => intro s h; rw [run_nil] at h; cases h; exact .here
  | cons i rest ih =>
      intro s h
      rw [run_cons] at h
      obtain ⟨s₀, hs₀, hr⟩ := Option.bind_eq_some_iff.mp h
      exact Reachable.trans (.step i hs₀ .here) (ih s₀ hr)

end Machine

end Machines

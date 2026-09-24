/-
# Machines.Testing — the conformance battery every machine inherits

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/01-core.md §3 (the honest trichotomy — a
battery check answers PROVED / REFUTED-with-witness / UNKNOWN-with-
reason, never a bare bool) + notes/v3/15-patterns.md #9's mined shape
(legacy/lean/Machines/Machines/Testing.lean, ported fresh over the
landed Explore.lean's verdict discipline).

The framework theorems (Events.lean's `step?_preserves`,
`run_preserves`, `reachable_preserves`) say what is true of EVERY
`MachineWithInv`. What they do NOT say about a PARTICULAR authored
machine:

1. **Deadlock-freedom over reachable states** — from every REACHABLE
   state satisfying the invariant, at least one event is enabled. A
   machine that can wedge in a legal state is a bug the safety POs
   cannot see (safety speaks only of states the events REACH — a
   wedged state is one no event leaves). The reachable fragment is
   computed here by the bounded frontier fold; if the fragment does
   not stabilize within the budget, the answer is `.unknown` —
   budget exhaustion is NEVER a verdict (01-core §3).
2. **Guard coverage** — every event is enabled from at least one
   enumerated state. A never-enabled event is dead code the compiler
   accepts; the battery REFUTES it with the dead label as witness.
3. **Invariant non-vacuity** — the invariant excludes at least one
   enumerated state (a `True` invariant discharges every safety PO
   and proves nothing).

These are SWEEPS, not theorems: the framework proves the laws, the
battery checks the instance. The label-completeness proof
(`∀ i, i ∈ inputs`) is threaded into both sweeps as a phantom —
REQUIRED so the caller PROVES the input enumeration is total (a
partial enumeration would let a never-swept event wedge the machine
or die undetected — the check would pass vacuously).

The verdicts are CLOSED vocabulary (ctors never strings), riding the
landed Explore discipline: `.refuted` carries its witness (the wedged
state / the dead label / the vacuity), `.unknown` carries
`ExploreReason` — the shared honest-gap cause type.

## The seam (CLOSED — the macro landed)

The `machine!` MACRO (15-patterns #9) is LANDED (`Machines.Dsl`): its
`states:` clause generates the enumerations and discharges the
completeness proof per machine, and its `battery` registration feeds
THIS battery (the generated `labels_complete` is the totality premise
below, now machine!-discharged). Hand-built machines still pass the
lists + the completeness proof as the constructor arguments here.

## The five questions

- **Root**: TraceModel (01-core §3) — the sweeps are over the
  executions' reachable fragment; deadlock-freedom is a property of
  the TRANSITION TABLE, checked here, not derived there.
- **Carrier grade**: pattern #1 again — the decidable sweeps are the
  shadows; `deadlockFree_proved` / `guardCoverage_proved` /
  `guardCoverage_refuted` are the bridges to the proposition-level
  reading.
- **Spine reading**: none — a substrate for the `machine!` lane.
- **Ladder rung**: the sweep bodies are rung-3 decides at the call
  sites (the verdicts compute by `rfl` on the worked fixtures); the
  bridge theorems are hand (rung 6) — they quantify over all
  reachable states / all labels.
- **Gate rows**: the axiom report pins in MachinesTests.Axioms.

## Named exclusions

- NO payload-label sample path (legacy's `conformanceOver`) — a
  `send (v : α)` family has no finite enumeration to prove complete;
  the sampled variant lands with the first payload-machine consumer
  (the leftover rule).
- NO trace correctness, NO safety re-check — trace correctness is the
  oracle's (engine-side); safety is the EventSpec PO, discharged at
  construction (Events.lean).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Events
import Machines.Explore

namespace Machines.Testing

/-! ## The battery's honest verdict -/

/-- WHY a check refuted: the closed vocabulary of battery failures.
    Each ctor IS the witness (ctors never strings; 04 §6). -/
inductive BatteryReason (S I : Type) where
  /-- A state satisfying the invariant with NO enabled event — the
      machine wedges in a legal state. -/
  | wedged (s : S)
  /-- An event never enabled over the enumerated states — dead code
      the compiler accepted. -/
  | dead (i : I)
  /-- The invariant holds on EVERY enumerated state — it discharges
      every PO and proves nothing. -/
  | vacuous
deriving BEq, Repr

/-- The honest trichotomy (Explore.lean's discipline, battery-grade):
    PROVED (the sweep found nothing to refute) / REFUTED (with the
    reason-as-witness) / UNKNOWN (the named honest gap — e.g. the
    reachable fragment did not stabilize within the budget). -/
inductive BatteryVerdict (S I : Type) where
  | proved
  | refuted (reason : BatteryReason S I)
  | unknown (reason : ExploreReason)
deriving BEq, Repr

/-! ## The reachable fragment (the deadlock sweep's substrate) -/

variable {S I : Type}

/-- The bounded frontier fold: rounds over the accumulated
    (state, tape) entries. SOME of the stabilized state list; NONE =
    the budget ran out before stabilization (the honest gap, reported
    — never laundered). An INSTANCE of Explore's `foldFrontier` (the
    ONE parameterized fold — the review's finding #4, consolidated):
    the state-projection observers `none` / `some ∘ map Prod.fst`
    against Explore's verdict observers `refutedOf` / `stabilizedOf`. -/
def reachableAux (m : Machine S I) (inputs : List I) [DecidableEq S] :
    Nat → List (S × List I) → Option (List S) :=
  foldFrontier m inputs (fun _ => none)
    (fun acc : List (S × List I) => some (acc.map Prod.fst))

/-- The reachable fragment of `m` from `init`, under input vocabulary
    `inputs`, within budget `fuel`. -/
def reachableStates (m : Machine S I) (inputs : List I) (init : S) (fuel : Nat)
    [DecidableEq S] : Option (List S) :=
  reachableAux m inputs fuel [(init, [])]

/-- THE FRONTIER NEVER LIES: every state the fold reports is genuinely
    reachable (the entries carry their tapes; the run tie). An INSTANCE
    of `foldFrontier_run` — the run skeleton proved once over the
    parameterized shape. -/
theorem reachableAux_run (m : Machine S I) (inputs : List I) [DecidableEq S]
    (init : S) :
    ∀ (fuel : Nat) (acc : List (S × List I)),
      (∀ p ∈ acc, m.run init p.2 = some p.1) →
      ∀ s ∈ (reachableAux m inputs fuel acc).getD [], m.Reachable init s := by
  intro fuel acc hacc
  refine foldFrontier_run m inputs init (fun _ => none)
    (fun acc : List (S × List I) => some (acc.map Prod.fst))
    (Q := fun o => ∀ s ∈ Option.getD o [], m.Reachable init s)
    (hbudget := fun _ _ s hs => by simp at hs)
    (hstable := fun a hacc' s hs => by
      obtain ⟨t, ht⟩ := by simpa using hs
      exact m.run_reachable init (hacc' (s, t) ht))
    fuel acc hacc

/-- STABILIZATION = COVERAGE: if the fold reports `some rs`, then every
    reachable state is IN `rs` — OR the fold returned `none` (the
    budget gap; the disjunction is the honesty, not a hedge). This is
    what upgrades a `.proved` deadlock verdict from "the visited
    states are clean" to "the reachable fragment is clean". An
    INSTANCE of `foldFrontier_coverage` + `closure_covers` — the
    stabilization⇒coverage induction proved once over the
    parameterized shape. -/
theorem reachableAux_complete (m : Machine S I) (inputs : List I)
    [DecidableEq S] (init : S) :
    ∀ (fuel : Nat) (acc : List (S × List I)), (init, []) ∈ acc →
      (∀ s i s', m.Reachable init s → m.step? s i = some s' → i ∈ inputs) →
      ∀ s, m.Reachable init s →
        s ∈ (reachableAux m inputs fuel acc).getD [] ∨
        reachableAux m inputs fuel acc = none := by
  intro fuel acc hseed hinputs
  refine foldFrontier_coverage m inputs init (fun _ => none)
    (fun acc : List (S × List I) => some (acc.map Prod.fst))
    (Q := fun o => ∀ s, m.Reachable init s →
      s ∈ Option.getD o [] ∨ o = none)
    (hbudget := fun _ _ s _ => Or.inr rfl)
    (hstable := fun a hseed hclosed s hr => by
      obtain ⟨t, ht⟩ := closure_covers m inputs init a hseed hclosed hinputs s hr
      exact Or.inl (List.mem_map.mpr ⟨(s, t), ht, rfl⟩))
    fuel acc hseed

/-! ## The three checks -/

/-- CHECK 1 — deadlock-freedom over the REACHABLE states: every
    reachable state satisfying the invariant has some enabled event
    (the completeness proof makes the `any` a total sweep, not a
    sample). Budget exhaustion is `.unknown`, never a verdict. -/
def deadlockFree (m : MachineWithInv S I) (inputs : List I) (init : S) (fuel : Nat)
    [DecidableEq S] [DecidablePred m.inv]
    (_hcomplete : ∀ i, i ∈ inputs) : BatteryVerdict S I :=
  match reachableStates m.toMachine inputs init fuel with
  | none => .unknown .budgetExhausted
  | some rs =>
      match rs.find? (fun s => decide (m.inv s) && !inputs.any (m.enabled s)) with
      | some s => .refuted (.wedged s)
      | none => .proved

/-- CHECK 2 — guard coverage: every event fires from at least one
    enumerated state; a never-enabled event is REFUTED with its label.
    The completeness proof is REQUIRED — without it, a missing label
    would skip a dead event entirely (the check would pass
    vacuously). -/
def guardCoverage (m : MachineWithInv S I) (inputs : List I) (states : List S)
    (_hcomplete : ∀ i, i ∈ inputs) : BatteryVerdict S I :=
  match inputs.find? (fun i => !states.any (fun s => m.enabled s i)) with
  | some i => .refuted (.dead i)
  | none => .proved

/-- CHECK 3 — invariant non-vacuity: the invariant excludes at least
    one enumerated state. (If your invariant is genuinely `True`, skip
    this check — call the two above directly.) -/
def invariantNonVacuous (m : MachineWithInv S I) (states : List S)
    [DecidablePred m.inv] : BatteryVerdict S I :=
  if states.any (fun s => !decide (m.inv s)) then .proved
  else .refuted .vacuous

/-- THE BATTERY, as named checks — one line per machine. The
    completeness proof threads into both sweeps (the `machine!`
    macro's generated `labels_complete` discharges it per machine —
    Machines.Dsl). -/
def battery (m : MachineWithInv S I) (inputs : List I) (states : List S)
    (init : S) (fuel : Nat) [DecidableEq S] [DecidablePred m.inv]
    (hcomplete : ∀ i, i ∈ inputs) : List (String × BatteryVerdict S I) :=
  [ ("deadlock-freedom", deadlockFree m inputs init fuel hcomplete)
  , ("guard-coverage", guardCoverage m inputs states hcomplete)
  , ("invariant-non-vacuity", invariantNonVacuous m states) ]

/-! ## The bridges (the verdicts' proposition-level reading) -/

/-- A `.proved` deadlock verdict MEANS: every reachable state
    satisfying the invariant has an enabled event. The bridge from
    the sweep to the proposition (pattern #1) — completeness feeds
    the coverage, soundness keeps the fragment honest. -/
theorem deadlockFree_proved (m : MachineWithInv S I) (inputs : List I)
    (init : S) (fuel : Nat) [DecidableEq S] [DecidablePred m.inv]
    (hcomplete : ∀ i, i ∈ inputs)
    (hinputs : ∀ s i s', m.toMachine.Reachable init s →
      m.toMachine.step? s i = some s' → i ∈ inputs)
    (h : deadlockFree m inputs init fuel hcomplete = .proved) :
    ∀ s, m.toMachine.Reachable init s → m.inv s → ∃ i, i ∈ inputs ∧ m.enabled s i := by
  intro s hr hinv
  -- the reachable fold either stabilized covering `s`, or hit the budget —
  -- but a `.proved` verdict rules the gap out
  have hcov := reachableAux_complete m.toMachine inputs init fuel [(init, [])]
    (by simp) hinputs s hr
  cases hrz : reachableAux m.toMachine inputs fuel [(init, [])] with
  | none =>
      exfalso
      simp only [reachableStates, hrz, deadlockFree] at h
      exact absurd h (by simp)
  | some rs =>
      rw [hrz, Option.getD_some] at hcov
      rcases hcov with hcov | hgap
      · -- the sweep's `find?` found nothing wedged
        have hfind :
            rs.find? (fun s => decide (m.inv s) && !inputs.any (m.enabled s)) = none := by
          simp only [deadlockFree, reachableStates, hrz] at h
          cases hf : rs.find? (fun s => decide (m.inv s) && !inputs.any (m.enabled s)) with
          | none => rfl
          | some s' => rw [hf] at h; simp at h
        -- so this state's sweep entry is false — but `m.inv s` forces the `any` true
        have hany : inputs.any (m.enabled s) = true := by
          cases hb : inputs.any (m.enabled s) with
          | false =>
              have hnot := List.find?_eq_none.mp hfind s hcov
              rw [hb] at hnot
              have hdec : decide (m.inv s) = true := decide_eq_true_eq.mpr hinv
              rw [hdec] at hnot
              simp at hnot
          | true => rfl
        exact List.any_eq_true.mp hany
      · exfalso
        simp at hgap

/-- A `.proved` guard-coverage verdict MEANS: every event (the sweep
    is complete by the caller's proof) is enabled somewhere. The bridge
    from the sweep to the proposition (pattern #1). -/
theorem guardCoverage_proved (m : MachineWithInv S I) (inputs : List I)
    (states : List S) (hcomplete : ∀ i, i ∈ inputs)
    (h : guardCoverage m inputs states hcomplete = .proved) :
    ∀ i, i ∈ inputs → ∃ s, s ∈ states ∧ m.enabled s i = true := by
  intro i hi
  have hfind : inputs.find? (fun i => !states.any (fun s => m.enabled s i)) = none := by
    simp only [guardCoverage] at h
    cases hf : inputs.find? (fun i => !states.any (fun s => m.enabled s i)) with
    | none => rfl
    | some i' =>
        rw [hf] at h
        simp at h
  have hnot := List.find?_eq_none.mp hfind i hi
  simp only [Bool.not_eq_true'] at hnot
  cases hb : states.any (fun s => m.enabled s i) with
  | false => rw [hb] at hnot; simp at hnot
  | true => exact List.any_eq_true.mp hb

/-- A `.refuted (.dead i)` verdict's WITNESS IS REAL: `i` is in the
    (complete) input list, and it is enabled NOWHERE in the
    enumeration — the dead code, caught. This is the teeth's proof
    content. -/
theorem guardCoverage_refuted (m : MachineWithInv S I) (inputs : List I)
    (states : List S) (hcomplete : ∀ i, i ∈ inputs) (i : I)
    (h : guardCoverage m inputs states hcomplete = .refuted (.dead i)) :
    i ∈ inputs ∧ ∀ s ∈ states, m.enabled s i = false := by
  have hfind : inputs.find? (fun i => !states.any (fun s => m.enabled s i)) = some i := by
    simp only [guardCoverage] at h
    cases hf : inputs.find? (fun i => !states.any (fun s => m.enabled s i)) with
    | none => rw [hf] at h; simp at h
    | some i' =>
        rw [hf] at h
        injection h with h1
        injection h1 with h2
        subst h2
        rfl
  refine ⟨List.mem_of_find?_eq_some hfind, fun s hs => ?_⟩
  have hp := List.find?_some hfind
  simp only [Bool.not_eq_true'] at hp
  simpa using List.any_eq_false.mp hp s hs

end Machines.Testing

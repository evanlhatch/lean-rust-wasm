/-
# Machines.Fusion — the machines ↔ deltas fusion bridges

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/01-core.md §2-3 (Change + TraceModel meet:
the journal IS the differentiation of the run; replay IS its
integration) + notes/v3/03-bidirectional.md §7 (the trichotomy: the
journal is EVENTS — recorded occurrences; the delta is the NET change;
net-zero ≠ nothing happened — the mandatory control is in
MachinesTests) + the legacy's proven content
(legacy/lean/Machines/Machines/Fusion.lean: the dI iso, journal = D∘run,
replay = I∘journal, bisimulation as stream equality — the "one
phenomenon" cluster, ported fresh).

## The adaptation notes (where the legacy's shape didn't fit)

- The legacy's `Machine` had an infinite-run time theory and mathlib
  `AddCommGroup` streams. The new substrate's `Machine.run` is
  Option-valued over finite tapes (Basic.lean), and the cone rule
  forbids mathlib. HONEST RESOLUTION: the bridge semantics is the
  TOTALIZED tick (`Machine.tick`: fire if enabled, else HOLD — the
  legacy's Sim convention), which makes the state stream a plain
  recursive function; the finite-tape `run`/`Exec`/`Reachable` views
  keep their own landed laws (Trace.lean) and are tied in below
  (`traceStates_exec`). The additive structure is the LANDED
  `Kit.Additive A A` (delta-as-state — the dbsp reading;
  `Kit.intAdd`/`ZSet.zsetAdditive` are its canonical occupants),
  consumed explicitly, never assumed as a mathlib class.
- The legacy's journal lived in `SchemaLang.EventSourced` (its Machines
  could not see the schema). Here the crossing is IN the machines
  layer, with the delta structure as an explicit parameter — the
  premise made honest: the machine's delta function is the NET-CHANGE
  function derived from the run (new `compose`- old `inv`), not a
  command family. A machine whose deltas are FIRST-CLASS COMMANDS
  (the EventSpec family) is the trichotomy's event face, and is NOT
  collapsed into Δ here — the net-zero control demonstrates the seam.
- The legacy's bisim bridge was stated on state-valued streams with no
  observer parameter. The new statement rides `Kit.Observer` (04 §4:
  "same behavior" is meaningless without naming the observer): the
  response stream and the response TRACE both carry one.

## The five questions

- **Root**: the Change ↔ TraceModel CROSSING (01-core §2-3) — every
  bridge here is a statement + glue over landed laws (the legacy's own
  description): no new inductions beyond the run-unfolding each bridge
  needs.
- **Carrier grade**: the `Machines.dI` Iso VALUE (Kit.Correspondence)
  for the stream crossing; pattern-#1 ties for the derived views
  (`traceStates_exec` ties the trace view to the landed `Exec.record`;
  `respTrace_exec` ties the bisim statement to it).
- **Spine reading**: none — a substrate module; the event-sourcing and
  dbsp lanes instantiate it.
- **Ladder rung**: hand theorems over the landed fold (rung 6 —
  relational content over `stateStream`'s recursion); the bisim
  equivalence's both directions are one-induction each.
- **Gate rows**: the axiom report pins in MachinesTests.Axioms.

## Named exclusions

- NO nondeterministic bisimulation (the general LTS story) — the
  deterministic tick-agreement notion is what this slice's machines
  support; the general form waits for its consumer (the legacy's own
  scoping).
- NO event-identity/dedup machinery for replay under reordering (03
  §7's signed-addition caveat) — lands with the first
  out-of-order-replay consumer.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Basic
import Machines.Trace
import Machines.Stream
import Kit.Observer
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Machines

/-! ## The totalized tick -/

namespace Machine

variable {S I : Type}

/-- One tick of the machine, TOTAL: fire the label if enabled, else
    hold (a blocked event is a no-op — the Sim convention, mined from
    the legacy's Fusion). This is the machine's step as a plain
    function — the state streams below are its iterates. -/
def tick (m : Machine S I) (l : I) (s : S) : S := (m.step? s l).getD s

/-- The tick agrees with the authoritative relation on every enabled
    step: `step?`-successful ticks ARE the step. -/
theorem tick_of_step (m : Machine S I) {s : S} {i : I} {s' : S}
    (h : m.step s i s') : m.tick i s = s' := by
  simp only [Machine.step] at h
  simp [Machine.tick, h]

end Machine

namespace Fusion

variable {S I A O : Type}

/-! ## The state stream (the run, as a stream) -/

/-- THE STATE STREAM: the machine's state at each time under the input
    stream `ins`, starting from `s`. Step `t` consumes input `ins t` —
    the totalized tick makes the semantics total, so this is the
    honest "run" as a stream (the legacy's `runFrom`/`respStream`
    shape, one-index flattened). -/
def stateStream (m : Machine S I) (ins : Stream I) (s : S) : Stream S :=
  fun t => match t with
    | 0 => s
    | t + 1 => m.tick (ins t) (stateStream m ins s t)

@[simp, nolint linter.guestlang.zeroCitation "public API: the lane's @[simp] unfolding laws (the stream faces' base/step)"] theorem stateStream_zero (m : Machine S I) (ins : Stream I) (s : S) :
    stateStream m ins s 0 = s := rfl

@[simp, nolint linter.guestlang.zeroCitation "public API: the lane's @[simp] unfolding laws (the stream faces' base/step)"] theorem stateStream_succ (m : Machine S I) (ins : Stream I) (s : S) (t : Nat) :
    stateStream m ins s (t + 1) = m.tick (ins t) (stateStream m ins s t) := rfl

/-! ## THE JOURNAL BRIDGE: journal = D ∘ run -/

/-- THE JOURNAL: entry `0` carries the initial value (the init
    snapshot); entry `t+1` is the tick's NET change — the new state
    `compose`- the old one, in the additive delta structure. The
    journal is event-shaped data (one recorded occurrence per tick),
    but its entries are NET deltas: the trichotomy (03 §7) is
    exercised by the net-zero control in MachinesTests — a journal
    can be net-zero without being the empty run's. -/
def journal (g : Kit.Additive A A) (m : Machine A I) (ins : Stream I) (s : A) :
    Stream A :=
  fun t => match t with
    | 0 => s
    | t + 1 =>
        g.compose (m.tick (ins t) (stateStream m ins s t))
          (g.inv (stateStream m ins s t))

@[simp, nolint linter.guestlang.zeroCitation "public API: the lane's @[simp] unfolding laws (the stream faces' base/step)"] theorem journal_zero (g : Kit.Additive A A) (m : Machine A I)
    (ins : Stream I) (s : A) : journal g m ins s 0 = s := rfl

@[simp, nolint linter.guestlang.zeroCitation "public API: the lane's @[simp] unfolding laws (the stream faces' base/step)"] theorem journal_succ (g : Kit.Additive A A) (m : Machine A I)
    (ins : Stream I) (s : A) (t : Nat) :
    journal g m ins s (t + 1)
      = g.compose (m.tick (ins t) (stateStream m ins s t))
          (g.inv (stateStream m ins s t)) := rfl

/-- **THE JOURNAL BRIDGE**: the journal IS the differentiation of the
    run — `journal = D ∘ stateStream` (the legacy's `journal = D ∘ run`,
    adapted to the totalized-tick semantics; see the adaptation notes).
    Glue over the landed definitions: no new induction. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem journal_eq_D_run (g : Kit.Additive A A) (m : Machine A I)
    (ins : Stream I) (s : A) :
    journal g m ins s = D g (stateStream m ins s) := by
  funext t
  cases t with
  | zero => rfl
  | succ t =>
      rw [journal_succ, D_succ, stateStream_succ]

/-! ## THE REPLAY BRIDGE: replay = I ∘ journal -/

/-- THE REPLAY: integrate the journal — the event-sourcing consumer's
    fold. -/
def replay (g : Kit.Additive A A) (m : Machine A I) (ins : Stream I) (s : A) :
    Stream A :=
  Machines.I g (journal g m ins s)

/-- **THE REPLAY BRIDGE**: replaying the journal reconstructs the
    state stream — `replay = I ∘ journal = run`. Rides the dI iso's
    `I ∘ D = id` law (Machines.I_D); no new induction. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem replay_eq_run (g : Kit.Additive A A) (m : Machine A I)
    (ins : Stream I) (s : A) :
    replay g m ins s = stateStream m ins s := by
  rw [replay, journal_eq_D_run]
  exact Machines.I_D g (stateStream m ins s)

/-! ## Bisimulation as stream equality (the observer-parameterized form) -/

/-- The response STATE stream: the post-tick state at each time (the
    initial state excluded — the legacy's `respStream` convention). -/
def respStateStream (m : Machine S I) (ins : Stream I) (s : S) : Stream S :=
  fun t => stateStream m ins s (t + 1)

/-- Tick-agreeing states have equal state streams (from time 1 on):
    the deterministic-bisimulation premise propagates through the
    totalized tick. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem stateStream_tick_agree (m : Machine S I) (s₁ s₂ : S)
    (h : ∀ l, m.tick l s₁ = m.tick l s₂) (ins : Stream I) :
    ∀ t, stateStream m ins s₁ (t + 1) = stateStream m ins s₂ (t + 1) := by
  intro t
  induction t with
  | zero => exact h (ins 0)
  | succ t ih =>
      show m.tick (ins (t + 1)) (stateStream m ins s₁ (t + 1))
         = m.tick (ins (t + 1)) (stateStream m ins s₂ (t + 1))
      rw [ih]

/-- **THE BISIMULATION BRIDGE** (the legacy's
    `bisim_iff_resp_streams`, stream level): two states are bisimilar —
    one-step tick-agreement, which for DETERMINISTIC machines is the
    classical bisimulation — iff their response streams are EQUAL on
    every input stream. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem bisim_iff_respStreams (m : Machine S I) (s₁ s₂ : S) :
    (∀ l, m.tick l s₁ = m.tick l s₂) ↔
      ∀ ins : Stream I, respStateStream m ins s₁ = respStateStream m ins s₂ := by
  constructor
  · intro h ins
    funext t
    exact stateStream_tick_agree m s₁ s₂ h ins t
  · intro h l
    simpa [respStateStream, stateStream] using congrFun (h (fun _ => l)) 0

/-- The response stream under an observer: what the observer sees of
    the post-tick states (04 §4: the observer is a parameter — the
    premise stays EXACT tick-agreement; the observer rides the
    conclusion, since observation-equality of one step's results does
    not make the successor states interchangeable). -/
def respStream (o : Kit.Observer S O) (m : Machine S I) (ins : Stream I) (s : S) :
    Stream O :=
  fun t => o.see (stateStream m ins s (t + 1))

/-- The observer corollary: tick-agreeing states are indistinguishable
    under ANY observer's response streams — the equality rides
    `Kit.Observer.see` directly. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem respStream_equiv (o : Kit.Observer S O) (m : Machine S I) (s₁ s₂ : S)
    (h : ∀ l, m.tick l s₁ = m.tick l s₂) (ins : Stream I) :
    respStream o m ins s₁ = respStream o m ins s₂ := by
  funext t
  rw [respStream, respStream, stateStream_tick_agree m s₁ s₂ h ins t]

/-! ## The trace face: same-step observability ⇒ same-trace-observability -/

/-- The state trace of a tape, in FORWARD order (initial state first):
    the tape-level sibling of `stateStream`. -/
def traceStates (m : Machine S I) (s : S) : List I → List S
  | [] => [s]
  | i :: t => s :: traceStates m (m.tick i s) t

@[simp, nolint linter.guestlang.zeroCitation "public API: the lane's @[simp] unfolding laws (the stream faces' base/step)"] theorem traceStates_nil (m : Machine S I) (s : S) :
    traceStates m s [] = [s] := rfl

@[simp, nolint linter.guestlang.zeroCitation "public API: the lane's @[simp] unfolding laws (the stream faces' base/step)"] theorem traceStates_cons (m : Machine S I) (s : S) (i : I) (t : List I) :
    traceStates m s (i :: t) = s :: traceStates m (m.tick i s) t := rfl

/-- THE TRACE TIE (over the landed Exec/Trace): the trace of an
    execution's tape is the initial state followed by the execution's
    post-states — the record's second projections. The stream/tape
    view and the witness-carrying `Exec` cannot drift. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem traceStates_exec (m : Machine S I) (s fin : S) (e : Exec m s fin) :
    traceStates m s e.tape = s :: e.record.map (fun p => p.2) := by
  induction e with
  | here => rfl
  | step i s' h r ih =>
      simp only [Exec.tape, Exec.record, traceStates_cons, List.map_cons]
      rw [m.tick_of_step h, ih]

/-- The observed RESPONSE trace: the post-step states' images, in
    order — what the observer sees of the run, initial state excluded
    (the trace-level `respStream`). -/
def respTrace (o : Kit.Observer S O) (m : Machine S I) (s : S) (t : List I) :
    List O :=
  (traceStates m s t).tail.map o.see

/-- The cons face: the response trace of a nonempty tape is the
    observed trace of the run from the ticked state. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of the test-pinned theorems (follow_runs/bounded_refines/taken_of_run/bisim_iff_respStreams)"]
theorem respTrace_cons (o : Kit.Observer S O) (m : Machine S I) (s : S) (i : I)
    (t : List I) :
    respTrace o m s (i :: t) = (traceStates m (m.tick i s) t).map o.see := rfl

/-- **THE TRACE BISIMULATION** (same-step observability ⇒
    same-trace-observability): tick-agreeing states produce identical
    observed response traces on EVERY tape. The trace face of the
    bisimulation bridge, over the landed tape view. The proof is pure
    glue: the first tick lands on EQUAL states (the premise is exact),
    so the successor traces agree by congruence. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem respTrace_tick_agree (o : Kit.Observer S O) (m : Machine S I) (s₁ s₂ : S)
    (h : ∀ l, m.tick l s₁ = m.tick l s₂) :
    ∀ (t : List I), respTrace o m s₁ t = respTrace o m s₂ t := by
  intro t
  cases t with
  | nil => rfl
  | cons i rest =>
      rw [respTrace_cons, respTrace_cons,
        congrArg (traceStates m) (h i)]

/-- The trace face tied to the landed Exec: the observed response trace
    of an execution's tape IS the record's observed image (the audit
    trail, read through the observer). -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by the lane's tests (MachinesTests #print axioms / the session-machine pins)"]
theorem respTrace_exec (o : Kit.Observer S O) (m : Machine S I) (s fin : S)
    (e : Exec m s fin) :
    respTrace o m s e.tape = e.record.map (fun p => o.see p.2) := by
  simp only [respTrace]
  rw [traceStates_exec]
  simp [List.map_map]

end Fusion

end Machines

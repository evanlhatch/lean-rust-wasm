/-
# Contracts.WpMachine — the wp↔machine bridge (wave 30, A4)

The contracts lane's execution semantics (`Prog.exec`) restated as
`Machines.Machine` instances (the TraceModel root, notes/v3/01-core.md
§3), and `wp_sound` restated as the SIMULATION between the wp
semantics and the machine's executions — the bridge's honest shape:
**the wp's soundness implies the machine-level safety**, and a wrong
invariant/variant stays unconstructible (the premise is the `LoopVCs`
row, which a wrong invariant/variant cannot populate — the teeth in
ContractsTests).

Two machines, one carrier each:

- `progMachine` — the fragment's executor: state = the value+state
  pair (the value-returning discipline's carrier), input = a `Prog`,
  the step relation the graph of `Prog.exec` (pattern #1: both bridge
  directions by definition, so the readings cannot drift). The run's
  cons law IS the exec-side composition (`wp_bind`'s face).
- `loopMachine` — the while carrier: input `Bool` — `true` = the
  continue-step (ENABLED only when the guard holds — claiming
  "continue" against a false guard is refused, `none`, the honest
  refusal), `false` = the exit-step (the loop's normal termination,
  a no-op landing). The machine's runs ARE the loop's executions.

THE BRIDGE (the four-VC structure ↔ the machine's reachable-states
discipline): `LoopVCs` (init / preserve / descend / exit) maps onto
the loop machine's executions —

- `loopvc_run_inv` + `loopvc_reachable_inv` — PRESERVE at the machine
  level: every machine-reachable state satisfies the invariant (or has
  already exited); the engine is `wp_sound` THROUGH `vBody` — the
  wp's soundness is the invariant's propagation; a wrong invariant
  cannot populate the `LoopVCs` row (the teeth in ContractsTests), so
  the theorem has no reachable counterexample;
- `loopvc_variant_bounds` — DESCEND at the machine level: the machine
  REFUSES a continue-run longer than the variant allows (the run over
  `var s + 1` continue-steps is `none`) — the variant is the
  termination certificate, the machine reads it as a bound on its own
  executions;
- `loopvc_exit_machine` — INIT + EXIT at the machine level: some
  continue-run of length ≤ the variant, closed by the exit-step,
  lands in the postcondition — `while_sat`'s machine-level face.

THE SIMULATION: `wpSim` — the wp semantics' verified steps are
simulated by the machine's steps along the state tie (R = the
diagonal; the sim law is the executor's determinism, by definition).
Its graph is `Kit.Simulation.toRel` — the carrier-as-graph bridge's
Simulation grade, the same bridge the duel restatement rides
(WasmCore.ExecMachine). The CONTENT is `wp_machine_safe`: from a
wp-verified state, EVERY machine step lands in the postcondition —
`wp_sound` at the machine interface (cited, never re-proved).

The five questions (notes/v3/01-core.md):

- **Root**: TraceModel (01-core §3) — the fragment's behavior as the
  machines' executions; the four VCs are the reachable-states
  discipline's faces, each a theorem tied to the machine's `run`/
  `Reachable`.
- **Carrier grade**: pattern #1 at the fragment level + the
  Simulation grade (the one-step law IS the bridge; the safety
  corollary consumes `wp_sound`).
- **Spine reading**: none — the fragment's contracts ride `Wp`; the
  machine reading adds no artifacts.
- **Ladder rung**: rung 6 — the reachable/variant/exit theorems are
  hand inductions with named relational content (the descent's
  arithmetic rides `omega`); the step ties are definitional/cited.
- **Gate row**: Contracts' row in Gates.Packages' gated set (the
  per-library axiom sweep covers this module through the umbrella);
  ContractsTests' machine suite pins the bridge + the controls.

Named exclusions (the honest ledger): NO nondeterministic fragment
(the wp is a transformer over a deterministic exec; a relational wp
lands with its consumer); NO invariant inference (the invariant is
required data on the carrier — the toolkit computes nothing it
cannot); the nested-loop discipline waits for its first consumer.

Core-only: imports `Contracts.Wp` + `Machines.Basic` +
`Kit.Correspondence` (the cone rule; no mathlib, no Batteries).
-/

import Contracts.Wp
import Machines.Basic
import Kit.Correspondence

namespace Contracts

/-! ## The fragment's machine -/

/-- THE FRAGMENT'S MACHINE: the state is the value+state pair (the
    value-returning discipline's carrier), the input a `Prog`, the
    step relation the graph of `Prog.exec`. Total: the fragment has
    no refusals — every step applies. -/
def progMachine : Machines.Machine (Nat × State) Prog :=
  ⟨fun xs p => some (p.exec xs.2)⟩

/-- THE STEP BRIDGE (pattern #1): the machine's step relation is the
    graph of `Prog.exec` — both directions by definition. -/
theorem prog_step_iff (xs xs' : Nat × State) (p : Prog) :
    progMachine.step xs p xs' ↔ xs' = p.exec xs.2 := by
  constructor
  · intro h
    simp only [Machines.Machine.step, progMachine] at h
    exact (Option.some.inj h).symm
  · intro h
    simp only [Machines.Machine.step, progMachine, h]

/-- The machine's cons law IS the exec-side composition: running the
    program then the tail = the tail from the program's exit pair
    (`wp_bind`'s exec face; `Prog.exec_bind` cited). -/
theorem prog_run_cons (xs : Nat × State) (p : Prog) (t : List Prog) :
    progMachine.run xs (p :: t) = progMachine.run (p.exec xs.2) t := by
  show progMachine.run xs (p :: t) = _
  rw [Machines.Machine.run_cons]
  rfl

/-! ## The wp↔machine simulation -/

/-- THE WP↔MACHINE SIMULATION: the wp semantics' verified steps (the
    exec under the wp premise) are simulated by the machine's steps
    along the state tie — R = the diagonal, the sim law is the
    executor's determinism (by definition). The graph is
    `Kit.Simulation.toRel` (the carrier-as-graph bridge's Simulation
    grade); the CONTENT is `wp_machine_safe` below — `wp_sound` at
    the machine interface. -/
def wpSim (p : Prog) : Kit.Simulation (Nat × State) (Nat × State) where
  stepA xs xs' := xs' = p.exec xs.2
  stepB xs xs' := progMachine.step xs p xs'
  R xs xs' := xs = xs'
  sim xs xs' xs₂ h hs := by
    rw [h] at hs
    exact ⟨p.exec xs₂.2, hs, by
      show progMachine.step xs₂ p (p.exec xs₂.2)
      simp [progMachine, Machines.Machine.step]⟩

/-- The simulation's graph IS the diagonal — the bridge's unit row's
    shape at the carrier (cited, not re-proved). -/
theorem wpSim_toRel (p : Prog) (a b : Nat × State) :
    (wpSim p).toRel a b ↔ a = b := by
  constructor
  · intro h; exact h
  · intro h; exact h

/-- THE MACHINE-LEVEL SAFETY (the bridge's content): from a
    wp-verified state, EVERY machine step of the program lands in the
    postcondition — `wp_sound` at the machine interface (cited, never
    re-proved). A wrong program/postcondition pair fails the wp side,
    and the machine then exposes the violating state as DATA. -/
theorem wp_machine_safe (p : Prog) (Q : Nat → State → Prop) (x : Nat) (s : State)
    (h : wp p Q s) (xs' : Nat × State) (hstep : progMachine.step (x, s) p xs') :
    Q xs'.1 xs'.2 := by
  rw [prog_step_iff] at hstep
  subst hstep
  exact wp_sound p Q s h

/-- The state-only face at the two-step run: the sequential
    composition's machine run lands in the postcondition whenever the
    wp-computed precondition holds (`wp_seq` + `wp_sound` at the
    machine's two-step run). -/
theorem wp_seq_machine_safe (p q : Prog) (Q : State → Prop) (s : State)
    (h : wpS (p.seq q) Q s) :
    ∀ xs', progMachine.run (0, s) [p, q] = some xs' → Q xs'.2 := by
  intro xs' hrun
  have hrun' : progMachine.run (0, s) [p, q] = some (q.exec (p.exec s).2) := by
    show progMachine.run (0, s) [p, q] = _
    rw [prog_run_cons, prog_run_cons]
    rfl
  rw [hrun'] at hrun
  have hs' : q.exec (p.exec s).2 = xs' := Option.some.inj hrun
  subst hs'
  have h2 : Q ((p.seq q).exec s).2 :=
    wp_sound (p.seq q) (fun _ s'' => Q s'') s h
  have hseq : ((p.seq q).exec s).2 = (q.exec (p.exec s).2).2 := rfl
  rw [hseq] at h2
  exact h2

/-! ## The while machine + the four VCs at the machine level -/

/-- THE WHILE MACHINE: the loop carrier as a `Machines.Machine` — the
    input is the guard's answer: `true` = the continue-step (the
    body's exec; ENABLED only when the guard holds — claiming
    "continue" against a false guard is refused, the honest `none`),
    `false` = the exit-step (the loop's normal termination, the no-op
    landing). -/
def loopMachine (w : While) : Machines.Machine State Bool :=
  ⟨fun s b =>
    match b with
    | true => match w.guard s with
      | true => some (w.body.exec s).2
      | false => none
    | false => some s⟩

/-- The continue-step's bridge: enabled exactly at a guard-true
    state, landing on the body's exit state. -/
theorem loop_step_true_iff (w : While) (s s' : State) :
    (loopMachine w).step s true s' ↔ w.guard s = true ∧ s' = (w.body.exec s).2 := by
  constructor
  · intro h
    simp only [Machines.Machine.step, loopMachine] at h
    split at h
    · rename_i hg
      exact ⟨hg, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · intro h
    simp only [Machines.Machine.step, loopMachine, h.1, h.2]

/-- The exit-step's bridge: the no-op landing. -/
theorem loop_step_false_iff (w : While) (s s' : State) :
    (loopMachine w).step s false s' ↔ s' = s := by
  constructor
  · intro h
    simp only [Machines.Machine.step, loopMachine] at h
    exact (Option.some.inj h).symm
  · intro h
    simp only [Machines.Machine.step, loopMachine, h]

/-- The exit-step's run face: the machine run over the exit-step is
    the no-op landing. -/
theorem loop_run_false (w : While) (s : State) :
    (loopMachine w).run s [false] = some s := by
  show (loopMachine w).run s [false] = _
  rw [Machines.Machine.run_cons]
  rfl

/-- The continue-run's reduction (the guard holds): the machine's
    continue-step IS the `While.run` fuel-step — the machine's runs
    and the wp lane's fuel-bounded execution are the same runs. -/
theorem loop_run_true_cons (w : While) (s : State) (hg : w.guard s = true)
    (t : List Bool) :
    (loopMachine w).run s (true :: t) = (loopMachine w).run ((w.body.exec s).2) t := by
  show (loopMachine w).run s (true :: t) = _
  rw [Machines.Machine.run_cons]
  simp only [loopMachine, hg]
  rfl

/-- PRESERVE at the machine level (the bridge's reachable-states
    face, run form): a machine run from an invariant state lands in
    an invariant state (or one whose guard already exited). The
    engine is `wp_sound` THROUGH `vBody` — the wp's soundness is the
    invariant's propagation; a wrong invariant cannot populate the
    `LoopVCs` row (the teeth in ContractsTests), so this theorem has
    no reachable counterexample. -/
theorem loopvc_run_inv (P Q : State → Prop) (w : While) (v : LoopVCs P Q w) :
    ∀ (t : List Bool) (s s' : State), (loopMachine w).run s t = some s' →
      w.inv s → w.inv s' ∨ w.guard s' = false := by
  intro t
  induction t with
  | nil =>
      intro s s' hrun hinv
      rw [Machines.Machine.run_nil] at hrun
      have hs' : s = s' := Option.some.inj hrun
      subst hs'
      exact Or.inl hinv
  | cons b rest ih =>
      intro s s' hrun hinv
      rw [Machines.Machine.run_cons] at hrun
      obtain ⟨s₁, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hrun
      cases b with
      | true =>
          have hg : w.guard s = true ∧ s₁ = (w.body.exec s).2 :=
            (loop_step_true_iff w s s₁).mp hstep
          have hb : wp w.body (fun _ s' => w.inv s') s := v.vBody s hg.1 hinv
          have hinv1 : w.inv ((w.body.exec s).2) :=
            wp_sound w.body (fun _ s' => w.inv s') s hb
          rw [← hg.2] at hinv1
          exact ih s₁ s' hrest hinv1
      | false =>
          have hs1 : s₁ = s := (loop_step_false_iff w s s₁).mp hstep
          rw [hs1] at hrest
          exact ih s s' hrest hinv

/-- PRESERVE at the machine level (the reachable view): every
    machine-REACHABLE state from an invariant state satisfies the
    invariant (or has already exited) — the run view's face above
    transported through the machines' two-direction tie
    (`Machines.Machine.reachable_run`, cited). -/
theorem loopvc_reachable_inv (P Q : State → Prop) (w : While) (v : LoopVCs P Q w)
    (s : State) (hP : P s) (s' : State)
    (hr : Machines.Machine.Reachable (loopMachine w) s s') :
    w.inv s' ∨ w.guard s' = false := by
  obtain ⟨t, hrun⟩ := Machines.Machine.reachable_run hr
  exact loopvc_run_inv P Q w v t s s' hrun (v.vInit s hP)

/-- DESCEND at the machine level (the variant as the termination
    certificate): the machine REFUSES a continue-run longer than the
    variant allows — the run over `var s + 1` continue-steps is
    `none` (the honest disabled refusal, never a fabricated state).
    The engine is `wp_sound` through `vBody` + the descent's
    arithmetic through `vVar`. -/
theorem loopvc_variant_bounds (P Q : State → Prop) (w : While) (v : LoopVCs P Q w) :
    ∀ (m : Nat) (s : State), w.inv s → w.var s < m →
      (loopMachine w).run s (List.replicate m true) = none := by
  intro m
  induction m with
  | zero => intro s _ hv; exact absurd hv (by omega)
  | succ n ih =>
      intro s hinv hv
      rw [List.replicate_succ, Machines.Machine.run_cons]
      cases hg : w.guard s with
      | false =>
          have hstep : (loopMachine w).step? s true = none := by
            simp only [loopMachine, hg]
          rw [hstep, Option.bind_none]
      | true =>
          have hstep : (loopMachine w).step? s true = some ((w.body.exec s).2) := by
            simp only [loopMachine, hg]
          have hb : wp w.body (fun _ s' => w.inv s') s := v.vBody s hg hinv
          have hinv' : w.inv ((w.body.exec s).2) :=
            wp_sound w.body (fun _ s' => w.inv s') s hb
          have hv' := (v.vVar s hg hinv).2
          rw [hstep, Option.bind_some]
          rw [ih ((w.body.exec s).2) hinv' (by omega)]

/-- INIT + EXIT at the machine level (`while_sat`'s machine face):
    some continue-run of length ≤ the variant, closed by the
    exit-step, lands in the postcondition — the machine's executions
    are bounded by the variant AND end in Q. The engine is
    `while_sound_fuel`'s structure (which consumes `wp_sound` through
    `vBody`); a wrong invariant/variant cannot populate the `LoopVCs`
    row, so the machine-level safety has no counterexample. -/
theorem loopvc_exit_machine (P Q : State → Prop) (w : While) (v : LoopVCs P Q w) :
    ∀ (N : Nat) (s : State), w.inv s → w.var s ≤ N →
      ∃ (k : Nat) (s' : State), k ≤ N ∧
        (loopMachine w).run s (List.replicate k true ++ [false]) = some s' ∧ Q s' := by
  intro N
  induction N with
  | zero =>
      intro s hinv hv
      have hg : w.guard s = false := by
        cases hb : w.guard s with
        | false => rfl
        | true => exact absurd hv (by have := (v.vVar s hb hinv).1; omega)
      exact ⟨0, s, by omega, by
        show (loopMachine w).run s ([] ++ [false]) = _
        rw [List.nil_append]
        exact loop_run_false w s, v.vExit s hinv hg⟩
  | succ n ih =>
      intro s hinv hv
      cases hg : w.guard s with
      | false =>
          exact ⟨0, s, by omega, by
            show (loopMachine w).run s ([] ++ [false]) = _
            rw [List.nil_append]
            exact loop_run_false w s, v.vExit s hinv hg⟩
      | true =>
          have hb : wp w.body (fun _ s' => w.inv s') s := v.vBody s hg hinv
          have hinv' : w.inv ((w.body.exec s).2) :=
            wp_sound w.body (fun _ s' => w.inv s') s hb
          have hv' := (v.vVar s hg hinv).2
          obtain ⟨k, s', hk, hrun, hQ⟩ := ih ((w.body.exec s).2) hinv' (by omega)
          refine ⟨k + 1, s', by omega, ?_, hQ⟩
          show (loopMachine w).run s (true :: (List.replicate k true ++ [false])) = _
          rw [loop_run_true_cons w s hg]
          exact hrun

end Contracts

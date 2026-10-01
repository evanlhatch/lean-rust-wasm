/-
# Machines.Live — the coinductive foundation + the liveness vocabulary

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/08-capabilities.md §10 (the liveness lane:
eventually / always-eventually / until over the machine, with
counterexample traces as data and the honest trichotomy everywhere) +
notes/v3/01-core.md §3 (the TraceModel's honest corrections: FAIRNESS
IS AN ENVIRONMENT ASSUMPTION, never derived from the transition table;
bounded exploration answers proved/refuted/unknown) + 16-surface §4.2
(the landed finality — behavioral equality IS bisimilarity — proved
WITHOUT coinductive types, by time-shifted induction over FINITE
observations).

## THE COINDUCTIVE FOUNDATION meets the landed discipline (the honest
relationship)

`Machines.Coalg` landed the finality theorem over the STREAM carrier:
`beh` equality is pointwise equality at every finite time, and the
coinduction principle is the time-shifted INDUCTION. Lean 4.25+'s
`coinductive` command now lands the INFINITE face directly: `InfRun` —
the machine's infinite execution as the greatest fixed point of the
step relation (zero kernel extensions: the command compiles to
`Lean.Order`'s lfp/gfp machinery; the axiom surface stays the core
triple — pinned in MachinesTests.Live).

The two disciplines MEET in the bridges:

- `InfRun.head` — the infinite run's every step fires (the gfp
  unfolding), so its every FINITE observation is honest (`beh` never
  sees a refusal: `beh_some_of_infRun`);
- `infRun_of_states_fires` — the landed unfold (`Coalgebra.states`,
  hold-on-refusal) crossing to the infinite face: if the states stream
  fires at every time, the run is infinite (Park induction = the
  bisimulation proof principle);
- `InfRun.of_explore` — the bounded exploration's PROVED face
  (stabilization + the coverage premise, 01-core §3) with the
  environment's supply gives the infinite run. The UNKNOWN face
  bridges to NOTHING — budget exhaustion is the honest gap.

## The liveness vocabulary (08 §10)

- `Eventually P c ins s` — the FINITE face: the hold-states stream
  reaches `P`.
- `Fairness c ins s` — THE ASSUMPTION AS DATA: the environment's
  promise that the run keeps firing, carried as a hypothesis the
  caller supplies — never derived (01-core §3's correction).
  `Fairness.infRun`: the assumption IS the infinite run.
- `InfOften` / `AlwaysEventually` — the INFINITE face, coinductive:
  `P` at infinitely many times; the Park principle (`InfOften.park`)
  is its proof discipline; `AlwaysEventually.eventually` ties it back
  to the finite face.

Named exclusions: NO `until` (its bounded-B face is an inductive
fixpoint, a different discipline — lands with its first consumer); NO
general weak/strong fairness (JT/justice vs compassion) — the single
`Fairness` datum is what the finite machines here can honestly carry.

Core-only: no mathlib, no Batteries (the cone rule).
-/
module

public import Machines.Basic
public import Machines.Stream
public import Machines.Coalg
public import Machines.Explore
@[expose] public section


namespace Machines

/-! ## The coinductive foundation: the infinite run -/

/-- THE COINDUCTIVE FOUNDATION: `InfRun m ins s` — executing the input
    stream `ins` from state `s` NEVER refuses. The machine's infinite
    execution as the greatest fixed point of the step relation: the
    `step` constructor is the guarded intro rule, and `InfRun.coinduct`
    (generated, cited below as `InfRun.park`) is the Park induction —
    the bisimulation proof principle. Zero kernel extensions: the
    `coinductive` command compiles to `Lean.Order`'s fixpoint
    machinery; the axiom surface stays the core triple. -/
coinductive InfRun {S I : Type} (m : Machine S I) : Stream I → S → Prop where
  | step (ins : Stream I) {s s' : S} :
      m.step? s (ins 0) = some s' →
      InfRun m (fun u => ins (u + 1)) s' → InfRun m ins s

namespace InfRun

variable {S I : Type} {m : Machine S I} {ins : Stream I} {s : S}

/-- The full step inversion: an infinite run fires now and continues
    forever — the gfp's unfolding, one step at a time. (The generated
    `functor_unfold` + `_functor.existential_equiv` pair IS the
    greatest-fixed-point equation; this packages it.) -/
theorem step_inv (h : InfRun m ins s) :
    ∃ s', m.step? s (ins 0) = some s' ∧ InfRun m (fun u => ins (u + 1)) s' := by
  rw [InfRun.functor_unfold, InfRun._functor.existential_equiv] at h
  exact h

/-- THE PARK INDUCTION (the bisimulation proof principle): a relation
    `Q` between input streams and states that (i) holds at `(ins, s)`
    and (ii) is STEP-CLOSED — every `Q`-pair fires into a `Q`-pair one
    step on — puts `(ins, s)` in the greatest fixed point. This is the
    coinductive twin of `Coalgebra.bisim_sound`'s time-shifted
    induction: there the relation is kept invariant by hand, here the
    greatest fixed point does the bookkeeping. -/
theorem park (Q : Stream I → S → Prop) (hQ : Q ins s)
    (hstep : ∀ (is : Stream I) (x : S), Q is x →
      ∃ s', m.step? x (is 0) = some s' ∧ Q (fun u => is (u + 1)) s') :
    InfRun m ins s :=
  InfRun.coinduct m Q hstep ins s hQ

/-- THE STEP FACE (the gfp unfolding): an infinite run's next step
    fires. The destructive reading of the greatest fixed point — the
    one observation the finite face can demand of the infinite. -/
theorem head (h : InfRun m ins s) : ∃ s', m.step? s (ins 0) = some s' := by
  obtain ⟨s', h1, _⟩ := h.step_inv
  exact ⟨s', h1⟩

/-- The refusal tooth: a run whose next step refuses is NOT infinite —
    the refusal is data, and the greatest fixed point sees it. -/
theorem refuses (h : InfRun m ins s) : m.step? s (ins 0) ≠ none := by
  obtain ⟨s', h1⟩ := h.head
  intro hn
  rw [hn] at h1
  simp at h1

end InfRun

/-! ### The bridges: the landed unfold meets the infinite face -/

variable {S I O : Type}

/-- THE UNFOLD BRIDGE, forward: an infinite run fires at EVERY time of
    the landed `Coalgebra.states` stream — the infinite face's finite
    observations are exactly the unfold's, one per time. -/
theorem states_fires_of_infRun (c : Coalgebra S I O) {ins : Stream I} {s : S}
    (h : InfRun c.machine ins s) :
    ∀ t, ∃ s', c.machine.step? (c.states ins s t) (ins t) = some s' := by
  intro t
  induction t generalizing ins s with
  | zero => exact h.head
  | succ t ih =>
      obtain ⟨b, hb, h2⟩ := h.step_inv
      have hobs : c.observe s (ins 0) = some (c.observer.see b, b) := by
        simp [Coalgebra.observe, hb]
      rw [c.states_shift ins s t, c.next_of_some hobs]
      obtain ⟨s'', hs''⟩ :=
        ih (ins := fun u => ins (u + 1)) (s := b) h2
      exact ⟨s'', by simpa using hs''⟩

/-- THE UNFOLD BRIDGE, backward: a states stream that fires at every
    time IS an infinite run — the Park induction at work. Together with
    `states_fires_of_infRun`: the infinite run is EXACTLY the
    never-refusing unfold, one discipline in two faces. -/
theorem infRun_of_states_fires (c : Coalgebra S I O) (ins : Stream I) (s : S)
    (h : ∀ t, ∃ s', c.machine.step? (c.states ins s t) (ins t) = some s') :
    InfRun c.machine ins s := by
  apply InfRun.park
    (fun is x => ∃ t, x = c.states ins s t ∧ ∀ u, is u = ins (t + u))
  · exact ⟨0, rfl, fun _ => by simp⟩
  · rintro is x ⟨t, rfl, his⟩
    obtain ⟨s', hstep⟩ := h t
    have hobs : c.observe (c.states ins s t) (ins t)
        = some (c.observer.see s', s') := by
      simp [Coalgebra.observe, hstep]
    refine ⟨s', ?_, ?_⟩
    · rw [his 0, Nat.add_zero]
      exact hstep
    · refine ⟨t + 1, ?_, fun u => ?_⟩
      · rw [c.states_succ ins s t, c.next_of_some hobs]
      · show is (u + 1) = ins (t + 1 + u)
        rw [his (u + 1)]
        have hix : t + (u + 1) = t + 1 + u := by omega
        rw [hix]

/-- THE FINALITY BRIDGE: under an infinite run, the landed behavior
    stream never sees a refusal — every finite time yields SOME
    observation. The landed finality (`behEq_iff_bisim`) compares
    observation streams pointwise; this is where its carrier meets the
    infinite face honestly: the finite observations are ALL of what the
    infinite run shows, and they are all `some`. -/
theorem beh_some_of_infRun (c : Coalgebra S I O) {ins : Stream I} {s : S}
    (h : InfRun c.machine ins s) :
    ∀ t, ∃ o, c.beh ins s t = some o := by
  intro t
  obtain ⟨s', hstep⟩ := states_fires_of_infRun c h t
  refine ⟨c.observer.see s', ?_⟩
  rw [c.beh_eq, Coalgebra.observe, hstep]
  rfl

/-! ## The Explore integration: the PROVED face crosses, UNKNOWN does not -/

/-- THE EXPLORE INTEGRATION: the bounded exploration's PROVED face for
    the enabledness invariant (`i₀` is enabled at every reachable
    state) plus the environment's constant supply gives the coinductive
    infinite run — the Park induction over the reachable fragment. The
    UNKNOWN face (budget exhaustion) bridges to NOTHING: the honest gap
    is a gap (01-core §3); only stabilization + coverage crosses. -/
theorem InfRun.of_explore {m : Machine S I} {i₀ : I} {inputs : List I}
    {init : S} {budget : Nat} [DecidableEq S]
    (hproved : check m (fun x => (m.step? x i₀).isSome) inputs init budget = .proved)
    (hcov : ∀ s i s', m.Reachable init s → m.step s i s' → i ∈ inputs) :
    InfRun m (fun _ => i₀) init := by
  apply InfRun.park
    (fun is x => (∀ u, is u = i₀) ∧ m.Reachable init x)
  · exact ⟨fun _ => rfl, Machine.Reachable.here⟩
  · rintro is x ⟨his, hx⟩
    rw [his 0]
    have hen := check_proved m (fun x => (m.step? x i₀).isSome) inputs init
      budget hproved hcov x hx
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hen
    exact ⟨s', hs', fun u => show (fun u => is (u + 1)) u = i₀ from his (u + 1),
      Machine.Reachable.step i₀ hs' hx⟩

/-! ## The liveness vocabulary (08 §10) -/

/-- `Eventually P c ins s`: the run's hold-states stream reaches `P` —
    the FINITE face of the liveness vocabulary. `P` is read on the
    STATE (the hold-on-refusal convention keeps the stream total; what
    the state does under refusal is the fairness question below). -/
def Eventually (P : S → Prop) (c : Coalgebra S I O) (ins : Stream I) (s : S) : Prop :=
  ∃ t, P (c.states ins s t)

/-- THE FAIRNESS ASSUMPTION, AS DATA (01-core §3's correction: fairness
    is an environment ASSUMPTION, never derived from the transition
    table). The caller supplies the witness: at every time of the run,
    the environment's next input is enabled. Nothing derives it — a
    machine whose table cannot keep firing under `ins` simply has no
    `Fairness` value to name (the teeth in MachinesTests.Live). -/
structure Fairness (c : Coalgebra S I O) (ins : Stream I) (s : S) : Prop where
  keepsFiring : ∀ t, ∃ s', c.machine.step? (c.states ins s t) (ins t) = some s'

/-- THE ASSUMPTION IS THE RUN: the fairness datum (as data) feeds the
    unfold bridge — assuming fairness IS assuming the infinite run.
    This is the honest direction: the run is never derived from the
    table alone, only from table + assumption. -/
theorem Fairness.infRun {c : Coalgebra S I O} {ins : Stream I} {s : S}
    (f : Fairness c ins s) : InfRun c.machine ins s :=
  infRun_of_states_fires c ins s f.keepsFiring

/-! ### The infinite face: always-eventually -/

/-- THE INFINITE FACE, time-indexed: `P` holds at infinitely many
    times — the coinductive always-eventually. The `step` constructor
    is the guarded intro (P now-or-soon, the rest continues later);
    `InfOften.coinduct` (cited as `InfOften.park`) is the proof
    discipline. -/
coinductive InfOften (P : Nat → Prop) : Nat → Prop where
  | step (t : Nat) : {u : Nat} → P (t + u) → InfOften P (t + u + 1) → InfOften P t

namespace InfOften

/-- THE PARK INDUCTION for the time-indexed face: a step-closed `Q`
    puts its time in the greatest fixed point. -/
theorem park {P : Nat → Prop} {t : Nat} (Q : Nat → Prop) (hQ : Q t)
    (hstep : ∀ t, Q t → ∃ u, P (t + u) ∧ Q (t + u + 1)) : InfOften P t :=
  InfOften.coinduct P Q hstep t hQ


/-- The step face: infinitely often means AT LEAST once — some time
    witnesses `P`. -/
theorem some_time {P : Nat → Prop} {t : Nat} (h : InfOften P t) : ∃ t', P t' := by
  rw [InfOften.functor_unfold, InfOften._functor.existential_equiv] at h
  obtain ⟨u, h1, _⟩ := h
  exact ⟨t + u, h1⟩


end InfOften

/-- THE INFINITE FACE over a run: `P` holds at infinitely many times of
    the run — 08 §10's always-eventually. -/
def AlwaysEventually (P : S → Prop) (c : Coalgebra S I O) (ins : Stream I)
    (s : S) : Prop :=
  InfOften (fun t => P (c.states ins s t)) 0

/-- THE FACE TIE: the infinite face implies the finite one — infinitely
    often is at least once. -/
theorem AlwaysEventually.eventually {P : S → Prop} {c : Coalgebra S I O}
    {ins : Stream I} {s : S} (h : AlwaysEventually P c ins s) :
    Eventually P c ins s := by
  obtain ⟨t, ht⟩ := h.some_time
  exact ⟨t, ht⟩

/-! ### The honest gap: refusal holds, and the gap is honest -/

/-- THE GAP (01-core §3): from a state whose EVERY step refuses, the
    hold-stream never leaves `s` — so `P` off `s` is never reached. The
    environment that names only refused inputs gets an honest REFUTED
    eventually, never a laundered verdict. -/
theorem not_eventually_of_allRefuse (c : Coalgebra S I O) (P : S → Prop)
    (ins : Stream I) (s : S) (h0 : ¬ P s) (hhold : ∀ i, c.machine.step? s i = none) :
    ¬ Eventually P c ins s := by
  rintro ⟨t, ht⟩
  have hobs : ∀ i, c.observe s i = none := fun i =>
    by simp [Coalgebra.observe, hhold i]
  have hold : ∀ t, c.states ins s t = s := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [c.states_succ, ih, c.next_of_none (hobs (ins t))]
  rw [hold t] at ht
  exact h0 ht

end Machines

end -- public section

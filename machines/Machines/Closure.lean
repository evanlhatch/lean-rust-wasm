/-
# Machines.Closure — the frontier fold = the Datalog closure (the bridge)

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/02-data-plane.md §9 (the closure reading:
the machines' exploration IS a relational closure — one phenomenon, two
engines) + notes/v3/16-surface.md's dissolution discipline (the graph /
closure reading is ONE thing) + notes/v3/15-patterns.md #1
(relation-as-spec + executable checker + proved bridge — here at the
CROSS-LIBRARY level: the machine's `step?` checker vs the Datalog LFP
spec, and the two ENGINES tied).

## The two engines, one phenomenon

- `Machines.Explore.foldFrontier` — the parameterized bounded frontier
  fold (semi-naive: each round extends the accumulated frontier by the
  fresh post-states). Its run/coverage skeletons
  (`foldFrontier_run`/`foldFrontier_coverage` + `closure_covers`) are
  the machines-side laws — CITED here, never re-proved.
- `Datalog.Semantics.eval` — the bottom-up LFP evaluator over the
  finite fact universe, with `deriv_iff_eval` (the evaluation-
  correctness bridge against the inductive `Deriv` reading) and
  `eval_fix`/`lfp_least` (it IS the least fixpoint) — CITED, never
  re-proved.

## The machine-as-rules encoding

A machine `m : Machine S I` with input vocabulary `inputs` and initial
state `init` is read as a DATALOG PROGRAM over the value universe
`MVal S I = S ⊕ I` (a state or an input label) with two unary
predicates: `state(·)` and `in(·)`. The EDB is the initial state's
fact plus one `in` fact per listed input. The machine's TRANSITION
TABLE — extracted over the enumerated fragment `states × inputs` —
becomes the rule set: each enabled transition `(s, i, s')` is the
GROUND rule `state(s') :- state(s), in(i)`. Firing a rule IS one
machine step; reachability IS the closure.

Because the rules are ground (no variables), safety and
well-formedness are discharged by computation (`ruleOf_safe`,
`ruleOf_wf`, `edb_wf`) — the encoding cannot be unsafe.

## The honest premises (the fuel / height relationship)

- `hinit : init ∈ states` + `hclosed` (the extracted table is CLOSED:
  steps out of enumerated states land in enumerated states) — these
  make the rule extraction total over the reachable fragment; dropping
  `hclosed` silently truncates the closure (the negative control pins
  this).
- `hinputs` — the SAME coverage premise `check_proved` consumes (every
  step out of a reachable state uses a listed input); it aligns the
  unrestricted `Reachable` reading with both engines' restricted
  exploration.
- FUEL: the Datalog side needs NO budget premise — its fuel IS the
  height bound by construction (`Datalog.height`, the theoretic bound
  of `Datalog.exists_fix`; loose but sufficient). The frontier fold's
  fuel is the caller's budget: the bridge's hypothesis is the fold's
  OWN stabilization report (`reachableStates … = some rs`). An
  under-fueled fold reports the honest `none` and the bridge does not
  apply — budget exhaustion is never laundered into a verdict
  (01-core §3). The worked instance pins the relationship concretely:
  a 3-state fragment needs exactly 3 rounds; the height bound is far
  looser, and the Datalog side consumes it internally.

## The theorems

- `deriv_iff_reachable` — THE ENCODING BRIDGE: the Datalog `Deriv` LFP
  reading of `state(s)` IS machine reachability. (New proof content:
  the two induction directions over the encoding; everything else
  cited.)
- `bridge` — THE AGREEMENT: the frontier fold's stabilized result and
  the Datalog closure agree state by state. The machines side is
  `Testing.reachableAux_run`/`reachableAux_complete` (cited); the
  Datalog side is `deriv_iff_eval` (cited); the connection is the
  encoding bridge.
- `inv_of_eval` — THE PAYOFF: invariant-holds-on-the-closure ⇒
  invariant-holds-on-every-reachable-state. This RE-EXPRESSES
  `check_proved`'s content with the Datalog evaluation as the engine —
  an ALTERNATIVE evaluation path (the closure check is decidable, its
  fuel the height bound by construction). The verdict-based exploration
  stays authoritative; refactoring Explore onto Datalog is NOT this
  order (the dissolution's second half is a later window).

## The cone (verified)

`machines` importing `datalog` is a PEER import at the theory stratum:
`Datalog.Basic` imports only `Kit.Change` (C0 machinery); Datalog sits
at Machines' own level of the build order (14-build-map §2's C2 theory
row), no cycle is created, and the cone rule's prohibition (a cone-LOW
module importing cone-HIGH) is not touched — Datalog is not above
Machines. Core-only: no mathlib, no Batteries (the cone rule).

- **Root**: the relational engine (01-core §6, 02 §9) — the closure
  reading of exploration.
- **Carrier grade**: pattern #1 at the cross-library level — the
  encoding bridge `deriv_iff_reachable` is the pattern's tie, between
  two already-landed pattern-#1 instances.
- **Spine reading**: none — a substrate bridge.
- **Ladder rung**: rung 6 hand theorems CITING the two libraries'
  skeleton theorems (`foldFrontier_run`/`_coverage`, `deriv_iff_eval`)
  — cited, never re-proved; the encoding's well-formedness/safety are
  rung-3 computes.
- **Gate rows**: the axiom report pins in MachinesTests.Axioms.
-/

import Machines.Basic
import Machines.Testing
import Datalog.Semantics

namespace Machines.Closure

/-! ## The value universe and the two predicates -/

/-- The machine-as-rules VALUE universe: a state or an input label. -/
abbrev MVal (S I : Type) := Sum S I

/-- Inhabitance for the value universe (used by Datalog only to
    totalize the spec-level grounding — `Datalog.Basic`'s note). -/
instance mvalInhabited {S I : Type} [Inhabited S] : Inhabited (MVal S I) :=
  ⟨.inl default⟩

/-- The state predicate: `state(s)` — s is an accumulated machine state. -/
def stPred : Datalog.Pred := ⟨"state", 1⟩

/-- The input predicate: `in(i)` — i is a listed input (available). -/
def inPred : Datalog.Pred := ⟨"in", 1⟩

theorem stPred_ne_inPred : stPred ≠ inPred := by decide

/-! ## The encoding -/

variable {S I : Type}

/-- The EDB: the initial state's fact + one `in` fact per listed input.
    NOTE what is NOT here: the enumerated fragment's states are NOT
    facts — they only parametrize the rule extraction; the closure must
    DERIVE them (the init-fact negative control pins this). -/
def edbOf (init : S) (inputs : List I) : List (Datalog.Atom (MVal S I)) :=
  ⟨stPred, [.inl init]⟩ :: inputs.map (fun i => ⟨inPred, [.inr i]⟩)

/-- The machine's transition TABLE over the enumerated fragment: one
    triple per (state, listed input) whose step is enabled. -/
def transOf (m : Machine S I) (states : List S) (inputs : List I) :
    List (S × I × S) :=
  states.flatMap fun s =>
    inputs.filterMap fun i => (m.step? s i).map fun s' => (s, i, s')

/-- THE MACHINE AS A RULE: the transition `(s, i, s')` becomes the
    ground rule `state(s') :- state(s), in(i)` — the head is the
    post-state, the body is the pre-state plus the input's
    availability. Firing the rule IS the machine step. -/
def ruleOf (t : S × I × S) : Datalog.Rule (MVal S I) :=
  ⟨stPred, [Datalog.Term.cst (.inl t.2.2)],
    [⟨true, stPred, [Datalog.Term.cst (.inl t.1)]⟩,
     ⟨true, inPred, [Datalog.Term.cst (.inr t.2.1)]⟩]⟩

/-- The extracted program: one rule per enabled transition. -/
def programOf (m : Machine S I) (states : List S) (inputs : List I) :
    Datalog.Program (MVal S I) :=
  (transOf m states inputs).map ruleOf

/-! ## The encoding's well-formedness (rung-3 computes: ground rules
      cannot be unsafe) -/

theorem edb_wf (init : S) (inputs : List I) :
    ∀ a ∈ edbOf init inputs, a.wf := by
  intro a ha
  simp only [edbOf, List.mem_cons, List.mem_map] at ha
  rcases ha with rfl | ⟨i, _, rfl⟩ <;> simp [Datalog.Atom.wf, stPred, inPred]

theorem ruleOf_wf (t : S × I × S) : (ruleOf t).wf := by
  simp [ruleOf, Datalog.Rule.wf, stPred]

theorem ruleOf_safe (t : S × I × S) : (ruleOf t).safe = true := by
  simp [ruleOf, Datalog.Rule.safe, Datalog.Rule.bound, Datalog.Lit.vars,
    Datalog.Term.vars]

/-! ## The extraction's tie: rules ↔ transitions -/

/-- Every extracted triple's step is real: the table never invents a
    transition. -/
theorem transOf_step (m : Machine S I) (states : List S) (inputs : List I)
    (t : S × I × S) (ht : t ∈ transOf m states inputs) :
    m.step? t.1 t.2.1 = some t.2.2 := by
  simp only [transOf, List.mem_flatMap, List.mem_filterMap,
    Option.map_eq_some_iff] at ht
  obtain ⟨s, _, i, _, w, hstep, hEq⟩ := ht
  cases hEq
  exact hstep

/-- Every enabled step over the fragment IS extracted: the table never
    misses a transition (this is where `hinputs` bites — an unlisted
    input's transition has no rule, on BOTH engines). -/
theorem ruleOf_mem (m : Machine S I) (states : List S) (inputs : List I)
    (s : S) (i : I) (s' : S) (hs : s ∈ states) (hi : i ∈ inputs)
    (hstep : m.step? s i = some s') :
    ruleOf (s, i, s') ∈ programOf m states inputs := by
  simp only [programOf, List.mem_map, transOf]
  exact ⟨(s, i, s'), List.mem_flatMap.mpr ⟨s, hs,
    List.mem_filterMap.mpr ⟨i, hi, by simp [hstep]⟩⟩, rfl⟩

/-! ## The closure's substrate: reachability ⊆ the fragment -/

/-- The enumerated fragment COVERS the reachable fragment (given the
    closedness of the extraction). -/
theorem reachable_mem_states (m : Machine S I) (states : List S)
    (inputs : List I) (init : S)
    (hinit : init ∈ states)
    (hclosed : ∀ s ∈ states, ∀ i ∈ inputs, ∀ s',
      m.step? s i = some s' → s' ∈ states)
    (hinputs : ∀ s i s', m.Reachable init s → m.step? s i = some s' →
      i ∈ inputs) :
    ∀ s, m.Reachable init s → s ∈ states := by
  intro s hr
  induction hr with
  | here => exact hinit
  | step i hst hprev ih =>
      exact hclosed _ ih i (hinputs _ i _ hprev hst) _ hst

/-! ## THE ENCODING BRIDGE -/

/-- THE ENCODING BRIDGE, forward: the Datalog LFP reading of the
    encoding derives EXACTLY the reachable states — a derivation IS a
    run (each rule firing is one machine step, the base fact is the
    initial state). -/
theorem deriv_reachable [DecidableEq S] [DecidableEq I] [Inhabited S]
    (m : Machine S I) (states : List S) (inputs : List I) (init : S) :
    ∀ a : Datalog.Atom (MVal S I),
      Datalog.Deriv (programOf m states inputs) (edbOf init inputs) a →
      ∀ s, a = ⟨stPred, [.inl s]⟩ → m.Reachable init s := by
  intro a h
  induction h with
  | base ha =>
      rcases List.mem_cons.mp ha with rfl | ham
      · intro s hEq
        have hsi : s = init := by
          simpa using (((Datalog.atom_ext_iff _ _).mp hEq).2).symm
        rw [hsi]
        exact .here
      · obtain ⟨i, _, hEq⟩ := List.mem_map.mp ham
        subst hEq
        intro s hEq'
        exact absurd (((Datalog.atom_ext_iff _ _).mp hEq').1).symm
          stPred_ne_inPred
  | @fire r a' σ hr _ hbody hhead ih =>
      obtain ⟨t, htmem, hteq⟩ := List.mem_map.mp hr
      subst hteq
      -- the first body literal derives the pre-state's fact
      have hpre := ih (⟨true, stPred, [Datalog.Term.cst (.inl t.1)]⟩ : _)
        (by simp [ruleOf]) t.1 rfl
      intro s hEq
      -- the head's grounding pins a' to the post-state's atom
      have hhead' : ⟨stPred, [Sum.inl t.2.2]⟩ = a' := by
        simpa only [ruleOf, Datalog.ground, List.map_cons, List.map_nil,
          Datalog.sub] using hhead
      have hts : t.2.2 = s := by
        simpa using ((Datalog.atom_ext_iff _ _).mp (hhead'.trans hEq)).2
      rw [hts.symm]
      exact Machine.Reachable.step t.2.1 (transOf_step m states inputs t htmem)
        hpre

/-- THE ENCODING BRIDGE, combined: the LFP reading of `state(s)` IS
    machine reachability — both directions (the ← direction rides the
    rule-extraction tie + the input coverage premise). -/
theorem deriv_iff_reachable [DecidableEq S] [DecidableEq I] [Inhabited S]
    (m : Machine S I) (states : List S) (inputs : List I) (init : S)
    (hinit : init ∈ states)
    (hclosed : ∀ s ∈ states, ∀ i ∈ inputs, ∀ s',
      m.step? s i = some s' → s' ∈ states)
    (hinputs : ∀ s i s', m.Reachable init s → m.step? s i = some s' →
      i ∈ inputs)
    (s : S) :
    (Datalog.Deriv (programOf m states inputs) (edbOf init inputs)
        ⟨stPred, [.inl s]⟩ ↔ m.Reachable init s) := by
  constructor
  · intro h
    exact deriv_reachable m states inputs init _ h s rfl
  · intro hr
    induction hr with
    | here => exact Datalog.Deriv.base (by simp [edbOf])
    | @step s₀ s' i hst hprev ih =>
        have hs₀ : s₀ ∈ states :=
          reachable_mem_states m states inputs init hinit hclosed hinputs s₀ hprev
        refine Datalog.Deriv.fire (r := ruleOf (s₀, i, s'))
          (σ := fun _ => Sum.inl default)
          (ruleOf_mem m states inputs s₀ i s' hs₀
            (hinputs s₀ i s' hprev hst) hst) ?_ ?_ ?_
        · simp [ruleOf]
        · intro l hl
          simp only [ruleOf, List.mem_cons] at hl
          rcases hl with rfl | rfl | hnil
          · exact ih
          · exact Datalog.Deriv.base (by
              show (⟨inPred, [Sum.inr i]⟩ : Datalog.Atom (MVal S I)) ∈
                edbOf init inputs
              exact List.mem_cons_of_mem _ (List.mem_map
                (f := fun (i' : I) =>
                  (⟨inPred, [Sum.inr i']⟩ : Datalog.Atom (MVal S I)))
                |>.mpr ⟨i, hinputs s₀ i s' hprev hst, rfl⟩))
          · cases hnil
        · rfl

/-! ## THE AGREEMENT: the fold's stabilized result = the Datalog closure -/

/-- THE BRIDGE: the bounded frontier fold's stabilized result and the
    Datalog closure of the machine-as-rules encoding agree state by
    state. Machines side: `Testing.reachableAux_run`/`_complete`
    (cited — the fold's skeletons, proved once). Datalog side:
    `deriv_iff_eval` (cited — the LFP correctness bridge). Connection:
    `deriv_iff_reachable` (the encoding bridge above).
    Premises: the closed extraction (`hinit` + `hclosed`), the shared
    coverage premise (`hinputs`), and the fold's OWN stabilization
    report — the fuel discipline (see header: the Datalog side's fuel
    is the height bound by construction; an under-fueled fold reports
    the honest `none` and this theorem does not apply). -/
theorem bridge [DecidableEq S] [DecidableEq I] [Inhabited S]
    (m : Machine S I) (states : List S) (inputs : List I) (init : S)
    (fuel : Nat)
    (hinit : init ∈ states)
    (hclosed : ∀ s ∈ states, ∀ i ∈ inputs, ∀ s',
      m.step? s i = some s' → s' ∈ states)
    (hinputs : ∀ s i s', m.Reachable init s → m.step? s i = some s' →
      i ∈ inputs)
    (rs : List S)
    (hstab : Testing.reachableStates m inputs init fuel = some rs)
    (s : S) :
    s ∈ rs ↔ ⟨stPred, [.inl s]⟩ ∈
      Datalog.eval (programOf m states inputs) (edbOf init inputs) := by
  have hpwf : ∀ r ∈ programOf m states inputs, r.wf := fun r hr => by
    obtain ⟨t, _, hEq⟩ := List.mem_map.mp hr; subst hEq; exact ruleOf_wf t
  have hsafe : ∀ r ∈ programOf m states inputs, r.safe = true :=
    fun r hr => by
      obtain ⟨t, _, hEq⟩ := List.mem_map.mp hr; subst hEq; exact ruleOf_safe t
  rw [Testing.reachableStates] at hstab
  constructor
  · intro hmem
    have hrun := Testing.reachableAux_run m inputs init fuel [(init, [])]
      (fun p hp => by
        have hpe : p = (init, []) := List.mem_singleton.mp hp
        subst hpe; rfl)
    rw [hstab] at hrun
    exact (Datalog.deriv_iff_eval (programOf m states inputs)
      (edbOf init inputs) (edb_wf init inputs) hpwf hsafe
      (⟨stPred, [.inl s]⟩ : Datalog.Atom (MVal S I))).mp
      ((deriv_iff_reachable m states inputs init hinit hclosed hinputs s).2
        (hrun s (by simpa using hmem)))
  · intro hev
    have hr : m.Reachable init s :=
      (deriv_iff_reachable m states inputs init hinit hclosed hinputs s).1
        ((Datalog.deriv_iff_eval (programOf m states inputs)
          (edbOf init inputs) (edb_wf init inputs) hpwf hsafe
          (⟨stPred, [.inl s]⟩ : Datalog.Atom (MVal S I))).mpr hev)
    rcases Testing.reachableAux_complete m inputs init fuel [(init, [])]
      (by simp) hinputs s hr with h | h
    · rw [hstab] at h; simpa using h
    · rw [h] at hstab; simp at hstab

/-! ## THE PAYOFF: the closure check re-expresses check_proved -/

/-- THE PAYOFF: if the invariant holds on every state the Datalog
    closure derives, it holds on EVERY reachable state — the content of
    `check_proved`, re-expressed with the closure evaluation as the
    engine. The closure check is decidable with its fuel the height
    bound by construction (`Datalog.eval`); the verdict-based
    exploration (`check`) stays authoritative — this is the ALTERNATIVE
    path, not a refactor. -/
theorem inv_of_eval [DecidableEq S] [DecidableEq I] [Inhabited S]
    (m : Machine S I) (states : List S) (inputs : List I) (init : S)
    (hinit : init ∈ states)
    (hclosed : ∀ s ∈ states, ∀ i ∈ inputs, ∀ s',
      m.step? s i = some s' → s' ∈ states)
    (hinputs : ∀ s i s', m.Reachable init s → m.step? s i = some s' →
      i ∈ inputs)
    (inv? : S → Bool)
    (hinv : ∀ s, ⟨stPred, [.inl s]⟩ ∈
        Datalog.eval (programOf m states inputs) (edbOf init inputs) →
        inv? s = true)
    (s : S) (hr : m.Reachable init s) : inv? s = true :=
  hinv s ((Datalog.deriv_iff_eval (programOf m states inputs)
    (edbOf init inputs) (edb_wf init inputs)
    (fun r hmem => by
      obtain ⟨t, _, hEq⟩ := List.mem_map.mp hmem; subst hEq; exact ruleOf_wf t)
    (fun r hmem => by
      obtain ⟨t, _, hEq⟩ := List.mem_map.mp hmem; subst hEq;
        exact ruleOf_safe t)
    (⟨stPred, [.inl s]⟩ : Datalog.Atom (MVal S I))).mp (
      (deriv_iff_reachable m states inputs init hinit hclosed hinputs s).2
      hr))

end Machines.Closure

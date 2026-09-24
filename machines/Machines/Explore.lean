/-
# Machines.Explore — the bounded exploration with the honest trichotomy

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/01-core.md §3 (bounded exploration returns
THREE honest answers: PROVED with a certificate / REFUTED with a
counterexample trace / UNKNOWN with the reason — budget exhaustion is
UNKNOWN, never silently a verdict) + notes/v3/08-capabilities.md §10
(the liveness/finite model-checking lane: the honest trichotomy
everywhere; guard: finite only).

## The verdict (the closed vocabulary, ctors never strings)

- `.proved` — the explored frontier STABILIZED (a round found no fresh
  state) and no accumulated state violated the predicate. Soundness
  (`check_proved`): under the input-coverage premise, the invariant
  then holds on EVERY reachable state — stabilization makes the
  accumulated set closed under the covered step relation, so the
  exploration covered the reachable fragment, not just the visited
  paths.
- `.refuted tape bad` — a witnessed violation: the tape RUNS from the
  initial state to `bad` (`check_refuted` proves it — the witness is
  data, and the theorem proves it counter-exemplifies). A seen
  violation is reported as a refutation regardless of the budget: the
  witness exists whether or not the search may continue.
- `.unknown reason` — the budget ran out before stabilization with no
  violation SEEN. Honest gap: no claim either way. This checker's only
  unknown cause is `budgetExhausted`; further causes (e.g.
  stateSpaceUnbounded for checkers over unenumerated spaces) land with
  the checkers that can honestly name them — a constructor no code
  path produces is armed-but-unfired (the obligation discipline).

The search: rounds over an accumulated frontier of (state, tape)
entries; each round appends one entry per (accumulated entry, input)
whose post-state is fresh. Termination is by the fuel (the budget) —
the caller names it, and its exhaustion is REPORTED, never laundered.

## The parameterized frontier fold (the review's finding #4, consolidated)

The fuel recursion over the (S × List I) frontier — the round
structure, the `freshEntries` growth, the stabilization check — is
written ONCE here as `foldFrontier`, parameterized by the per-round
observer: the caller names what the fold RETURNS at budget exhaustion
(`budget`) and at stabilization (`stable`). This module instantiates
it with the verdict observers (`refutedOf` / `stabilizedOf`);
Machines.Testing instantiates it with the state-projection observers
(`none` / `some ∘ map Prod.fst`). The run/stabilization skeletons —
`foldFrontier_run`, `foldFrontier_coverage`, plus the shared
`closure_covers` / `seen_refuted` cores — are proved ONCE over the
parameterized shape; the consumers' theorems keep their statements as
instances (15-patterns: one carrier, many faces — never a parallel
table).

## The five questions

- **Root**: TraceModel (01-core §3) — the bounded-exploration face of
  the behavior side: PROVED/REFUTED/UNKNOWN over the executions.
- **Carrier grade**: pattern #1 again — the decidable search is the
  shadow; the soundness/witness theorems are the bridge to the
  proposition-level reading.
- **Spine reading**: none — a substrate for the 08 §10 lane.
- **Ladder rung**: hand theorems (rung 6, the written reason: the
  soundness argument is an induction over the fuel rounds, not a
  decide); the per-machine faces are rung-3 decides in the tests.
- **Gate rows**: the axiom report pins in MachinesTests.Axioms.

## Named exclusions

- NO fairness, NO POR, NO vector clocks (08 §10's guard — the heavy
  half follows its first genuinely-concurrent consumer).
- NO dedup of same-state tapes (the frontier keeps one entry per
  distinct path) — a size discipline lands with a consumer that
  measures; correctness here needs only membership facts.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Basic

namespace Machines

/-! ## The verdict -/

/-- The UNKNOWN causes this checker can honestly name. -/
inductive ExploreReason where
  /-- The fuel ran out before the frontier stabilized — no claim either
      way (01-core §3: budget exhaustion is UNKNOWN, never a verdict). -/
  | budgetExhausted
deriving BEq, Repr

/-- The honest trichotomy. A verdict is DATA carrying its evidence:
    the refutation's tape + bad state; the unknown's named cause. -/
inductive Verdict (S I : Type) where
  /-- The frontier stabilized with no violation found — soundness is
      `check_proved` (under the coverage premise). -/
  | proved
  /-- A witnessed violation: the tape runs from the initial state to
      `bad`, which violates the predicate — `check_refuted`. -/
  | refuted (tape : List I) (bad : S)
  /-- No verdict — the named cause says why. -/
  | unknown (reason : ExploreReason)
deriving BEq, Repr

/-! ## The search -/

variable {S I : Type}

/-- The first accumulated entry whose state violates `inv?`. -/
def badEntry (inv? : S → Bool) (acc : List (S × List I)) : Option (S × List I) :=
  acc.find? fun p => inv? p.1 = false

/-- The fresh frontier: one entry per (accumulated entry, input) whose
    post-state's state is not yet accumulated. The tape is the entry's
    tape extended by the input — the path is carried with the state. -/
def freshEntries (m : Machine S I) (inputs : List I) (acc : List (S × List I))
    [DecidableEq S] : List (S × List I) :=
  (acc.flatMap fun p => inputs.filterMap fun i =>
      (m.step? p.1 i).map fun s' => (s', p.2 ++ [i]))
    |>.filter fun q => !(acc.any fun p => decide (p.1 = q.1))

/-- The verdict when the budget is exhausted: a SEEN violation is a
    refutation (the witness exists); otherwise the honest gap. -/
def refutedOf (inv? : S → Bool) (acc : List (S × List I)) : Verdict S I :=
  match badEntry inv? acc with
  | some (bad, tape) => .refuted tape bad
  | none => .unknown .budgetExhausted

/-- The verdict when the frontier stabilized: a SEEN violation is a
    refutation; otherwise the coverage proved (`check_proved`). -/
def stabilizedOf (inv? : S → Bool) (acc : List (S × List I)) : Verdict S I :=
  match badEntry inv? acc with
  | some (bad, tape) => .refuted tape bad
  | none => .proved

/-- THE FRONTIER FOLD, parameterized by the per-round observer (the
    review's finding #4, consolidated): the caller supplies the
    fuel-exhaustion reading (`budget`) and the stabilization reading
    (`stable`) of the accumulated frontier; the fold itself — the
    rounds over `freshEntries`, the fuel recursion, the frontier
    growth — is written ONCE. This module instantiates it with the
    verdict observers (`refutedOf` / `stabilizedOf`, below);
    Machines.Testing instantiates it with the state-projection
    observers. -/
def foldFrontier (m : Machine S I) (inputs : List I) [DecidableEq S]
    {O : Type} (budget stable : List (S × List I) → O) :
    Nat → List (S × List I) → O
  | 0, acc => budget acc
  | fuel + 1, acc =>
      if freshEntries m inputs acc = [] then stable acc
      else foldFrontier m inputs budget stable fuel (acc ++ freshEntries m inputs acc)

/-- The bounded exploration: the frontier fold over the VERDICT
    observers — budget exhaustion reports via `refutedOf` (a SEEN
    violation is a refutation, never laundered into a verdict),
    stabilization via `stabilizedOf`. -/
def exploreAux (m : Machine S I) (inv? : S → Bool) (inputs : List I)
    [DecidableEq S] : Nat → List (S × List I) → Verdict S I :=
  foldFrontier m inputs (refutedOf inv?) (stabilizedOf inv?)

/-- The bounded model check of `inv?` over `m` from `init`, with the
    input vocabulary `inputs` and the exploration budget `fuel`. -/
def check (m : Machine S I) (inv? : S → Bool) (inputs : List I) (init : S)
    (fuel : Nat) [DecidableEq S] : Verdict S I :=
  exploreAux m inv? inputs fuel [(init, [])]

/-! ## The search's internal laws (the soundness substrates) -/

/-- THE PATH LAW: every fresh entry's tape RUNS to its state — the
    frontier never lies about its own paths. Proved once; cited by the
    witness argument. -/
theorem freshEntries_run (m : Machine S I) (inputs : List I)
    (acc : List (S × List I)) [DecidableEq S] (init : S)
    (hacc : ∀ p ∈ acc, m.run init p.2 = some p.1) :
    ∀ q ∈ freshEntries m inputs acc, m.run init q.2 = some q.1 := by
  intro q hq
  have h1 : q ∈ List.filter (fun q => !(acc.any fun r => decide (r.1 = q.1)))
      (acc.flatMap fun p => inputs.filterMap fun i =>
        (m.step? p.1 i).map fun s' => (s', p.2 ++ [i])) := hq
  obtain ⟨hflat, _⟩ := List.mem_filter.mp h1
  obtain ⟨p, hp, hfm⟩ := List.mem_flatMap.mp hflat
  obtain ⟨i, hi, hfm2⟩ := List.mem_filterMap.mp hfm
  rw [Option.map_eq_some_iff] at hfm2
  obtain ⟨s', hstep, hqeq⟩ := hfm2
  have hrun := hacc p hp
  rw [← hqeq, m.run_append init p.2 [i], hrun, Option.bind_some,
    m.run_one p.fst i, hstep]

/-- STABILIZATION = CLOSURE: a round that finds nothing fresh leaves an
    accumulated set closed under the covered step relation — every
    covered step from an accumulated state lands on a state that is
    also accumulated. This is what upgrades PROVED from "the visited
    paths are clean" to "the reachable fragment is clean". -/
theorem freshEntries_nil (m : Machine S I) (inputs : List I)
    (acc : List (S × List I)) [DecidableEq S]
    (h : freshEntries m inputs acc = []) :
    ∀ (p : S × List I), p ∈ acc → ∀ i ∈ inputs, ∀ s',
      m.step? p.1 i = some s' → ∃ t, (s', t) ∈ acc := by
  intro p hp i hi s' hs
  have hq : (s', p.2 ++ [i]) ∈ acc.flatMap
      (fun p => inputs.filterMap fun i =>
        (m.step? p.1 i).map fun s' => (s', p.2 ++ [i])) :=
    List.mem_flatMap.mpr ⟨p, hp, List.mem_filterMap.mpr ⟨i, hi, by
      rw [hs]; exact rfl⟩⟩
  cases hb2 : acc.any (fun r => decide (r.1 = s')) with
  | false =>
      exfalso
      have hmem : (s', p.2 ++ [i]) ∈ freshEntries m inputs acc :=
        List.mem_filter.mpr ⟨hq, by
          show (!(acc.any fun r => decide (r.1 = s'))) = true
          rw [hb2]; simp⟩
      rw [h] at hmem
      exact absurd hmem List.not_mem_nil
  | true =>
      -- some accumulated entry already HAS this state
      obtain ⟨p', hp', heq⟩ := List.any_eq_true.mp hb2
      refine ⟨p'.2, ?_⟩
      rw [← show p'.1 = s' from decide_eq_true_eq.mp heq]
      exact hp'

/-- No violation found by `find?` = no accumulated state violates. -/
theorem badEntry_none (inv? : S → Bool) (acc : List (S × List I))
    (h : badEntry inv? acc = none) : ∀ p ∈ acc, inv? p.1 = true := by
  intro p hp
  have := List.find?_eq_none.mp h p hp
  simpa using this

/-! ## The fold's laws (proved ONCE over the parameterized shape) -/

/-- THE COVERAGE INDUCTION (the stabilization⇒coverage induction,
    proved once): the seed entry + the per-round closure (what
    `freshEntries_nil` delivers at stabilization) ⇒ the accumulated set
    covers the reachable fragment. Both consumers' stabilization
    handlers cite this — the induction is no longer proved twice. -/
theorem closure_covers (m : Machine S I) (inputs : List I) (init : S)
    (acc : List (S × List I)) (hseed : (init, []) ∈ acc)
    (hclosed : ∀ (p : S × List I), p ∈ acc → ∀ i ∈ inputs, ∀ s',
      m.step? p.1 i = some s' → ∃ t, (s', t) ∈ acc)
    (hinputs : ∀ s i s', m.Reachable init s → m.step? s i = some s' → i ∈ inputs) :
    ∀ s, m.Reachable init s → ∃ t, (s, t) ∈ acc := by
  intro s hr
  induction hr with
  | here => exact ⟨[], hseed⟩
  | @step s₀ s' i hst hprev ihc =>
      obtain ⟨t₀, ht₀⟩ := ihc
      exact hclosed (s₀, t₀) ht₀ i (hinputs s₀ i s' hprev hst) s' hst

/-- THE WITNESS CORE (proved once): a SEEN violation (`badEntry` found
    one) yields the refuting witness — the tape runs, the predicate
    fails, the state is reachable — whichever verdict wrapper reports
    it (`refutedOf` at budget exhaustion, `stabilizedOf` at
    stabilization: both route through `badEntry`). -/
theorem seen_refuted (m : Machine S I) (inv? : S → Bool) (acc : List (S × List I))
    (init : S) (hacc : ∀ p ∈ acc, m.run init p.2 = some p.1)
    (e : S × List I) (hb : badEntry inv? acc = some e) :
    m.run init e.2 = some e.1 ∧ inv? e.1 = false ∧ m.Reachable init e.1 := by
  refine ⟨hacc e (List.mem_of_find?_eq_some hb), ?_,
    m.run_reachable init (hacc e (List.mem_of_find?_eq_some hb))⟩
  have hfind := List.find?_some hb
  simpa using hfind

/-- THE RUN SKELETON (proved once over the parameterized shape): for
    ANY predicate `Q` on the fold's output that the observers preserve
    from a run-honest frontier (`hbudget` / `hstable`), the fold's
    result satisfies `Q` — the run-honesty of the frontier is preserved
    round by round (`freshEntries_run` does the growth step). The
    consumers' "the frontier never lies" theorems are instances. -/
theorem foldFrontier_run {O : Type} (m : Machine S I) (inputs : List I)
    [DecidableEq S] (init : S) (budget stable : List (S × List I) → O)
    (Q : O → Prop)
    (hbudget : ∀ acc : List (S × List I),
      (∀ p ∈ acc, m.run init p.2 = some p.1) → Q (budget acc))
    (hstable : ∀ acc : List (S × List I),
      (∀ p ∈ acc, m.run init p.2 = some p.1) → Q (stable acc)) :
    ∀ (fuel : Nat) (acc : List (S × List I)),
      (∀ p ∈ acc, m.run init p.2 = some p.1) →
      Q (foldFrontier m inputs budget stable fuel acc) := by
  intro fuel
  induction fuel with
  | zero => intro acc h; exact hbudget acc h
  | succ n ih =>
      intro acc h
      simp only [foldFrontier]
      by_cases hf : freshEntries m inputs acc = []
      · rw [if_pos hf]
        exact hstable acc h
      · rw [if_neg hf]
        refine ih (acc ++ freshEntries m inputs acc) fun p hp => ?h
        rcases List.mem_append.mp hp with h1 | h2
        · exact h p h1
        · exact freshEntries_run m inputs acc init h p h2

/-- THE COVERAGE SKELETON (proved once over the parameterized shape):
    for ANY predicate `Q` on the fold's output that the observers
    preserve from a seeded + closed frontier (`hbudget` / `hstable` —
    the closure slot is `freshEntries_nil`'s deliverance), the fold's
    result satisfies `Q`. The consumers' "stabilization = coverage"
    theorems are instances. -/
theorem foldFrontier_coverage {O : Type} (m : Machine S I) (inputs : List I)
    [DecidableEq S] (init : S) (budget stable : List (S × List I) → O)
    (Q : O → Prop)
    (hbudget : ∀ acc : List (S × List I), (init, []) ∈ acc → Q (budget acc))
    (hstable : ∀ acc : List (S × List I), (init, []) ∈ acc →
      (∀ (p : S × List I), p ∈ acc → ∀ i ∈ inputs, ∀ s',
        m.step? p.1 i = some s' → ∃ t, (s', t) ∈ acc) → Q (stable acc)) :
    ∀ (fuel : Nat) (acc : List (S × List I)), (init, []) ∈ acc →
      Q (foldFrontier m inputs budget stable fuel acc) := by
  intro fuel
  induction fuel with
  | zero => intro acc hseed; exact hbudget acc hseed
  | succ n ih =>
      intro acc hseed
      simp only [foldFrontier]
      by_cases hf : freshEntries m inputs acc = []
      · rw [if_pos hf]
        exact hstable acc hseed fun p hp i hi s' hs =>
          freshEntries_nil m inputs acc hf p hp i hi s' hs
      · rw [if_neg hf]
        exact ih (acc ++ freshEntries m inputs acc)
          (List.mem_append.mpr (Or.inl hseed))

/-! ## The soundness theorems (the verdict observers' instances) -/

/-- PROVED SOUNDNESS: a `.proved` verdict means the invariant holds on
    every state REACHABLE from `init` — the coverage premise is the
    input coverage (every step out of a reachable state uses a listed
    input). Stated honestly: this is coverage of the reachable
    fragment, nothing about unreachable states. An INSTANCE of
    `foldFrontier_coverage` at the verdict observers. -/
theorem exploreAux_proved (m : Machine S I) (inv? : S → Bool) (inputs : List I)
    [DecidableEq S] (init : S) (fuel : Nat) (acc : List (S × List I))
    (hseed : (init, []) ∈ acc)
    (h : exploreAux m inv? inputs fuel acc = .proved)
    (hinputs : ∀ s i s', m.Reachable init s → m.step s i s' → i ∈ inputs) :
    ∀ s, m.Reachable init s → inv? s = true := by
  have hgen := foldFrontier_coverage m inputs init (refutedOf inv?)
    (stabilizedOf inv?)
    (Q := fun o => o = .proved → ∀ s, m.Reachable init s → inv? s = true)
    (hbudget := by
        intro a _ hcon
        cases hb : badEntry inv? a with
        | none => simp [refutedOf, hb] at hcon
        | some e => simp [refutedOf, hb] at hcon)
    (hstable := by
        intro a hseed hclosed hcon
        cases hb : badEntry inv? a with
        | some e => simp [stabilizedOf, hb] at hcon
        | none =>
            have hclean := badEntry_none inv? a hb
            intro s hr
            obtain ⟨t, ht⟩ := closure_covers m inputs init a hseed hclosed hinputs s hr
            exact hclean (s, t) ht)
    fuel acc hseed
  exact hgen h

/-- The check-level wrapper of `exploreAux_proved` (the seed is the
    singleton frontier). -/
theorem check_proved (m : Machine S I) (inv? : S → Bool) (inputs : List I)
    (init : S) (fuel : Nat) [DecidableEq S]
    (h : check m inv? inputs init fuel = .proved)
    (hinputs : ∀ s i s', m.Reachable init s → m.step s i s' → i ∈ inputs) :
    ∀ s, m.Reachable init s → inv? s = true :=
  exploreAux_proved m inv? inputs init fuel [(init, [])] (by simp) h hinputs

/-- REFUTED WITNESS: the `.refuted` verdict's tape is a REAL
    counterexample — it runs from the initial state to `bad`, and `bad`
    violates the predicate. The verdict's evidence is proved, not
    asserted. An INSTANCE of `foldFrontier_run` at the verdict
    observers (both route through `badEntry`, so both handlers share
    `seen_refuted`). -/
theorem exploreAux_refuted (m : Machine S I) (inv? : S → Bool) (inputs : List I)
    [DecidableEq S] (init : S) :
    ∀ (fuel : Nat) (acc : List (S × List I)),
      (∀ p ∈ acc, m.run init p.2 = some p.1) →
      exploreAux m inv? inputs fuel acc = .refuted tape bad →
      m.run init tape = some bad ∧ inv? bad = false ∧ m.Reachable init bad := by
  intro fuel acc hacc h
  have hgen := foldFrontier_run m inputs init (refutedOf inv?) (stabilizedOf inv?)
    (Q := fun o => ∀ t b, o = .refuted t b →
      m.run init t = some b ∧ inv? b = false ∧ m.Reachable init b)
    (hbudget := by
        intro a hacc'
        cases hb : badEntry inv? a with
        | none =>
            intro t b hcon
            simp [refutedOf, hb] at hcon
        | some e =>
            intro t b hcon
            simp only [refutedOf, hb] at hcon
            injection hcon with h1 h2
            subst h1; subst h2
            exact seen_refuted m inv? a init hacc' e hb)
    (hstable := by
        intro a hacc'
        cases hb : badEntry inv? a with
        | none =>
            intro t b hcon
            simp [stabilizedOf, hb] at hcon
        | some e =>
            intro t b hcon
            simp only [stabilizedOf, hb] at hcon
            injection hcon with h1 h2
            subst h1; subst h2
            exact seen_refuted m inv? a init hacc' e hb)
    fuel acc hacc
  exact hgen tape bad h

/-- The check-level wrapper of `exploreAux_refuted`. -/
theorem check_refuted (m : Machine S I) (inv? : S → Bool) (inputs : List I)
    (init : S) (fuel : Nat) [DecidableEq S]
    (h : check m inv? inputs init fuel = .refuted tape bad) :
    m.run init tape = some bad ∧ inv? bad = false ∧ m.Reachable init bad :=
  exploreAux_refuted m inv? inputs init fuel [(init, [])]
    (by intro p hp
        have : p = (init, []) := List.mem_singleton.mp hp
        subst this
        rfl)
    h

end Machines

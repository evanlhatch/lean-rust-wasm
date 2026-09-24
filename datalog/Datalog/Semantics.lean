/-
# Datalog.Semantics — the monotone operator, the LFP, the evaluator, the bridge

Owned by: the datalog agent (the mandate tree, `datalog/`).
Driving decisions: notes/v3/02-data-plane.md §9 (Datalog as the
executable fragment: the monotone consequence operator, LFP semantics,
evaluation correctness — finite-domain Boolean facts give finite-height
iteration) + notes/v3/01-core.md §6 (the evaluation-correctness
theorem's shape: per-primitive soundness/completeness — here the
matcher lemmas — composed ONCE into the whole-operator bridge)
+ notes/v3/15-patterns.md #1 (relation-as-spec + executable checker +
the proved bridge — the Prop-level `Conseq`/`Deriv` reading vs the
executable `step`/`eval`, tied by `step_iff_conseq` and
`deriv_iff_eval`).

## The shape

- SPEC: `Conseq P D a` — one-step consequence under a TOTAL grounding
  `σ : String → Value`; `Deriv P E a` — the inductively-defined least
  fixpoint (an EDB fact, or the σ-head of a rule whose grounded body
  is derivable). `Lit.sat` DEMANDS positivity, so a negated literal
  satisfies nothing — the spec refuses negation exactly where the
  executable checker refuses it.
- OPERATOR: `step P F` = `F` plus every ground head derived by firing
  a rule over `F` (grounding through the executable matcher over the
  POSITIVE body; a rule with any negated body literal is INERT — it
  produces nothing). `step` is total and MONOTONE for all programs
  (`step_mono`); safety is needed only where the spec reading is
  claimed (`step_iff_conseq`'s ←, `Deriv.eval_mem`).
- FINITENESS: the fact universe is carved out of the EDB values +
  program constants (`univ`); the representable ground atoms over the
  program's predicates form the finite `possible` list. Every derived
  fact stays inside `possible` (the closure theorem), each
  non-fixpoint step strictly shrinks `missing = |possible \ F|`
  (`missing_step_lt`), so the iteration stabilizes by
  `height = |possible|` (`exists_fix`) — a THEORETIC bound, not a
  tuning cap.
- EVALUATOR: `eval P E = iter P E (height P E)` — bottom-up with the
  honest fuel. `eval_fix` (it IS a fixpoint), `lfp_least` (it is the
  LEAST one: below every pre-fixpoint above the EDB), and
  `deriv_iff_eval` (sound + complete against `Deriv` — both directions
  honest over the finite fragment).

## The honest exclusions (named, per 02-data-plane §9)

- STRATIFIED NEGATION is NOT in this fragment: a negated body literal
  fails the safety check (`SafetyError.negation` — the named refusal)
  and is inert under the operator. Extension point: stratification
  with its own termination law.
- NO aggregation, NO arithmetic generation (the value universe never
  grows — closure over `univ` is load-bearing for `height`), NO
  recursive bag weights (finite keys alone don't terminate those —
  the trap), NO external effects. Each lands with its named law.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Datalog.Basic

namespace Datalog

variable {Value : Type}

/-! ## A small core-only filter lemma -/

/-- A filtered list that provably drops a member is STRICTLY shorter. -/
theorem length_filter_lt {p : α → Bool} {l : List α} {a : α}
    (ha : a ∈ l) (hp : p a = false) : (l.filter p).length < l.length := by
  induction l with
  | nil => cases ha
  | cons x t ih =>
    cases hx : p x with
    | false =>
      rw [List.filter_cons_of_neg (by simp [hx])]
      exact Nat.succ_le_succ (List.length_filter_le p t)
    | true =>
      rcases List.mem_cons.1 ha with rfl | ha
      · rw [hx] at hp; exact absurd hp (by simp)
      · rw [List.filter_cons_of_pos hx]
        exact Nat.succ_le_succ (ih ha)

/-! ## The spec reading: total groundings -/

/-- The spec-level grounding of a term under a total substitution. -/
def sub (σ : String → Value) : Term Value → Value
  | .cst v => v
  | .var x => σ x

/-- The spec-level ground atom of a (pred, terms) pair. -/
def ground (σ : String → Value) (p : Pred) (ts : List (Term Value)) : Atom Value :=
  ⟨p, ts.map (sub σ)⟩

/-- A literal is satisfied (in this fragment) iff it is POSITIVE and
    its ground instance is in the reading `D`. A negated literal has
    no satisfying grounding — the spec refuses negation exactly where
    the executable checker refuses it (the named exclusion). -/
abbrev Lit.sat (σ : String → Value) (l : Lit Value) (D : Atom Value → Prop) : Prop :=
  l.positive = true ∧ D (ground σ l.pred l.args)

/-- A rule's consequence reading: some grounding satisfies every body
    literal and the head grounds to `a`. -/
def Rule.conseq (r : Rule Value) (σ : String → Value) (D : Atom Value → Prop)
    (a : Atom Value) : Prop :=
  (∀ l ∈ r.body, l.sat σ D) ∧ ground σ r.headPred r.headArgs = a

/-- ONE-STEP consequence over a reading `D` — the spec face of
    `step`. -/
def Conseq (P : Program Value) (D : Atom Value → Prop) (a : Atom Value) : Prop :=
  ∃ r ∈ P, ∃ σ, r.conseq σ D a

/-- The spec operator is MONOTONE (02-data-plane §9): a bigger reading
    satisfies at least the same bodies. This is the property the
    fragment is built around — and the property negation destroys
    (which is why negation is refused). -/
theorem Conseq.mono (P : Program Value) {D D' : Atom Value → Prop}
    (h : ∀ a, D a → D' a) (a : Atom Value) (hD : Conseq P D a) : Conseq P D' a := by
  obtain ⟨r, hr, σ, hb, ha⟩ := hD
  exact ⟨r, hr, σ, fun l hl => ⟨(hb l hl).1, h _ (hb l hl).2⟩, ha⟩

/-! ## The executable operator -/

/-- Fire one rule over a fact set: ground the (wholly positive) body
    through the matcher, emit the ground head. A rule with ANY negated
    body literal is INERT (produces nothing) — the operator stays
    total and monotone for all programs; the safety checker refuses
    such rules before evaluation anyway. -/
def Rule.fire [DecidableEq Value] (r : Rule Value) (F : List (Atom Value)) :
    List (Atom Value) :=
  if r.body.all (fun l => l.positive = true) then
    (matchAll r.body F []).filterMap fun s =>
      (s.applyAll r.headArgs).map (⟨r.headPred, ·⟩)
  else []

/-- The immediate-consequence operator, ONE step: the old facts plus
    every newly derived ground head not already present. -/
def step [DecidableEq Value] (P : Program Value) (F : List (Atom Value)) :
    List (Atom Value) :=
  F ++ (P.flatMap (fun r => r.fire F)).filter (fun a => decide (a ∉ F))

/-- Matching is monotone in the fact set. -/
theorem matchAll_mono [DecidableEq Value] (lits : List (Lit Value))
    {F F' : List (Atom Value)} (h : F ⊆ F') (s : Subst Value) :
    matchAll lits F s ⊆ matchAll lits F' s := by
  induction lits generalizing s with
  | nil => intro x hx; exact hx
  | cons l rest ih =>
    intro x hx
    simp only [matchAll] at hx ⊢
    simp only [List.mem_flatMap, List.mem_filterMap] at hx ⊢
    obtain ⟨a, ⟨b, hb, hmatch⟩, hx⟩ := hx
    exact ⟨a, ⟨b, h hb, hmatch⟩, ih a hx⟩

/-- Firing is monotone in the fact set. -/
theorem Rule.fire_mono [DecidableEq Value] (r : Rule Value) {F F' : List (Atom Value)}
    (h : F ⊆ F') : r.fire F ⊆ r.fire F' := by
  unfold Rule.fire
  split
  · intro a ha
    simp only [List.mem_filterMap] at ha ⊢
    obtain ⟨s, hs, hres⟩ := ha
    exact ⟨s, matchAll_mono r.body h [] hs, hres⟩
  · intro a ha; cases ha

/-- THE OPERATOR IS MONOTONE (02-data-plane §9) — for ALL programs
    (negation-laden rules are inert, so they cannot break it). -/
theorem step_mono [DecidableEq Value] (P : Program Value) {F F' : List (Atom Value)}
    (h : F ⊆ F') : step P F ⊆ step P F' := by
  have hflat : P.flatMap (fun r => r.fire F) ⊆ P.flatMap (fun r => r.fire F') := by
    intro a ha
    simp only [List.mem_flatMap] at ha ⊢
    obtain ⟨r, hr, ha⟩ := ha
    exact ⟨r, hr, r.fire_mono h ha⟩
  intro a ha
  simp only [step, List.mem_append, List.mem_filter] at ha ⊢
  rcases ha with ha | ⟨ha, hnot⟩
  · exact Or.inl (h ha)
  · by_cases hmem : a ∈ F'
    · exact Or.inl hmem
    · exact Or.inr ⟨hflat ha, by rw [decide_eq_true_iff]; exact hmem⟩

/-! ## The bridge: agreement, matcher soundness/completeness -/

/-- Agreement: every BOUND variable of the executable substitution
    takes the value `σ` assigns (lookup reads the first occurrence). -/
def agree (s : Subst Value) (σ : String → Value) : Prop :=
  ∀ x v, s.lookup x = some v → σ x = v

/-- The total grounding extracted from an executable substitution
    (unbound variables fall back to the default — they are never read
    on grounded results). -/
def Subst.sigma [Inhabited Value] (s : Subst Value) : String → Value :=
  fun x => (s.lookup x).getD default

theorem Subst.sigma_agree [Inhabited Value] (s : Subst Value) :
    agree s s.sigma := fun _ _ hv => by simp [Subst.sigma, hv]

/-- lookup finds exactly the first binding of its key. -/
theorem Subst.mem_of_lookup {s : Subst Value} {x : String} {v : Value}
    (h : s.lookup x = some v) : (x, v) ∈ s := by
  induction s with
  | nil => simp [Subst.lookup] at h
  | cons p rest ih =>
    obtain ⟨x', v'⟩ := p
    by_cases hx : x = x'
    · subst hx
      simp only [Subst.lookup, List.lookup, beq_self_eq_true] at h
      injection h with hv
      subst hv
      exact List.mem_cons_self ..
    · simp only [Subst.lookup, List.lookup, beq_false_of_ne hx] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Matching preserves already-bound lookups (bindings are only ever
    ADDED, and only for unbound keys). -/
theorem matchArgs_lookup_preserve [DecidableEq Value] :
    ∀ (pat : List (Term Value)) (vals : List Value) (s s' : Subst Value),
    matchArgs pat vals s = some s' →
    ∀ x v, s.lookup x = some v → s'.lookup x = some v := by
  intro pat
  induction pat with
  | nil =>
    intro vals s s' h x v hv
    cases vals with
    | nil =>
      simp only [matchArgs, Option.some.injEq] at h
      subst h; exact hv
    | cons w wt => simp [matchArgs] at h
  | cons t pt ih =>
    cases t with
    | cst c =>
      intro vals s s' h x v hv
      cases vals with
      | nil => simp [matchArgs] at h
      | cons w wt =>
        simp only [matchArgs] at h
        by_cases hcw : c = w
        · rw [if_pos hcw] at h
          exact ih wt s s' h x v hv
        · rw [if_neg hcw] at h; simp at h
    | var x₀ =>
      intro vals s s' h x v hv
      cases vals with
      | nil => simp [matchArgs] at h
      | cons w wt =>
        simp only [matchArgs] at h
        cases hl : s.lookup x₀ with
        | none =>
          simp only [hl] at h
          by_cases hxx : x = x₀
          · subst hxx; rw [hl] at hv; simp at hv
          · exact ih wt ((x₀, w) :: s) s' h x v (by
              simp only [Subst.lookup, List.lookup, beq_false_of_ne hxx]
              exact hv)
        | some w' =>
          simp only [hl] at h
          by_cases hww : w' = w
          · rw [if_pos hww] at h
            exact ih wt s s' h x v hv
          · rw [if_neg hww] at h; simp at h

/-- The VALUE multiset of a substitution (all bound values). -/
def Subst.vals (s : Subst Value) : List Value := s.map (·.2)

/-- A lookup result's value is always among the substitution's values. -/
theorem Subst.val_of_lookup {s : Subst Value} {x : String} {u : Value}
    (h : s.lookup x = some u) : u ∈ s.vals := by
  induction s with
  | nil => simp [Subst.lookup] at h
  | cons p rest ih =>
    obtain ⟨x', v'⟩ := p
    by_cases hx : x = x'
    · rw [hx] at h
      simp only [Subst.lookup, List.lookup, beq_self_eq_true] at h
      obtain hv' : v' = u := Option.some.inj h
      simp only [Subst.vals, List.mem_map]
      exact ⟨(x', v'), by simp, hv'⟩
    · simp only [Subst.lookup, List.lookup, beq_false_of_ne hx] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Matching never invents values: every value bound by the result came
    from the input substitution or from the matched values. -/
theorem matchArgs_val_source [DecidableEq Value] :
    ∀ (pat : List (Term Value)) (vals : List Value) (s s' : Subst Value),
    matchArgs pat vals s = some s' →
    ∀ u, u ∈ s'.vals → u ∈ s.vals ∨ u ∈ vals := by
  intro pat
  induction pat with
  | nil =>
    intro vals s s' h u hu
    cases vals with
    | nil =>
      simp only [matchArgs, Option.some.injEq] at h
      subst h; exact Or.inl hu
    | cons w wt => simp [matchArgs] at h
  | cons t pt ih =>
    cases t with
    | cst c =>
      intro vals s s' h u hu
      cases vals with
      | nil => simp [matchArgs] at h
      | cons w wt =>
        simp only [matchArgs] at h
        by_cases hcw : c = w
        · rw [if_pos hcw] at h
          rcases ih wt s s' h u hu with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by simp [h2])
        · rw [if_neg hcw] at h; simp at h
    | var x₀ =>
      intro vals s s' h u hu
      cases vals with
      | nil => simp [matchArgs] at h
      | cons w wt =>
        simp only [matchArgs] at h
        cases hl : s.lookup x₀ with
        | none =>
          simp only [hl] at h
          rcases ih wt ((x₀, w) :: s) s' h u hu with hmem | huw
          · have hv2 : u = w ∨ u ∈ s.vals := by
              simpa [Subst.vals, List.mem_map] using hmem
            rcases hv2 with h12 | hmem
            · exact Or.inr (by simp [h12])
            · exact Or.inl hmem
          · exact Or.inr (by simp [huw])
        | some w' =>
          simp only [hl] at h
          by_cases hww : w' = w
          · rw [if_pos hww] at h
            rcases ih wt s s' h u hu with h1 | h2
            · exact Or.inl h1
            · exact Or.inr (by simp [h2])
          · rw [if_neg hww] at h; simp at h
/-- Matcher SOUNDNESS: a successful match grounds the pattern
    correctly under any σ the result agrees with. -/
theorem matchArgs_ground [DecidableEq Value] :
    ∀ (pat : List (Term Value)) (vals : List Value) (s s' : Subst Value)
      (σ : String → Value),
    agree s' σ → matchArgs pat vals s = some s' → pat.map (sub σ) = vals := by
  intro pat
  induction pat with
  | nil =>
    intro vals s s' σ _ h
    cases vals with
    | nil =>
      simp only [matchArgs, Option.some.injEq] at h
      subst h; rfl
    | cons w wt => simp [matchArgs] at h
  | cons t pt ih =>
    cases t with
    | cst c =>
      intro vals s s' σ hag h
      cases vals with
      | nil => simp [matchArgs] at h
      | cons w wt =>
        simp only [matchArgs, List.map_cons, sub] at h ⊢
        by_cases hcw : c = w
        · rw [if_pos hcw] at h
          rw [ih wt s s' σ hag h, hcw]
        · rw [if_neg hcw] at h; simp at h
    | var x₀ =>
      intro vals s s' σ hag h
      cases vals with
      | nil => simp [matchArgs] at h
      | cons w wt =>
        simp only [matchArgs, List.map_cons, sub] at h ⊢
        cases hl : s.lookup x₀ with
        | none =>
          simp only [hl] at h
          have hpt := ih wt ((x₀, w) :: s) s' σ hag h
          rw [hpt]
          -- the fresh head binding survives to the end
          have hpres := matchArgs_lookup_preserve pt wt ((x₀, w) :: s) s' h x₀ w (by
            simp [Subst.lookup])
          rw [hag _ _ hpres]
        | some w' =>
          simp only [hl] at h
          by_cases hww : w' = w
          · rw [if_pos hww] at h
            have hpt := ih wt s s' σ hag h
            have hpres' := matchArgs_lookup_preserve pt wt s s' h x₀ w' hl
            rw [hpt, hag _ _ hpres', hww]
          · rw [if_neg hww] at h; simp at h

/-- Matcher COMPLETENESS: whenever a total grounding instantiates the
    pattern to the values, the matcher finds a substitution that
    agrees with it and binds every pattern variable. -/
theorem matchArgs_complete [DecidableEq Value] :
    ∀ (pat : List (Term Value)) (vals : List Value) (s : Subst Value)
      (σ : String → Value),
    agree s σ → pat.map (sub σ) = vals →
    ∃ s', matchArgs pat vals s = some s' ∧ agree s' σ ∧
      ∀ x, x ∈ pat.flatMap Term.vars → (s'.lookup x).isSome := by
  intro pat
  induction pat with
  | nil =>
    intro vals s σ hag h
    cases vals with
    | nil => exact ⟨s, rfl, hag, by simp⟩
    | cons w wt => simp at h
  | cons t pt ih =>
    cases t with
    | cst c =>
      intro vals s σ hag h
      cases vals with
      | nil => simp at h
      | cons w wt =>
        simp only [List.map_cons, sub] at h
        injection h with h1 h2
        obtain ⟨s', h1', h2', h3'⟩ := ih wt s σ hag h2
        exact ⟨s', by simp only [matchArgs, if_pos h1]; exact h1', h2', h3'⟩
    | var x₀ =>
      intro vals s σ hag h
      cases vals with
      | nil => simp at h
      | cons w wt =>
        simp only [List.map_cons, sub] at h
        injection h with h1 h2
        -- h1 : σ x₀ = w
        cases hl : s.lookup x₀ with
        | none =>
          have hag' : agree ((x₀, w) :: s) σ := by
            intro x' u hu
            by_cases hxx : x' = x₀
            · rw [hxx] at hu ⊢
              simp only [Subst.lookup, List.lookup, beq_self_eq_true] at hu
              exact h1.trans (Option.some.inj hu)
            · simp only [Subst.lookup, List.lookup, beq_false_of_ne hxx] at hu
              exact hag x' u hu
          obtain ⟨s'', h1', h2', h3'⟩ := ih wt ((x₀, w) :: s) σ hag' h2
          refine ⟨s'', ?_, h2', ?_⟩
          · simp only [matchArgs, hl]
            exact h1'
          · intro x hxv
            by_cases hxx : x = x₀
            · rw [hxx]
              have hpres := matchArgs_lookup_preserve pt wt ((x₀, w) :: s) s'' h1' x₀ w (by
                simp [Subst.lookup])
              simp [hpres]
            · exact h3' x (by
                simp only [List.mem_flatMap] at hxv ⊢
                obtain ⟨t, ht, hxv⟩ := hxv
                refine ⟨t, ?_, hxv⟩
                rcases List.mem_cons.1 ht with ht1 | ht
                · subst ht1
                  simp only [Term.vars, List.mem_cons] at hxv
                  rcases hxv with hx1 | hx2
                  · exact absurd hx1 hxx
                  · exact absurd hx2 (by simp)
                · exact ht)
        | some w' =>
          have hw'w : w' = w := by rw [← h1]; exact (hag x₀ w' hl).symm
          obtain ⟨s'', h1', h2', h3'⟩ := ih wt s σ hag h2
          refine ⟨s'', ?_, h2', ?_⟩
          · simp only [matchArgs, hl, if_pos hw'w]
            exact h1'
          · intro x hxv
            by_cases hxx : x = x₀
            · rw [hxx]
              have hpres := matchArgs_lookup_preserve pt wt s s'' h1' x₀ w' hl
              simp [hpres]
            · exact h3' x (by
                simp only [List.mem_flatMap] at hxv ⊢
                obtain ⟨t, ht, hxv⟩ := hxv
                refine ⟨t, ?_, hxv⟩
                rcases List.mem_cons.1 ht with ht1 | ht
                · subst ht1
                  simp only [Term.vars, List.mem_cons] at hxv
                  rcases hxv with hx1 | hx2
                  · exact absurd hx1 hxx
                  · exact absurd hx2 (by simp)
                · exact ht)

/-! ## The matchAll bridge: lookup preservation, value provenance, grounding -/

/-- matchAll preserves already-bound lookups along produced chains. -/
theorem matchAll_lookup_preserve [DecidableEq Value] (lits : List (Lit Value)) :
    ∀ (F : List (Atom Value)) (s s' : Subst Value),
    s' ∈ matchAll lits F s → ∀ x u, s.lookup x = some u → s'.lookup x = some u := by
  induction lits with
  | nil =>
    intro F s s' h x u hu
    simp only [matchAll, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact hu
    · cases h
  | cons l rest ih =>
    intro F s s' h x u hu
    simp only [matchAll, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨a, ⟨b, hb, hmatch⟩, hrest⟩ := h
    have hargs : matchArgs l.args b.args s = some a := by
      simp only [Lit.matchLit] at hmatch
      by_cases hpe : l.pred = b.pred
      · rw [if_pos hpe] at hmatch; exact hmatch
      · rw [if_neg hpe] at hmatch; simp at hmatch
    exact ih F a s' hrest x u (matchArgs_lookup_preserve l.args b.args s a hargs x u hu)

/-- matchAll never invents values. -/
theorem matchAll_val_source [DecidableEq Value] (lits : List (Lit Value)) :
    ∀ (F : List (Atom Value)) (s s' : Subst Value),
    s' ∈ matchAll lits F s →
    ∀ u, u ∈ s'.vals → u ∈ s.vals ∨ ∃ b ∈ F, u ∈ b.args := by
  induction lits with
  | nil =>
    intro F s s' h u hu
    simp only [matchAll, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact Or.inl hu
    · cases h
  | cons l rest ih =>
    intro F s s' h u hu
    simp only [matchAll, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨a, ⟨b, hb, hmatch⟩, hrest⟩ := h
    have hargs : matchArgs l.args b.args s = some a := by
      simp only [Lit.matchLit] at hmatch
      by_cases hpe : l.pred = b.pred
      · rw [if_pos hpe] at hmatch; exact hmatch
      · rw [if_neg hpe] at hmatch; simp at hmatch
    rcases ih F a s' hrest u hu with h1 | h2
    · rcases matchArgs_val_source l.args b.args s a hargs u h1 with h3 | h4
      · exact Or.inl h3
      · exact Or.inr ⟨b, hb, h4⟩
    · exact Or.inr h2

/-- applyAll's result length. -/
theorem Subst.applyAll_length (s : Subst Value) (ts : List (Term Value)) (vs : List Value)
    (h : s.applyAll ts = some vs) : vs.length = ts.length := by
  induction ts generalizing s vs with
  | nil =>
    simp only [Subst.applyAll, Option.some.injEq] at h
    subst h; rfl
  | cons t' ts' ih =>
    simp only [Subst.applyAll, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, vs', hvs, heq⟩ := h
    rw [← heq]
    simp only [List.length_cons, ih s vs' hvs]

/-- applyAll computes the σ-grounding of the terms (for any agreeing σ). -/
theorem Subst.applyAll_ground (s : Subst Value) (ts : List (Term Value)) (vs : List Value)
    (σ : String → Value) (hag : agree s σ) (h : s.applyAll ts = some vs) :
    ts.map (sub σ) = vs := by
  induction ts generalizing s vs with
  | nil =>
    simp only [Subst.applyAll, Option.some.injEq] at h
    subst h; rfl
  | cons t' ts' ih =>
    simp only [Subst.applyAll, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, vs', hvs, heq⟩ := h
    cases t' with
    | cst c =>
      have hcv : c = v := Option.some.inj (by simpa [Subst.apply] using hv)
      rw [← heq, List.map_cons, show sub σ (Term.cst c) = v from by simp [sub, hcv],
        ih s vs' hag hvs]
    | var x =>
      have hxv : σ x = v := hag x v (by simpa [Subst.apply] using hv)
      rw [← heq, List.map_cons, show sub σ (Term.var x) = v from by simp [sub, hxv],
        ih s vs' hag hvs]

/-- applyAll grounds every term when every variable is bound. -/
theorem Subst.applyAll_bound (s : Subst Value) (ts : List (Term Value))
    (σ : String → Value) (hag : agree s σ)
    (hb : ∀ x, x ∈ ts.flatMap Term.vars → (s.lookup x).isSome = true) :
    s.applyAll ts = some (ts.map (sub σ)) := by
  induction ts with
  | nil => rfl
  | cons t' ts' ih =>
    simp only [Subst.applyAll]
    cases t' with
    | cst c =>
      rw [ih (fun x hx => hb x (by
        rcases List.mem_flatMap.1 hx with ⟨t, ht, hxt⟩
        exact List.mem_flatMap.2 ⟨t, List.mem_cons_of_mem _ ht, hxt⟩))]
      simp [Subst.apply, sub]
    | var x =>
      have hx := hb x (List.mem_flatMap.2 ⟨Term.var x, List.mem_cons_self ..,
        by simp [Term.vars]⟩)
      cases hl : s.lookup x with
      | none => rw [hl] at hx; simp at hx
      | some w =>
        have hxw : w = σ x := (hag x w hl).symm
        simp only [Subst.apply, hl]
        rw [ih (fun x hx => hb x (by
          rcases List.mem_flatMap.1 hx with ⟨t, ht, hxt⟩
          exact List.mem_flatMap.2 ⟨t, List.mem_cons_of_mem _ ht, hxt⟩))]
        simp [sub, hxw]

/-- applyAll never invents values. -/
theorem Subst.applyAll_val_source (s : Subst Value) (ts : List (Term Value))
    (vs : List Value) (h : s.applyAll ts = some vs) :
    ∀ u, u ∈ vs → u ∈ s.vals ∨ ∃ t ∈ ts, u ∈ Term.consts t := by
  induction ts generalizing s vs with
  | nil => simp [Subst.applyAll] at h; simp [h]
  | cons t' ts' ih =>
    simp only [Subst.applyAll, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, vs', hvs, heq⟩ := h
    intro u hu
    rw [← heq] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · cases t' with
      | cst c =>
        have hcv : c = u := Option.some.inj (by simpa [Subst.apply] using hv)
        exact Or.inr ⟨Term.cst c, List.mem_cons_self .., by simp [Term.consts, hcv]⟩
      | var x => exact Or.inl (Subst.val_of_lookup (by simpa [Subst.apply] using hv))
    · rcases ih s vs' hvs u hu with h1 | h2
      · exact Or.inl h1
      · obtain ⟨t, ht, hconst⟩ := h2
        exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, hconst⟩

/-- matchAll SOUNDNESS: every produced substitution grounds every body
    literal against a fact of `F`. -/
theorem matchAll_ground [DecidableEq Value] (lits : List (Lit Value)) :
    ∀ (F : List (Atom Value)) (s s' : Subst Value) (σ : String → Value),
    agree s' σ → s' ∈ matchAll lits F s →
    ∀ l ∈ lits, ∃ b ∈ F, b.pred = l.pred ∧ b.args = l.args.map (sub σ) := by
  induction lits with
  | nil => intro F s s' σ _ h l hl; cases hl
  | cons l rest ih =>
    intro F s s' σ hag h
    simp only [matchAll, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨a, ⟨b, hb, hmatch⟩, hrest⟩ := h
    have haag : agree a σ := fun x u hu =>
      hag x u (matchAll_lookup_preserve rest F a s' hrest x u hu)
    by_cases hpe : l.pred = b.pred
    · have hargs : matchArgs l.args b.args s = some a := by
        simp only [Lit.matchLit, if_pos hpe] at hmatch; exact hmatch
      have hground := matchArgs_ground l.args b.args s a σ haag hargs
      intro l' hl'
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact ⟨b, hb, hpe.symm, hground.symm⟩
      · exact ih F a s' σ hag hrest l' hl'
    · simp only [Lit.matchLit, if_neg hpe] at hmatch; simp at hmatch

/-- matchAll COMPLETENESS: a grounding satisfying every body literal is
    found by the matcher, with every body variable bound. -/
theorem matchAll_complete [DecidableEq Value] (lits : List (Lit Value)) :
    ∀ (F : List (Atom Value)) (σ : String → Value) (s : Subst Value),
    agree s σ →
      (List.all (lits.map (fun l : Lit Value => (⟨l.pred, l.args.map (sub σ)⟩ : Atom Value)))
        (fun a => decide (a ∈ F))) = true →
      ∃ s', s' ∈ matchAll lits F s ∧ agree s' σ ∧
        ∀ x, x ∈ lits.flatMap Lit.vars → (s'.lookup x).isSome = true := by
  induction lits with
  | nil =>
    intro F σ s hag _
    exact ⟨s, by simp [matchAll], hag, by simp⟩
  | cons l rest ih =>
    intro F σ s hag hsat
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hsat
    obtain ⟨hm, htail⟩ := hsat
    have hm : ⟨l.pred, l.args.map (sub σ)⟩ ∈ F := decide_eq_true_iff.1 hm
    have hself : l.pred = (⟨l.pred, l.args.map (sub σ)⟩ : Atom Value).pred := rfl
    obtain ⟨s₁, h1, h2, h3⟩ :=
      matchArgs_complete l.args (l.args.map (sub σ)) s σ hag rfl
    have hmatch : l.matchLit ⟨l.pred, l.args.map (sub σ)⟩ s = some s₁ := by
      simp only [Lit.matchLit]; exact h1
    obtain ⟨s₂, hrest, h2', h3'⟩ := ih F σ s₁ h2 htail
    have hmem : s₂ ∈ matchAll (l :: rest) F s := by
      rw [matchAll]
      exact List.mem_flatMap.2 ⟨s₁,
        List.mem_filterMap.2 ⟨⟨l.pred, l.args.map (sub σ)⟩, hm, hmatch⟩, hrest⟩
    refine ⟨s₂, hmem, h2', ?_⟩
    intro x hxv
    rcases List.mem_append.1 (show x ∈ Lit.vars l ++ rest.flatMap Lit.vars from
      by simpa using hxv) with hx1 | hx2
    · have hx3 := h3 x hx1
      cases hl : s₁.lookup x with
      | none => rw [hl] at hx3; simp at hx3
      | some u =>
        have hpres := matchAll_lookup_preserve rest F s₁ s₂ hrest x u hl
        simp [hpres]
    · exact h3' x (by simpa using hx2)

/-! ## The fire/step bridge against the spec reading -/

theorem Rule.fire_eq [DecidableEq Value] {r : Rule Value} {F : List (Atom Value)}
    (h : r.body.all (fun l => l.positive = true) = true) :
    r.fire F =
      (matchAll r.body F []).filterMap fun s =>
        (s.applyAll r.headArgs).map (⟨r.headPred, ·⟩) := by
  unfold Rule.fire; rw [if_pos h]

theorem Rule.fire_of_not_all_pos [DecidableEq Value] {r : Rule Value}
    {F : List (Atom Value)}
    (h : r.body.all (fun l => l.positive = true) = false) : r.fire F = [] := by
  unfold Rule.fire
  rw [if_neg (by intro hc; rw [hc] at h; simp at h)]

theorem Rule.safe_body_pos {r : Rule Value} (h : r.safe = true) :
    r.body.all (fun l => l.positive = true) = true := by
  simp only [Rule.safe, Bool.and_eq_true] at h; exact h.1.1

theorem Rule.safe_head_bound {r : Rule Value} (h : r.safe = true) :
    ∀ x ∈ r.headArgs.flatMap Term.vars, x ∈ r.bound := by
  simp only [Rule.safe, Bool.and_eq_true, List.all_eq_true] at h
  intro x hx
  exact List.contains_iff_mem.1 (h.1.2 x hx)

/-- Firing a rule produces a one-step CONSEQUENCE (the spec reading):
    some total grounding satisfies the body and grounds the head. -/
theorem Rule.fire_conseq [DecidableEq Value] [Inhabited Value] (r : Rule Value)
    (F : List (Atom Value)) (a : Atom Value) (h : a ∈ r.fire F) :
    ∃ σ, (∀ l ∈ r.body, l.sat σ (fun b => b ∈ F)) ∧
      ground σ r.headPred r.headArgs = a := by
  cases hba : r.body.all (fun l => l.positive = true) with
  | false =>
    rw [Rule.fire_of_not_all_pos hba] at h
    exact absurd h (by simp)
  | true =>
    rw [Rule.fire_eq hba] at h
    simp only [List.mem_filterMap] at h
    obtain ⟨s, hs, hres⟩ := h
    obtain ⟨vs, hv, hva⟩ := Option.map_eq_some_iff.1 hres
    refine ⟨s.sigma, ?_, ?_⟩
    · intro l hl
      have hpos : l.positive = true := by simpa using List.all_eq_true.1 hba l hl
      obtain ⟨b, hb, hbp, hba2⟩ :=
        matchAll_ground r.body F [] s s.sigma (Subst.sigma_agree s) hs l hl
      exact ⟨hpos, by
        show ground s.sigma l.pred l.args ∈ F
        have heq : (ground s.sigma l.pred l.args : Atom Value) = b :=
          (atom_ext_iff _ _).2 ⟨hbp.symm, hba2.symm⟩
        rw [heq]; exact hb⟩
    · show (⟨r.headPred, r.headArgs.map (sub s.sigma)⟩ : Atom Value) = a
      rw [Subst.applyAll_ground s r.headArgs vs s.sigma (Subst.sigma_agree s) hv]
      exact hva

/-- Conversely, a one-step consequence over a SAFE rule is produced by
    firing (the matcher finds the grounding — matcher completeness). -/
theorem Rule.conseq_fire [DecidableEq Value] (r : Rule Value)
    (F : List (Atom Value)) (a : Atom Value) (σ : String → Value)
    (hsafe : r.safe = true) (hbody : ∀ l ∈ r.body, l.sat σ (fun b => b ∈ F))
    (hhead : ground σ r.headPred r.headArgs = a) : a ∈ r.fire F := by
  have hpos := Rule.safe_body_pos hsafe
  have hboundbody : r.bound = r.body.flatMap Lit.vars := by
    simp only [Rule.bound, List.filter_eq_self.2 (fun l hl => List.all_eq_true.1 hpos l hl)]
  obtain ⟨s₁, hs₁, hs₁ag, hs₁b⟩ :=
    matchAll_complete r.body F σ []
      (fun x u hu => by simp [Subst.lookup] at hu)
      (List.all_eq_true.2 (fun a ha => by
        simp only [List.mem_map] at ha
        obtain ⟨l, hl, rfl⟩ := ha
        exact decide_eq_true_iff.2 (hbody l hl).2))
  have hb : s₁.applyAll r.headArgs = some (r.headArgs.map (sub σ)) :=
    Subst.applyAll_bound s₁ r.headArgs σ hs₁ag (fun x hx => by
      have hx' := Rule.safe_head_bound hsafe x hx
      rw [hboundbody] at hx'
      exact hs₁b x hx')
  rw [Rule.fire_eq hpos, List.mem_filterMap]
  exact ⟨s₁, hs₁, by
    simp only [hb, Option.map_some, Option.some.injEq]
    exact hhead⟩

theorem mem_step_of_fire [DecidableEq Value] {P : Program Value} {F : List (Atom Value)}
    {a : Atom Value} (h : a ∈ P.flatMap (fun r => r.fire F)) :
    ∃ r ∈ P, a ∈ r.fire F := by
  simp only [List.mem_flatMap] at h
  obtain ⟨r, hr, ha⟩ := h
  exact ⟨r, hr, ha⟩

/-- THE BRIDGE (15-patterns #1): the executable operator and the spec
    reading of one step agree — for safe programs, both directions. -/
theorem step_iff_conseq [DecidableEq Value] [Inhabited Value] (P : Program Value)
    (F : List (Atom Value)) (a : Atom Value) (hsafe : ∀ r ∈ P, r.safe = true) :
    a ∈ step P F ↔ a ∈ F ∨ Conseq P (fun b => b ∈ F) a := by
  simp only [step, List.mem_append, List.mem_filter, decide_eq_true_iff]
  constructor
  · rintro (h1 | ⟨h2, h3⟩)
    · exact Or.inl h1
    · obtain ⟨r, hr, ha⟩ := mem_step_of_fire h2
      obtain ⟨σ, hb, hh⟩ := r.fire_conseq F a ha
      exact Or.inr ⟨r, hr, σ, hb, hh⟩
  · rintro (h1 | ⟨r, hr, σ, hb, hh⟩)
    · exact Or.inl h1
    · by_cases hmem : a ∈ F
      · exact Or.inl hmem
      · exact Or.inr
          ⟨List.mem_flatMap.2 ⟨r, hr, r.conseq_fire F a σ (hsafe r hr) hb hh⟩, hmem⟩

/-! ## The finite fact universe + the closure theorem -/

/-- Well-formed ground atom: right arity. -/
abbrev Atom.wf (a : Atom Value) : Prop := a.args.length = a.pred.arity

/-- Well-formed rule: the head's term count matches the head's arity. -/
abbrev Rule.wf (r : Rule Value) : Prop := r.headArgs.length = r.headPred.arity

/-- The finite VALUE universe: the EDB's values + the program's
    constants. Derivation never invents values (the closure theorem),
    so this is where the fragment's finiteness lives — no arithmetic
    generation, by construction. -/
def univ (P : Program Value) (E : List (Atom Value)) : List Value :=
  (E.flatMap (·.args)) ++ P.flatMap (·.consts)

/-- All value-tuples of a given length over `U`. -/
def arityTuples : Nat → List Value → List (List Value)
  | 0, _ => [[]]
  | n + 1, U => (arityTuples n U).flatMap (fun t => U.map (· :: t))

/-- All ground atoms of predicate `p` over the value list `U`. -/
def atomsOf (p : Pred) (U : List Value) : List (Atom Value) :=
  (arityTuples p.arity U).map (Atom.mk p)

theorem mem_arityTuples_iff {n : Nat} {U : List Value} {t : List Value} :
    t ∈ arityTuples n U ↔ t.length = n ∧ ∀ v ∈ t, v ∈ U := by
  induction n generalizing t with
  | zero =>
    simp only [arityTuples, List.mem_cons]
    constructor
    · rintro (rfl | h)
      · exact ⟨rfl, by simp⟩
      · exact absurd h (by simp)
    · intro h
      rw [List.length_eq_zero_iff.1 h.1]
      exact Or.inl rfl
  | succ n ih =>
    simp only [arityTuples, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨t', ht', v, hv, rfl⟩
      obtain ⟨hl, he⟩ := ih.1 ht'
      exact ⟨by simp [hl], fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hv
        · exact he w hw⟩
    · rintro ⟨hl, he⟩
      cases t with
      | nil => simp at hl
      | cons v t' =>
        refine ⟨t', ih.2 ⟨by simpa using hl, fun w hw => he w (by simp [hw])⟩,
          v, he v (by simp), rfl⟩

theorem mem_atomsOf_iff {p : Pred} {U : List Value} {a : Atom Value} :
    a ∈ atomsOf p U ↔
      a.pred = p ∧ a.args.length = p.arity ∧ ∀ v ∈ a.args, v ∈ U := by
  simp only [atomsOf, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨hl, he⟩ := mem_arityTuples_iff.1 ht
    exact ⟨rfl, hl, he⟩
  · rintro ⟨hp, hl, he⟩
    subst hp
    exact ⟨a.args, mem_arityTuples_iff.2 ⟨hl, he⟩, rfl⟩

/-- Every ground atom over the program's predicates and the value
    universe — the fragment's finite state space. The iteration's
    height bound is this list's LENGTH. -/
def possible (P : Program Value) (E : List (Atom Value)) : List (Atom Value) :=
  ((E.map (·.pred)) ++ (P.map (·.headPred))).flatMap
    (fun p => atomsOf p (univ P E))

theorem mem_possible_of_mem {P : Program Value} {E : List (Atom Value)} {a : Atom Value}
    (ha : a ∈ E) (hwf : ∀ a ∈ E, a.wf) : a ∈ possible P E := by
  simp only [possible, List.mem_flatMap, List.mem_append, List.mem_map]
  refine ⟨a.pred, Or.inl ⟨a, ha, rfl⟩, ?_⟩
  rw [mem_atomsOf_iff]
  exact ⟨rfl, hwf a ha, fun v hv => by
    simp only [univ, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨a, ha, hv⟩⟩

theorem mem_possible_args {P : Program Value} {E : List (Atom Value)} {b : Atom Value}
    (h : b ∈ possible P E) : ∀ v ∈ b.args, v ∈ univ P E := by
  simp only [possible, List.mem_flatMap] at h
  obtain ⟨p, _, ha⟩ := h
  rw [mem_atomsOf_iff] at ha
  exact ha.2.2

/-- Firing keeps facts inside `possible` (the closure theorem: the
    operator never leaves the finite state space). -/
theorem Rule.mem_possible_of_fire [DecidableEq Value] {P : Program Value}
    {E F : List (Atom Value)} {r : Rule Value} {a : Atom Value}
    (hF : ∀ b ∈ F, b ∈ possible P E) (hr : r ∈ P) (hwf : r.wf)
    (h : a ∈ r.fire F) : a ∈ possible P E := by
  cases hba : r.body.all (fun l => l.positive = true) with
  | false =>
    rw [Rule.fire_of_not_all_pos hba] at h
    exact absurd h (by simp)
  | true =>
    rw [Rule.fire_eq hba] at h
    simp only [List.mem_filterMap] at h
    obtain ⟨s, hs, hres⟩ := h
    obtain ⟨vs, hv, hva⟩ := Option.map_eq_some_iff.1 hres
    simp only [possible, List.mem_flatMap, List.mem_append, List.mem_map]
    refine ⟨r.headPred, Or.inr ⟨r, hr, rfl⟩, ?_⟩
    rw [mem_atomsOf_iff, ← hva]
    refine ⟨rfl, ?_, ?_⟩
    · rw [Subst.applyAll_length s r.headArgs vs hv, hwf]
    · intro v hvv
      -- provenance: every head value is a program constant or a fact value
      rcases Subst.applyAll_val_source s r.headArgs vs hv v hvv with h1 | h2
      · -- v is bound in s, whose bindings come from matched facts
        rcases matchAll_val_source r.body F [] s hs v h1 with h3 | h4
        · exact absurd h3 (by simp [Subst.vals])
        · obtain ⟨b, hbF, hvb⟩ := h4
          exact mem_possible_args (hF b hbF) v hvb
      · obtain ⟨t, ht, hconst⟩ := h2
        cases t with
        | cst c =>
          simp only [univ, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨r, hr, by
            simp only [Rule.consts, List.mem_append, List.mem_flatMap]
            exact Or.inl ⟨Term.cst c, ht, by simpa [Term.consts] using hconst⟩⟩
        | var x => exact absurd hconst (by simp [Term.consts])

theorem step_mem_possible [DecidableEq Value] {P : Program Value}
    {E F : List (Atom Value)} (_hwf : ∀ a ∈ E, a.wf) (hpwf : ∀ r ∈ P, r.wf)
    (hF : ∀ b ∈ F, b ∈ possible P E) {a : Atom Value} (h : a ∈ step P F) :
    a ∈ possible P E := by
  simp only [step, List.mem_append, List.mem_filter, decide_eq_true_iff] at h
  rcases h with h | ⟨h, _⟩
  · exact hF a h
  · obtain ⟨r, hr, ha⟩ := mem_step_of_fire h
    exact r.mem_possible_of_fire hF hr (hpwf r hr) ha

/-! ## The iteration, the height bound, the stabilization theorem -/

/-- Bottom-up iteration of the consequence operator. -/
def iter [DecidableEq Value] (P : Program Value) (E : List (Atom Value)) :
    Nat → List (Atom Value)
  | 0 => E
  | n + 1 => step P (iter P E n)

/-- The height bound: the number of representable ground atoms — a
    THEORETIC bound (the fragment's finite state space), not a cap. -/
def height (P : Program Value) (E : List (Atom Value)) : Nat := (possible P E).length

/-- The evaluator: bottom-up to fixpoint with the honest fuel. -/
def eval [DecidableEq Value] (P : Program Value) (E : List (Atom Value)) :
    List (Atom Value) := iter P E (height P E)

/-- How many representable atoms the fact set is still missing. -/
def missing [DecidableEq Value] (P : Program Value) (E : List (Atom Value))
    (F : List (Atom Value)) : Nat :=
  ((possible P E).filter (fun a => decide (a ∉ F))).length

theorem iter_subset_possible [DecidableEq Value] (P : Program Value)
    (E : List (Atom Value)) (hwf : ∀ a ∈ E, a.wf) (hpwf : ∀ r ∈ P, r.wf) :
    ∀ n a, a ∈ iter P E n → a ∈ possible P E := by
  intro n
  induction n with
  | zero => intro a ha; exact mem_possible_of_mem ha hwf
  | succ n ih =>
    intro a ha
    exact step_mem_possible hwf hpwf (fun b hb => ih b hb) (by simpa only [iter] using ha)

/-- Each non-fixpoint step strictly decreases the missing count — the
    engine of the stabilization theorem. -/
theorem missing_step_lt [DecidableEq Value] {P : Program Value}
    {E F : List (Atom Value)} (hwf : ∀ a ∈ E, a.wf) (hpwf : ∀ r ∈ P, r.wf)
    (hF : ∀ b ∈ F, b ∈ possible P E) (hne : step P F ≠ F) :
    missing P E (step P F) < missing P E F := by
  have hstep : step P F =
      F ++ (P.flatMap (fun r => r.fire F)).filter (fun a => decide (a ∉ F)) := rfl
  -- the newly-derived part is nonempty when the step moves
  have hnewne : (P.flatMap (fun r => r.fire F)).filter (fun a => decide (a ∉ F)) ≠ [] := by
    intro h0
    rw [hstep, h0, List.append_nil] at hne
    exact hne rfl
  obtain ⟨a₀, ha₀⟩ := List.exists_mem_of_ne_nil _ hnewne
  have ha₀F : a₀ ∉ F := by
    have hmem := List.mem_filter.1 ha₀
    exact decide_eq_true_iff.1 hmem.2
  have ha₀pos : a₀ ∈ possible P E :=
    step_mem_possible hwf hpwf hF (by rw [hstep]; exact List.mem_append.2 (Or.inr ha₀))
  -- split the missing count over the appended `new`
  have key : ∀ a ∈ possible P E,
      decide (a ∉ F ++ (P.flatMap (fun r => r.fire F)).filter (fun a => decide (a ∉ F))) =
        (decide (a ∉ F) && decide (a ∉ (P.flatMap (fun r => r.fire F)).filter
          (fun a => decide (a ∉ F)))) := by
    intro a _
    by_cases h1 : a ∈ F <;> by_cases h2 : a ∈ (P.flatMap (fun r => r.fire F)).filter
      (fun a => decide (a ∉ F)) <;> simp [h1]
  rw [missing, hstep, List.filter_congr key, List.filter_congr
    (fun a (_ : a ∈ possible P E) => Bool.and_comm _ _), ← List.filter_filter, missing]
  refine length_filter_lt (a := a₀)
    (l := List.filter (fun a => decide (a ∉ F)) (possible P E)) ?_ ?_
  · exact List.mem_filter.2 ⟨ha₀pos, decide_eq_true_iff.2 ha₀F⟩
  · exact decide_eq_false_iff_not.2 (fun h => h ha₀)

theorem step_eq_self_of_missing_zero [DecidableEq Value] {P : Program Value}
    {E F : List (Atom Value)} (_hwf : ∀ a ∈ E, a.wf) (hpwf : ∀ r ∈ P, r.wf)
    (hF : ∀ b ∈ F, b ∈ possible P E) (h0 : missing P E F = 0) : step P F = F := by
  have hsub : ∀ a, a ∈ possible P E → a ∈ F := by
    intro a ha
    rw [missing] at h0
    have hnil : (possible P E).filter (fun a => decide (a ∉ F)) = [] :=
      List.length_eq_zero_iff.1 h0
    rw [List.filter_eq_nil_iff] at hnil
    have hmem := hnil a ha
    by_cases hd : a ∈ F
    · exact hd
    · exact absurd (decide_eq_true_iff.2 hd) hmem
  have hnew : (P.flatMap (fun r => r.fire F)).filter (fun a => decide (a ∉ F)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha hdec
    obtain ⟨r, hr, ha'⟩ := mem_step_of_fire ha
    have h3 : a ∈ F := hsub a (r.mem_possible_of_fire hF hr (hpwf r hr) ha')
    exact absurd (decide_eq_true_iff.1 hdec) (fun h => absurd h (by simp [h3]))
  simp only [step, hnew, List.append_nil]

/-- THE STABILIZATION THEOREM (the finite-height discipline, 02 §9):
    the iteration reaches a fixpoint by the height bound — the number of
    representable ground atoms. The fuel is THEORETIC. -/
theorem exists_fix [DecidableEq Value] (P : Program Value) (E : List (Atom Value))
    (hwf : ∀ a ∈ E, a.wf) (hpwf : ∀ r ∈ P, r.wf) :
    ∃ k, k ≤ height P E ∧ step P (iter P E k) = iter P E k := by
  have hbound : missing P E (iter P E 0) ≤ height P E := List.length_filter_le _ _
  by_cases hex : ∃ j, j < missing P E (iter P E 0) ∧ step P (iter P E j) = iter P E j
  · obtain ⟨j, hj, hf⟩ := hex
    exact ⟨j, Nat.le_of_lt (Nat.lt_of_lt_of_le hj hbound), hf⟩
  -- no fixpoint before m₀: the missing count strictly decreases every step
  have hnone : ∀ j, j < missing P E (iter P E 0) → step P (iter P E j) ≠ iter P E j :=
    fun j hj hf => hex ⟨j, hj, hf⟩
  have hdec : ∀ n, (∀ j, j < n → step P (iter P E j) ≠ iter P E j) →
      missing P E (iter P E n) + n ≤ missing P E (iter P E 0) := by
    intro n
    induction n with
    | zero => intro _; omega
    | succ n ih =>
      intro h
      have h1 := ih (fun j hj => h j (by omega))
      have h2 := missing_step_lt (P := P) (E := E) (F := iter P E n) hwf hpwf
        (fun b hb => iter_subset_possible P E hwf hpwf n b hb) (h n (by omega))
      have h3 : missing P E (iter P E (n + 1))
          = missing P E (step P (iter P E n)) := rfl
      omega
  have hzero : missing P E (iter P E (missing P E (iter P E 0))) = 0 := by
    have := hdec (missing P E (iter P E 0)) hnone
    omega
  refine ⟨missing P E (iter P E 0), hbound, ?_⟩
  exact step_eq_self_of_missing_zero hwf hpwf
    (fun b hb => iter_subset_possible P E hwf hpwf _ b hb) hzero

theorem iter_step_superset [DecidableEq Value] (P : Program Value)
    (E : List (Atom Value)) (n : Nat) :
    iter P E n ⊆ iter P E (n + 1) := by
  simp only [iter, step]
  exact fun a ha => List.mem_append.2 (Or.inl ha)

theorem iter_mono [DecidableEq Value] (P : Program Value) (E : List (Atom Value)) :
    ∀ {n m : Nat}, n ≤ m → iter P E n ⊆ iter P E m := by
  intro n m h
  induction h with
  | refl => exact fun a ha => ha
  | step _ ih => exact fun a ha => iter_step_superset P E _ (ih ha)

theorem iter_fix [DecidableEq Value] (P : Program Value) (E : List (Atom Value))
    (n : Nat) (h : step P (iter P E n) = iter P E n) :
    ∀ j, iter P E (n + j) = iter P E n := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => rw [← Nat.add_assoc, iter, ih, h]

/-- THE EVALUATOR IS A FIXPOINT: `eval`'s output is closed under one
    more step — the fuel (the height bound) provably saturates. -/theorem eval_fix [DecidableEq Value] (P : Program Value) (E : List (Atom Value))
    (hwf : ∀ a ∈ E, a.wf) (hpwf : ∀ r ∈ P, r.wf) :
    step P (eval P E) = eval P E := by
  obtain ⟨k, hk, hf⟩ := exists_fix P E hwf hpwf
  have hke : height P E = k + (height P E - k) := (Nat.add_sub_cancel' hk).symm
  have : eval P E = iter P E k := by
    rw [eval, hke, iter_fix P E k hf]
  rw [this, hf]

/-- THE LFP's LEASTNESS: `eval` is below every pre-fixpoint containing
    the EDB — it is THE least fixpoint, not just one. -/
theorem lfp_least [DecidableEq Value] (P : Program Value) (E : List (Atom Value))
    {G : List (Atom Value)} (hE : E ⊆ G) (hG : step P G ⊆ G) : eval P E ⊆ G := by
  have hall : ∀ n, iter P E n ⊆ G := by
    intro n
    induction n with
    | zero => exact hE
    | succ n ih => exact fun a ha => hG (step_mono P ih ha)
  exact hall _

/-! ## Deriv: the inductive least-fixpoint reading + evaluation correctness -/

/-- The PROOF-THEORETIC least fixpoint: an EDB fact, or the σ-head of a
    rule whose grounded body is derivable. Positivity is built into
    `Lit.sat` — a negated literal satisfies nothing (the named
    exclusion). -/
inductive Deriv (P : Program Value) (E : List (Atom Value)) : Atom Value → Prop where
  /-- A fact of the extensional database. -/
  | base {a : Atom Value} : a ∈ E → Deriv P E a
  /-- A rule fires: some grounding satisfies every body literal (in the
      Deriv reading) and grounds the head to `a`. -/
  | fire {r : Rule Value} {a : Atom Value} {σ : String → Value} :
      r ∈ P → (∀ l ∈ r.body, l.positive = true) →
      (∀ l, l ∈ r.body → Deriv P E (ground σ l.pred l.args)) →
      ground σ r.headPred r.headArgs = a → Deriv P E a

/-- Evaluation CORRECTNESS, completeness direction: everything derivable
    is in the evaluator's output (the derivation is honored). -/
theorem Deriv.eval_mem [DecidableEq Value] [Inhabited Value] {P : Program Value}
    {E : List (Atom Value)} {a : Atom Value}
    (hwf : ∀ a' ∈ E, a'.wf) (hpwf : ∀ r ∈ P, r.wf)
    (hsafe : ∀ r ∈ P, r.safe = true) (h : Deriv P E a) : a ∈ eval P E := by
  induction h with
  | base ha =>
    exact iter_mono P E (Nat.zero_le _) ha
  | @fire r a σ hr hb1 hderiv hh ih =>
    have hc : Conseq P (fun b => b ∈ eval P E) a :=
      ⟨r, hr, σ, fun l hl => ⟨hb1 l hl, ih l hl⟩, hh⟩
    have hstep := (step_iff_conseq P (eval P E) a hsafe).2 (Or.inr hc)
    rw [eval_fix P E hwf hpwf] at hstep
    exact hstep

/-- Evaluation CORRECTNESS, soundness direction: everything in the
    evaluator's output has a derivation. -/
theorem eval_deriv [DecidableEq Value] [Inhabited Value] (P : Program Value)
    (E : List (Atom Value)) (hsafe : ∀ r ∈ P, r.safe = true) :
    ∀ n a, a ∈ iter P E n → Deriv P E a := by
  intro n
  induction n with
  | zero => intro a ha; exact Deriv.base ha
  | succ n ih =>
    intro a ha
    obtain h2 | h2 :=
      (step_iff_conseq P (iter P E n) a hsafe).1 (by simpa only [iter] using ha)
    · exact ih a h2
    · obtain ⟨r, hr, σ, hb, hh⟩ := h2
      exact Deriv.fire hr (fun l hl => (hb l hl).1)
        (fun l hl => ih _ (hb l hl).2) hh

/-- THE CORRECTNESS THEOREM (02-data-plane §9's evaluation correctness,
    both directions honest over the finite fragment): the evaluator's
    output IS the least fixpoint of the derivation relation. -/
theorem deriv_iff_eval [DecidableEq Value] [Inhabited Value] (P : Program Value)
    (E : List (Atom Value)) (hwf : ∀ a ∈ E, a.wf) (hpwf : ∀ r ∈ P, r.wf)
    (hsafe : ∀ r ∈ P, r.safe = true) (a : Atom Value) :
    Deriv P E a ↔ a ∈ eval P E :=
  ⟨fun h => h.eval_mem hwf hpwf hsafe, eval_deriv P E hsafe _ a⟩

/-- The evaluator's ENTRY POINT: refuse unsafe programs LOUDLY (the
    rendered error names the rule index and the offending variable —
    15-patterns #16; the refusal's ONE owner is `Program.checked`, which
    `run` routes through), evaluate checked ones. The correctness
    theorems apply to the `.ok` face. -/
def Program.run [DecidableEq Value] [Inhabited Value] (P : Program Value)
    (E : List (Atom Value)) : Except String (List (Atom Value)) :=
  Program.checked P |>.map fun _ => eval P E

end Datalog

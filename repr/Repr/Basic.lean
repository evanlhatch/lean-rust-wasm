/-
# Repr.Basic — the representation discipline

The reviews' §2 (the meaning↔representation split): a domain concept
should not EQUAL its current encoding. A finite map has
representations — association list, sorted array, hash map, serialized
bytes — and none of them IS the map. The discipline:

1. the simple mathematical spec (the abstract carrier `A`);
2. the efficient executable implementation (the concrete carrier `C`);
3. the representation relation `R : Kit.Rel C A` — "c represents a";
4. the operations' preservation fields — an implementation whose
   operations do not preserve the relation DOES NOT CONSTRUCT
   (`pres_init` / `pres_step` / `pres_obs` are the construction gate);
5. the generic client theorem — a client of the abstract interface
   (a token program from the initial state) works over ANY
   representation, because the observations agree on related states.

Isomorphism is deliberately absent: `R` is a relation, not a bijection
(two hash tables with different capacities represent the same map).
The grade honesty is exercised per instance — `Repr.FinMap` shows the
sorted rep's canonicity face and the raw rep's Abstraction grade
(`raw_not_injective`), and never claims the Iso.

The composition discipline: representations compose through a MATCHED
middle (`comp` — the composite relation is `Kit.Rel.comp`, its witness
the shared middle state), the engine's transitivity shape (01 §6).
The construction gate's teeth: `no_ignore_step` — an implementation
that ignores an operation cannot bundle with an abstract step whose
effect is observable through a left-unique relation.

Relation to the landed substrate: this is the zset lane's canonical-rep
discipline GENERALIZED — ZSet's `Weighted` layer is one instance's
shape (the weight function vs the canonical rep); here the relation is
first-class and the interface rides the structure. Core-only: imports
`Kit.Relation` alone (the cone rule).

The five questions (notes/v3/01-core.md):
- root: Universe × Change crossing — the carriers are finite data; the
  client program is the Change face (a token sequence applied to a
  state); the relation is the §6 engine's explicit relation family.
- carrier grade: the honest grade is Abstraction (over, never exact) —
  deliberately NOT `Kit.Iso`/`Kit.Retraction`; the structure CITES the
  carrier (`Kit.Rel` is the engine's relation) and the instance files
  name the grade each representation earns.
- spine reading: none — the lanes' interpretation pairs are the
  consumers; nothing is emitted.
- ladder rung: hand theorems of the small generic kind (01 §7) —
  `client_obs` and `comp` are the ONE generic theorems per shape.
- gate row: Repr's row in Gates.Packages' gated set (the per-library
  axiom sweep covers it); ReprTests.Axioms pins the laws' cones
  (core triple only).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Kit.Relation

namespace Repr

/-! ## The representation discipline -/

/-- THE representation discipline (the reviews' §2, the honest
structure): the abstract carrier `A` (the spec), the concrete carrier
`C` (the implementation), the representation relation `R`, the shared
interface (init + a token-indexed step family + an observer), and the
preservation fields. The fields ARE the construction gate: a concrete
interface whose steps do not keep `R` to the abstract interface's
steps cannot build this structure. -/
structure Represents (Tok Obs C A : Type) where
  /-- The representation relation: `R c a` reads "c represents a".
      A relation, never a bijection — isomorphism is unnecessarily
      strong (different capacities, tombstones, duplicate logs). -/
  R : Kit.Rel C A
  /-- The abstract interface: initial state. -/
  initA : A
  /-- The abstract interface: one step per operation token. -/
  stepA : Tok → A → A
  /-- The abstract interface: the observation. -/
  obsA : A → Obs
  /-- The concrete interface: initial state. -/
  initC : C
  /-- The concrete interface: one step per operation token. -/
  stepC : Tok → C → C
  /-- The concrete interface: the observation. -/
  obsC : C → Obs
  /-- Preservation, initial states: the construction gate. -/
  pres_init : R initC initA
  /-- Preservation, steps: EVERY operation keeps related states
      related — the implementation's correctness contract, stated
      once per token, not per client. -/
  pres_step : ∀ (t : Tok) (c : C) (a : A), R c a → R (stepC t c) (stepA t a)
  /-- Preservation, observations: related states OBSERVE the same.
      The client's only contact with the representation. -/
  pres_obs : ∀ (c : C) (a : A), R c a → obsC c = obsA a

/-! ## The client theorem -/

/-- Run a client program (a token list) on the concrete carrier.
    Left-to-right: the fold's accumulator is the state. -/
def runC (r : Represents Tok Obs C A) (p : List Tok) (c : C) : C :=
  p.foldl (fun acc t => r.stepC t acc) c

/-- Run a client program on the abstract carrier. -/
def runA (r : Represents Tok Obs C A) (p : List Tok) (a : A) : A :=
  p.foldl (fun acc t => r.stepA t acc) a

/-- The states stay related under ANY client program — the per-token
preservation field, lifted over the program by one induction, once
for every representation ever bundled. -/
theorem run_pres (r : Represents Tok Obs C A) :
    ∀ (p : List Tok) (c : C) (a : A), r.R c a → r.R (runC r p c) (runA r p a) := by
  intro p
  induction p with
  | nil => intro c a h; exact h
  | cons t ps ih =>
      intro c a h
      simp only [runC, runA, List.foldl_cons]
      exact ih _ _ (r.pres_step t c a h)

/-- THE GENERIC CLIENT THEOREM (§2's step 5, the honest statement over
the minimal interface): a client of the abstract interface — any token
program from the initial state — observes the SAME result over ANY
representation. The proof is `run_pres` + `pres_obs`; nothing about
the representation beyond its preservation fields is ever used. -/
theorem client_obs (r : Represents Tok Obs C A) (p : List Tok) :
    r.obsC (runC r p r.initC) = r.obsA (runA r p r.initA) :=
  r.pres_obs _ _ (run_pres r p r.initC r.initA r.pres_init)

/-- The client theorem from an arbitrary related start state (the
non-initial form — a client mid-session). -/
theorem client_obs_from (r : Represents Tok Obs C A) (p : List Tok)
    (c : C) (a : A) (h : r.R c a) :
    r.obsC (runC r p c) = r.obsA (runA r p a) :=
  r.pres_obs _ _ (run_pres r p c a h)

/-! ## Composition -/

/-- The discipline's composition (01 §6's transitivity row): C
represents M and M represents A — with the middle MATCHED (the left
leg's abstract interface IS the right leg's concrete interface; the
three equalities are the match's proof obligations, the
`Simulation.trans` `hcomp` precedent) — gives C represents A along the
composite relation `Kit.Rel.comp`, its witness the shared middle
state. The composite's preservation fields chain the legs; no new
induction. -/
def comp {Tok Obs C M A : Type}
    (r₁ : Represents Tok Obs C M) (r₂ : Represents Tok Obs M A)
    (hstep : r₁.stepA = r₂.stepC) (hinit : r₁.initA = r₂.initC)
    (hobs : r₁.obsA = r₂.obsC) : Represents Tok Obs C A where
  R := Kit.Rel.comp r₁.R r₂.R
  initA := r₂.initA
  stepA := r₂.stepA
  obsA := r₂.obsA
  initC := r₁.initC
  stepC := r₁.stepC
  obsC := r₁.obsC
  pres_init := ⟨r₂.initC, by rw [← hinit]; exact r₁.pres_init, r₂.pres_init⟩
  pres_step := by
    intro t c a h
    obtain ⟨m, h1, h2⟩ := h
    have hm := r₂.pres_step t m a h2
    rw [← hstep] at hm
    exact ⟨r₁.stepA t m, r₁.pres_step t c m h1, hm⟩
  pres_obs := by
    intro c a h
    obtain ⟨m, h1, h2⟩ := h
    rw [r₁.pres_obs c m h1, hobs]
    exact r₂.pres_obs m a h2

/-! ## Cross-representation agreement -/

/-- Two representations of the SAME abstract interface agree: the same
program run on both concrete carriers gives the same observation —
each leg equals the shared abstract run (`client_obs` twice), so the
composite collapses. THE statement the tests exercise: same
operations, related states, same abstract results. -/
theorem crossRep_obs {Tok Obs C C' M : Type}
    (r₁ : Represents Tok Obs C M) (r₂ : Represents Tok Obs C' M)
    (hstep : r₂.stepA = r₁.stepA) (hinit : r₂.initA = r₁.initA)
    (hobs : r₂.obsA = r₁.obsA)
    (p : List Tok) :
    r₁.obsC (runC r₁ p r₁.initC) = r₂.obsC (runC r₂ p r₂.initC) := by
  rw [client_obs r₁ p, client_obs r₂ p]
  have h : runA r₂ p r₂.initA = runA r₁ p r₁.initA := by
    show p.foldl (fun acc t => r₂.stepA t acc) r₂.initA
         = p.foldl (fun acc t => r₁.stepA t acc) r₁.initA
    rw [hstep, hinit]
  rw [h, hobs]

/-! ## The construction gate's teeth -/

/-- The construction gate's teeth — the discipline's "doesn't
construct" made loud: a concrete step that IGNORES an operation
(behaves as the identity on token `t`) cannot bundle with an abstract
step whose effect on `a0` is observable, WHEN the relation is
left-unique in the abstract argument (the honest representations'
relation always is: the concrete state determines the abstract one).
Proof: preservation would force the abstract step's effect to vanish
too. The FinMap instance instantiates this for both representations. -/
theorem no_ignore_step {Tok Obs C A : Type} (R : Kit.Rel C A)
    (rstep : Tok → C → C) (astep : Tok → A → A)
    (hfun : ∀ c a a', R c a → R c a' → a = a')
    (c0 : C) (a0 : A) (hR0 : R c0 a0)
    (t : Tok) (hstep : ∀ c, rstep t c = c) (hne : astep t a0 ≠ a0) :
    ¬ ∃ r : Represents Tok Obs C A,
        r.R = R ∧ r.stepC = rstep ∧ r.stepA = astep := by
  rintro ⟨r, hR, hc, ha⟩
  have h : R c0 (astep t a0) := by
    have h0 := r.pres_step t c0 a0 (by rw [hR]; exact hR0)
    rw [ha, hc, hR, hstep] at h0
    exact h0
  exact hne (hfun c0 a0 (astep t a0) hR0 h).symm

end Repr

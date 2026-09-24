/-
# Kit.Relation — the relational engine's substrate

notes/v3/01-core.md §6 (THE relational engine) + decisions.md D16: the
proof-reuse mechanism — bundled interpretations + an explicit relation
family + per-primitive preservation + ONE generic theorem per
interpretation pair. This file is the substrate the AGREEMENT theorems
between interpretations stand on — NOT a parallel correspondence
library: the graded carrier stays `Kit.Correspondence` (§4: the grades
name a crossing's law), and the observer/grade nuance stays
`Kit.Observer` (04 §4, D18) — cited, not rebuilt.

What lands here:

- the relation family (`Rel`) + composition (`Rel.comp`, the
  transitivity-friendly existential shape) + the identity/diagonal
  (`Rel.refl` — reflexivity-as-determinism) + associativity (pointwise
  `Iff` — the honest shape) + transitivity AS composition's collapse
  (`Rel.trans_iff`) + determinism-for-free (`Rel.det_iff`);
- THE interpretation bundle (`Interpretation`: a term universe + its
  two evaluations + the relation) — the pair a per-primitive
  preservation argument lifts through;
- THE GENERIC THEOREM (`Expr.preserves`): over the minimal honest term
  universe (`Kit.Expr` — leaf/unary/binary) and the rows structure
  (`Preserves`: per-primitive row + the node laws), per-primitive
  R-preservation ⟹ whole-term R-preservation, by structural induction,
  ONCE. A lane instantiates by supplying the rows — the real universes'
  instances arrive with their lanes (spec↔impl, unoptimized↔optimized,
  abstract↔concrete, old↔new schema, full↔incremental,
  concrete↔instrumented); the composition rows lift THROUGH it with no
  second induction — `Expr.pipeline` (an R-preserving map pair into S,
  §6's "R-preserving f, g" row) and `Expr.chain` (two pairs sharing the
  middle universe: the end-to-end is ONE composite relation `Rel.comp`,
  its witness the shared middle evaluation — transitivity's shape).
- the Kripke note: the stateful lanes' evolving relations are a NAMED
  extension (`Kripke`) — the alias only; the machinery lands with its
  first consumer (§6: "never a hidden assumption").

Boundary (§6, kept): loops/recursion/effects need their own relational
rules — parametricity (and this induction) does not supply them; they
are NOT smuggled in here.

The five questions (notes/v3/01-core.md):
- root: Universe — the term universes are closed codes + total
  denotation (the ONE fold), and this file states the crossings
  between their presentations (§6 is the proof-reuse mechanism over
  §4's carrier).
- carrier grade: composes WITH `Kit.Correspondence` — the grades name
  the crossing's law; `Rel` + `Preserves` deliver the agreement
  theorems between the pair's evaluations.
- spine reading: none — the consumers are the lanes' interpretation
  pairs (the six named in §6); nothing is emitted.
- ladder rung: hand theorems of the small generic kind (01 §7) —
  `Expr.preserves` is the ONE generic theorem per interpretation pair.
- gate row: the axiom pins in `KitTests.Axioms` (Kit is outside the
  axiom gate's package set) + the KitTests pins — positive + the
  mandatory negative controls (the row premise is load-bearing).

Core-only: no mathlib, no Batteries (the cone rule).
-/

namespace Kit

/-! ## The relation family -/

/-- A relation family: `Rel A B` relates `A`s to `B`s — the explicit
    relation §6's agreement theorems are stated in (`abbrev`: the
    function shape reaches through to applications and instances). -/
abbrev Rel (A B : Type) := A → B → Prop

namespace Rel

/-- The identity/diagonal relation — reflexivity AS determinism (§6):
    the only `B` related to `a` is `a` itself. -/
def refl (A : Type) : Rel A A := fun a a' => a = a'

/-- Composition (§6's composition row: "relations compose (R∘S) — the
    multi-stage pipeline's end-to-end preservation is one composite
    relation + transitivity"). The existential shape IS the
    transitivity-friendly one: a composite is its witness chain. -/
def comp (R : Rel A B) (S : Rel B C) : Rel A C :=
  fun a c => ∃ b, R a b ∧ S b c

/-- Composition is associative — honestly: POINTWISE `Iff` (the two
    existential nestings re-associate; `Eq` of relations would buy the
    same content via funext + propext, nothing more). -/
theorem comp_assoc {A B C D : Type} (R : Rel A B) (S : Rel B C)
    (T : Rel C D) (a : A) (d : D) :
    (comp (comp R S) T a d ↔ comp R (comp S T) a d) :=
  ⟨fun h => by
      obtain ⟨c, ⟨b, h1, h2⟩, h3⟩ := h
      exact ⟨b, h1, c, h2, h3⟩,
   fun h => by
      obtain ⟨b, h1, c, h2, h3⟩ := h
      exact ⟨c, ⟨b, h1, h2⟩, h3⟩⟩

/-- The identity law, left: the diagonal is composition's unit. -/
theorem comp_reflLeft {A C : Type} (R : Rel A C) (a : A) (c : C) :
    (comp (refl A) R a c ↔ R a c) :=
  ⟨fun h => by
      obtain ⟨b, h1, h2⟩ := h
      rw [h1]
      exact h2,
   fun h => ⟨a, rfl, h⟩⟩

/-- The identity law, right. -/
theorem comp_reflRight {A B : Type} (R : Rel A B) (a : A) (b : B) :
    (comp R (refl B) a b ↔ R a b) :=
  ⟨fun h => by
      obtain ⟨x, h1, h2⟩ := h
      rw [← h2]
      exact h1,
   fun h => ⟨b, h, rfl⟩⟩

/-- THE transitivity-friendly shape (§6: "one composite relation +
    transitivity"): transitivity IS the composite's collapse — `R` is
    transitive exactly when `comp R R` implies `R`. The pipelines'
    transitivity arguments are stated in this shape, never re-invented. -/
theorem trans_iff {A : Type} (R : Rel A A) :
    (∀ x y z, R x y → R y z → R x z) ↔ ∀ x z, comp R R x z → R x z :=
  ⟨fun h x z hs => by
      obtain ⟨y, h1, h2⟩ := hs
      exact h x y z h1 h2,
   fun h x y z h1 h2 => h x z ⟨y, h1, h2⟩⟩

/-- Determinism for free (§6: "reflexivity is the determinism theorem
    for free"): a reflexive relation all of whose pairs are equal IS
    the diagonal — the single-interpretation case (an evaluation paired
    with itself) lands here with no proof of its own. -/
theorem det_iff {A : Type} (R : Rel A A) (hrefl : ∀ a, R a a)
    (hdet : ∀ a b, R a b → a = b) (a b : A) : (R a b ↔ a = b) :=
  ⟨hdet a b, fun h => by rw [h]; exact hrefl b⟩

end Rel

/-! ## The interpretation bundle -/

/-- THE interpretation bundle (§6): a term universe + its two
    evaluations + the relation the agreement is stated in — the pair a
    per-primitive preservation argument lifts through. Every lane's
    interpretation pair (spec↔generated impl, unoptimized↔optimized,
    abstract↔concrete, old↔new schema, full↔incremental,
    concrete↔instrumented) is an instance of this shape; the
    observer/grade nuance of a pair rides `Kit.Observer` +
    `Kit.Correspondence` (cited, not rebuilt). -/
structure Interpretation (Term V₁ V₂ : Type) where
  eval₁ : Term → V₁
  eval₂ : Term → V₂
  R : Rel V₁ V₂

namespace Interpretation

/-- The single-interpretation shape: ONE evaluation paired with
    itself, related by the diagonal — the determinism case
    (`Rel.det_iff` is its law). -/
def refl (eval : Term → V) : Interpretation Term V V :=
  ⟨eval, eval, Rel.refl V⟩

end Interpretation

/-! ## The generic theorem -/

/-- The minimal honest term universe (§6: "keep it generic — the real
    universes' instances arrive with their lanes"): a leaf (the
    primitive/carrier the lane owns) + a unary node + a binary node.
    A lane's syntax embeds by mapping its constructors onto these. -/
inductive Expr (P : Type) where
  | prim : P → Expr P
  | un : Expr P → Expr P
  | bin : Expr P → Expr P → Expr P

/-- The homomorphic evaluation: the ONE fold both evaluations of a
    pair instantiate (the Universe root's initial-algebra side). -/
def Expr.fold {P α : Type} (leaf : P → α) (un : α → α)
    (bin : α → α → α) : Expr P → α
  | .prim p => leaf p
  | .un e => un (e.fold leaf un bin)
  | .bin a b => bin (a.fold leaf un bin) (b.fold leaf un bin)

/-- THE per-primitive preservation contract — the engine's only input
    (§6's box, "proved once per primitive"): the per-primitive row plus
    the node laws. A lane instantiates by supplying these rows; nothing
    else is ever proved per pair. -/
structure Preserves (P V₁ V₂ : Type) (R : Rel V₁ V₂)
    (leaf₁ : P → V₁) (un₁ : V₁ → V₁) (bin₁ : V₁ → V₁ → V₁)
    (leaf₂ : P → V₂) (un₂ : V₂ → V₂) (bin₂ : V₂ → V₂ → V₂) : Prop where
  /-- The per-primitive row: each primitive's two evaluations relate. -/
  prim : ∀ p, R (leaf₁ p) (leaf₂ p)
  /-- The unary node respects the relation (proved once). -/
  un : ∀ a b, R a b → R (un₁ a) (un₂ b)
  /-- The binary node respects the relation (proved once). -/
  bin : ∀ a₁ a₂ b₁ b₂, R a₁ b₁ → R a₂ b₂ → R (bin₁ a₁ a₂) (bin₂ b₁ b₂)

/-- THE GENERIC THEOREM (§6's box): per-primitive R-preservation
    ⟹ whole-term R-preservation, by structural induction — ONCE, for
    every interpretation pair. A lane instantiates by supplying the
    rows; its agreement theorem is this one applied. The shape covers
    the six named pairs' PATTERN (spec↔impl agreement, optimization
    equivalence, migration, full↔incremental, instrumentation-hiding):
    `R` is the pair's relation; the observer/grade nuance rides
    `Kit.Observer` + the carrier. -/
theorem Expr.preserves {P V₁ V₂ : Type} {R : Rel V₁ V₂}
    {leaf₁ : P → V₁} {un₁ : V₁ → V₁} {bin₁ : V₁ → V₁ → V₁}
    {leaf₂ : P → V₂} {un₂ : V₂ → V₂} {bin₂ : V₂ → V₂ → V₂}
    (h : Preserves P V₁ V₂ R leaf₁ un₁ bin₁ leaf₂ un₂ bin₂)
    (e : Expr P) : R (e.fold leaf₁ un₁ bin₁) (e.fold leaf₂ un₂ bin₂) := by
  induction e with
  | prim p => exact h.prim p
  | un _ ih => exact h.un _ _ ih
  | bin _ _ iha ihb => exact h.bin _ _ _ _ iha ihb

/-- §6's composition row, map shape: a second stage `f₁/f₂` preserving
    `R` into `S` lifts the agreement through itself — no second
    induction (the homogeneous case `W₁ = V₁`, `W₂ = V₂`, `S = R` is
    the row's literal reading: R-preserving f ⟹ R-preserving f∘g via
    two applications). -/
theorem Expr.pipeline {P V₁ V₂ W₁ W₂ : Type} {R : Rel V₁ V₂}
    {S : Rel W₁ W₂}
    {leaf₁ : P → V₁} {un₁ : V₁ → V₁} {bin₁ : V₁ → V₁ → V₁}
    {leaf₂ : P → V₂} {un₂ : V₂ → V₂} {bin₂ : V₂ → V₂ → V₂}
    (h : Preserves P V₁ V₂ R leaf₁ un₁ bin₁ leaf₂ un₂ bin₂)
    {f₁ : V₁ → W₁} {f₂ : V₂ → W₂}
    (hstage : ∀ a b, R a b → S (f₁ a) (f₂ b))
    (e : Expr P) :
    S (f₁ (e.fold leaf₁ un₁ bin₁)) (f₂ (e.fold leaf₂ un₂ bin₂)) :=
  hstage _ _ (Expr.preserves h e)

/-- §6's composition row, chain shape: two interpretation pairs sharing
    the middle universe — the multi-stage pipeline's end-to-end
    preservation is ONE composite relation (`Rel.comp`), its witness
    the shared middle evaluation, and the two inductions are THE generic
    theorem applied twice (transitivity's content, no new proof). -/
theorem Expr.chain {P A B C : Type} {R : Rel A B} {S : Rel B C}
    {leafA : P → A} {unA : A → A} {binA : A → A → A}
    {leafB : P → B} {unB : B → B} {binB : B → B → B}
    {leafC : P → C} {unC : C → C} {binC : C → C → C}
    (h₁ : Preserves P A B R leafA unA binA leafB unB binB)
    (h₂ : Preserves P B C S leafB unB binB leafC unC binC)
    (e : Expr P) :
    Rel.comp R S (e.fold leafA unA binA) (e.fold leafC unC binC) :=
  ⟨e.fold leafB unB binB, Expr.preserves h₁ e, Expr.preserves h₂ e⟩

/-! ## The bundle connection -/

namespace Interpretation

/-- A row-supplied fold pair IS an interpretation: the bundle naming
    the agreement the generic theorem delivers. -/
def ofPreserves {P V₁ V₂ : Type} {R : Rel V₁ V₂}
    {leaf₁ : P → V₁} {un₁ : V₁ → V₁} {bin₁ : V₁ → V₁ → V₁}
    {leaf₂ : P → V₂} {un₂ : V₂ → V₂} {bin₂ : V₂ → V₂ → V₂}
    (_h : Preserves P V₁ V₂ R leaf₁ un₁ bin₁ leaf₂ un₂ bin₂) :
    Interpretation (Expr P) V₁ V₂ where
  eval₁ e := e.fold leaf₁ un₁ bin₁
  eval₂ e := e.fold leaf₂ un₂ bin₂
  R := R

/-- The bundle-level agreement: an interpretation built from rows
    AGREES — the generic theorem read at the bundle, no new proof. -/
theorem ofPreserves_agrees {P V₁ V₂ : Type} {R : Rel V₁ V₂}
    {leaf₁ : P → V₁} {un₁ : V₁ → V₁} {bin₁ : V₁ → V₁ → V₁}
    {leaf₂ : P → V₂} {un₂ : V₂ → V₂} {bin₂ : V₂ → V₂ → V₂}
    (h : Preserves P V₁ V₂ R leaf₁ un₁ bin₁ leaf₂ un₂ bin₂)
    (e : Expr P) :
    (ofPreserves h).R ((ofPreserves h).eval₁ e) ((ofPreserves h).eval₂ e) :=
  Expr.preserves h e

end Interpretation

/-! ## The Kripke note — the stateful lanes' named extension

§6: "the stateful lanes need Kripke-style evolving relations — the
relation grows with the state — a named extension, never a hidden
assumption." The alias NAMES the extension only: the machinery (the
evolution-aware generic theorem, the frame/modality rows) lands with
its first consumer, deliberately, per the leftover rule. Nothing below
presumes it.
-/

/-- Kripke-style evolving relations: the relation family indexed by
    the evolving state σ. Named extension only — no machinery. -/
abbrev Kripke (σ V₁ V₂ : Type) : Type := σ → Rel V₁ V₂

end Kit

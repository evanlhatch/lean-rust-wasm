/-
# Analysis.Basic — the abstract-interpretation framework

Owned by: the analysis agent (the mandate tree, `analysis/`).
Driving decisions: the reviews' verification-dimension addition
(abstract interpretation: "each abstract transfer function carries
soundness relative concrete semantics; untrusted analyzer searches;
checked result certifies") + notes/v3/01-core.md §4 (the ONE carrier —
this framework rides `Kit.Correspondence.Abstraction`'s grade: the
`γ` here IS the Abstraction's `conc`, bridged by
`AbstractDomain.toAbstraction`, cited not re-rolled) + notes/v3/01-core.md
§6 (the transfer functions' soundness fields ARE the per-primitive
preservation rows; the whole-program agreement is the relational
engine's ONE generic theorem — `Analysis.Checker`) + notes/v3/04 §3
(the certificate pattern: the analyzer is the untrusted producer, the
γ-membership certificate is what the soundness fields let the checker
admit) + notes/v3/15-patterns.md #1 and #5.

## The framework's exact shape

- The concretization `γ : Abs → Concrete → Prop` — the ONLY bridge
  between the two worlds. `γ a c` reads "concrete value `c` is OF
  abstract value `a`".
- A transfer function is a `step` PLUS its soundness field, bundled
  (`Transfer1`/`Transfer2`): an unsound step does not construct — the
  soundness proof is not documentation, it is a constructor argument.
- `AbstractDomain` bundles the concrete signature (one unary op, one
  binary op — the smallest signature that exercises both arities),
  their sound transfers, and the join with its cover law
  (`γ (a ⊔ b) ⊇ γ a ∪ γ b`, split into the two one-sided fields —
  the fixpoint iteration's soundness requirement, stated honestly as
  the upper-bound law, not the weaker both-hypotheses form).
- Named exclusion — MONOTONICITY is not a field: soundness is
  pointwise and monotonicity is a separate, stronger claim the
  framework does not need (the certificate reading only needs the
  γ-cover; termination of widening rides the per-domain finite-height
  discipline — `Analysis.Intervals`' width lemmas — not monotonicity).
- The concrete signature is deliberately minimal (unary + binary):
  domains with more operations extend by adding Transfer fields —
  the shape, not the arity count, is the framework (01 §7: instances
  of the pattern, never parallel tables).

The five questions (notes/v3/01-core.md):
- root: the crossing (01 §4's Abstraction grade is THIS file's
  consumer-facing carrier; no new root).
- carrier grade: Abstraction — γ + the per-transfer soundness fields;
  the transfer composition/agreement machinery is Kit.Relation's
  (cited at `Analysis.Checker`, never rebuilt).
- spine reading: none — the analysis lane's substrate; nothing emitted.
- ladder rung: the soundness fields are construction-time proof
  obligations (rung 3's discipline: an unsound transfer does not
  elaborate); the per-domain laws are small hand theorems (01 §7:
  the preferred foundation).
- gate row: none yet — Analysis is outside Gates.Packages' gated set;
  the tests' axiom pins carry the drift check (AnalysisTests.Axioms).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Kit.Correspondence

namespace Analysis

/-! ## The concretization order -/

/-- The abstract order induced by `γ`: `a ⊑ b` iff `b`'s concretization
    covers `a`'s. The framework's ONLY order — derived from γ, never
    declared separately (one bridge, one discipline). -/
def AbsLe {C A : Type} (γ : A → C → Prop) (a b : A) : Prop :=
  ∀ c, γ a c → γ b c

/-! ## The transfer functions — step + soundness, bundled -/

/-- A unary transfer: the abstract step of one concrete unary operation.
    The `sound` field is load-bearing: it is a constructor argument, so
    an unsound step does not construct (the soundness discipline). -/
structure Transfer1 {C A : Type} (γ : A → C → Prop) (f : C → C) where
  /-- The abstract step. -/
  step : A → A
  /-- Soundness relative `f`: the step's result concretizes over
      `f`'s result whenever the input concretizes. -/
  sound : ∀ a c, γ a c → γ (step a) (f c)

/-- A binary transfer: the abstract step of one concrete binary
    operation. Same discipline as `Transfer1`. -/
structure Transfer2 {C A : Type} (γ : A → C → Prop) (f : C → C → C) where
  /-- The abstract step. -/
  step : A → A → A
  /-- Soundness relative `f`: the steps' result concretizes over
      `f`'s result whenever both inputs concretize. -/
  sound : ∀ a₁ a₂ c₁ c₂, γ a₁ c₁ → γ a₂ c₂ → γ (step a₁ a₂) (f c₁ c₂)

/-! ## The abstract domain -/

/-- An abstract domain: the concretization γ + the concrete signature
    (the semantics being approximated) + the sound transfers + the join
    with its cover law. The abstract TYPE is `A` itself — the domain is
    the pair's discipline, not a wrapper. -/
structure AbstractDomain (C A : Type) where
  /-- The concretization — the one bridge (01 §4: the Abstraction
      grade's `conc`, bridged by `toAbstraction`). -/
  γ : A → C → Prop
  /-- The concrete unary operation being abstracted (the oracle). -/
  unC : C → C
  /-- The concrete binary operation being abstracted (the oracle). -/
  binC : C → C → C
  /-- The unary transfer — sound by construction (the field). -/
  unA : Transfer1 γ unC
  /-- The binary transfer — sound by construction (the field). -/
  binA : Transfer2 γ binC
  /-- The join (the widening point: the finite-height discipline that
      makes fixpoint iteration terminate is PER-DOMAIN — see
      `Analysis.Intervals`' width lemmas for the worked instance). -/
  join : A → A → A
  /-- The join covers the left operand: `γ (a ⊔ b) ⊇ γ a` — the
      upper-bound law fixpoint iteration needs (the honest form: the
      weaker both-hypotheses conjunction would NOT give an upper
      bound). -/
  join_cover_left : ∀ a b c, γ a c → γ (join a b) c
  /-- The join covers the right operand: `γ (a ⊔ b) ⊇ γ b`. -/
  join_cover_right : ∀ a b c, γ b c → γ (join a b) c

/-! ## The bridge to the kit's ONE carrier -/

/-- The bridge to `Kit.Abstraction` (01 §4): the domain's γ IS the
    Abstraction's `conc`; the abstraction function `α` with its covering
    proof supplies the `sound` field — cited, not re-rolled. The
    transfers' soundness is NOT restated here: it lives in the domain's
    proof fields and reappears as the per-primitive rows of the
    relational engine (`Analysis.Checker`'s instance of
    `Kit.Expr.preserves`). -/
def AbstractDomain.toAbstraction (d : AbstractDomain C A) (α : C → A)
    (hα : ∀ c, d.γ (α c) c) : Kit.Abstraction C A where
  abst := α
  conc := d.γ
  sound := hα

end Analysis

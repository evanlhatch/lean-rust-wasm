/-
# Analysis.Checker — the checker shape: concrete vs abstract, ONE theorem

Owned by: the analysis agent (the mandate tree, `analysis/`).
Driving decisions: notes/v3/01-core.md §6 (THE relational engine: the
abstract↔concrete pair is one of the six named interpretation pairs —
per-primitive preservation rows + ONE generic theorem, by structural
induction, ONCE) + notes/v3/04 §3 (the certificate pattern: the
untrusted analyzer searches; the checked result certifies — here the
abstract evaluation IS the certificate producer, and its soundness is
the engine's theorem, not a hope) + notes/v3/15-patterns.md #6 (the
dual-reading tie: two semantics of one expression, tied by ONE theorem
at the structure).

## The shape

- The term universe: `Kit.Expr Int` (leaf = the Int constant, un =
  negation, bin = addition — the honest minimal over `Iv`'s signature).
  The Kit.Expr generics are the term universe DIRECTLY: a lane with
  its own syntax embeds by mapping its constructors onto these (the
  fold is the ONE homomorphic map).
- `concreteEval`: the fold with the concrete ops (`id`, negation,
  addition) — the semantics.
- `abstractEval`: the fold with the interval domain's transfers
  (`point`, `negT`, `addT`) — the UNTRUSTED analyzer.
- `covers c iv` (the relation `R : Kit.Rel Int Iv`): the concrete
  result is OF the abstract result — the concretization, flipped into
  the engine's argument order.
- THE SOUNDNESS THEOREM: `abstract_sound` is `Kit.Expr.preserves`
  applied to the rows — the induction is the engine's, written once in
  Kit.Relation; this file writes ZERO induction. The per-primitive
  rows cite `Analysis.Intervals`' soundness theorems (which are the
  domain's transfer fields' content — cited, not re-rolled).
- The overflow face: `caged_result_certified` — a caged abstract
  result certifies the concrete value inside the cage; its
  contrapositive is the analysis's overflow FLAG (the escape is the
  loud answer, never a silent pass).

The five questions (notes/v3/01-core.md):
- root: Universe — the term universe is a closed code + the ONE fold;
  the theorem is the §6 box's instance.
- carrier grade: Abstraction (the abstract↔concrete pair), delivered
  through the relational engine's `Kit.Preserves` rows — the two
  surfaces are the SAME discipline (Kit.Relation's header note).
- spine reading: none — the checker the certificate pattern's small
  verified side.
- ladder rung: rung 6 done ONCE at the engine (Kit.Expr.preserves) —
  this file only cites it; the rows are rung-3-style fields over
  Intervals' hand theorems.
- gate row: none yet — AnalysisTests.Axioms pins the axiom cones.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Analysis.Intervals
import Kit.Relation

namespace Analysis

open Kit (Expr Preserves Interpretation)

/-! ## The two evaluations -/

/-- The concrete semantics: the ONE fold over the concrete ops. -/
def concreteEval (e : Expr Int) : Int :=
  e.fold (fun c => c) (fun c => -c) (fun a b => a + b)

/-- The abstract evaluation: the SAME fold over the interval domain's
    sound transfers — the untrusted analyzer (04 §3: the producer is
    free to be clever; here it is even total). -/
def abstractEval (e : Expr Int) : Iv :=
  e.fold point negT addT

/-! ## The relation + the per-primitive rows -/

/-- The relation the agreement is stated in: the concrete value is OF
    the abstract interval — the concretization in the engine's argument
    order (`Kit.Rel Int Iv`). -/
def covers : Kit.Rel Int Iv := fun c iv => iv.mem c

/-- The per-primitive preservation rows (01 §6's box): one row per
    primitive, each CITING the interval soundness theorem — the whole
    expression's agreement is the engine's generic theorem. This
    structure is the ONLY thing a new abstract domain supplies to get
    its checker soundness for free. -/
theorem intervalRows : Preserves Int Int Iv covers
    (fun c => c) (fun c => -c) (fun a b => a + b)
    point negT addT where
  prim p := point_sound p
  un := by
    intro a b h
    exact negT_sound b a h
  bin := by
    intro a₁ a₂ b₁ b₂ h1 h2
    exact addT_sound b₁ b₂ a₁ a₂ h1 h2

/-! ## THE soundness theorem — the engine's, cited -/

/-- THE soundness theorem (01 §6's ONE generic theorem, applied): the
    abstract evaluation's result concretizes over the concrete
    evaluation's result — proved once over the expression structure by
    `Kit.Expr.preserves`; this file writes no induction. The
    certificate reading: the analyzer's interval is a CHECKED
    certificate for the concrete value. -/
theorem abstract_sound (e : Expr Int) :
    covers (concreteEval e) (abstractEval e) :=
  Expr.preserves intervalRows e

/-- The certificate, in endpoint form. -/
theorem abstractEval_certifies (e : Expr Int) :
    (abstractEval e).lo ≤ concreteEval e
    ∧ concreteEval e ≤ (abstractEval e).hi :=
  abstract_sound e

/-- The overflow face: a caged abstract result CERTIFIES the concrete
    value inside the cage. Contrapositive: a concrete value outside the
    cage forces the abstract result out of the cage — the analysis's
    overflow flag (the loud answer, 01 §3's discipline). -/
theorem caged_result_certified {B : Int} (e : Expr Int)
    (h : Caged B (abstractEval e)) : CagedValue B (concreteEval e) := by
  obtain ⟨h1, h2⟩ := abstractEval_certifies e
  obtain ⟨h3, h4⟩ := h
  show -B ≤ concreteEval e ∧ concreteEval e ≤ B
  exact ⟨by omega, by omega⟩

/-! ## The interpretation bundle -/

/-- The pair as a `Kit.Interpretation` — the bundle naming the
    agreement the engine delivers (concrete = eval₁, abstract =
    eval₂, `covers` = R). -/
def intervalPair : Interpretation (Expr Int) Int Iv :=
  Interpretation.ofPreserves intervalRows

/-- The bundle-level agreement (no new proof — the engine's theorem
    read at the bundle). -/
theorem intervalPair_agrees (e : Expr Int) :
    intervalPair.R (intervalPair.eval₁ e) (intervalPair.eval₂ e) :=
  abstract_sound e

end Analysis

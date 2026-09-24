/-
# Cost.Expr — the cost interpretation pair + the agreement theorem

notes/v3/01-core.md §6 (the relational engine) applied to the
quantitative semantics: the cost interpretation is an INTERPRETATION
PAIR — the plain eval vs the cost-graded eval over the same term
universe, and the agreement theorem ("the cost is a lawful annotation:
`(graded.eval e).val = plain.eval e`") is the ENGINE's generic theorem
(`Kit.Expr.preserves`) instantiated, NOT a second induction.

Two engine instantiations, one shape each:

- **The agreement pair** — the relation is the value projection
  (`v = g.val`): per-primitive, the graded leaf/un/bin's VALUE is the
  plain leaf/un/bin's; `Expr.preserves` lifts it to whole terms, ONCE.
- **The honesty pair** — the relation is the cost projection
  (`c = g.cost`): per-primitive, the graded node's cost is THE
  composition of the primitives' costs (the direct cost fold's
  row); `Expr.preserves` lifts it — the graded eval's cost is the
  composition of the primitives' costs, no silent undercount.

The term universe is `Kit.Expr` (the engine's minimal honest one:
leaf/unary/binary); a real language embeds by mapping its constructors
onto these — the fixture language for the exercises lives in CostTests.

The five questions (notes/v3/01-core.md):
- **Root**: Universe — the term universes are closed codes + total
  denotation; this file states the cost crossing between the plain and
  the graded presentation (§6's concrete↔instrumented pair, the
  instrument's observer being perfObs — 04 §4).
- **Carrier grade**: the interpretation pair via `Kit.Relation` — the
  agreement is the engine's generic theorem applied, one per pair.
- **Spine reading**: none — the consumers are the lanes' cost
  interpretations.
- **Ladder rung**: rung 6 (hand theorems of the small generic kind) —
  the rows are the engine's only input; nothing is proved per pair.
- **Gate rows**: the axiom report over `agrees`/`cost_honest` +
  CostTests pins.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Cost.Basic
import Kit.Relation

open Kit

namespace Cost

/-! ## The grading bundle -/


/-- The grading bundle over a term universe: the plain operations
    (leaf/un/bin — the ONE fold the plain eval rides) + the
    per-primitive costs (the leaf's own cost, the unary node's, the
    binary node's). Generic in the cost type through the model — the
    Nat instance is `natCost`. -/
structure Grading (P V C : Type) [LE C] (m : CostModel C) where
  /-- The plain leaf evaluation. -/
  leaf : P → V
  /-- The primitive's own cost. -/
  primCost : P → C
  /-- The plain unary node. -/
  un : V → V
  /-- The unary node's own cost. -/
  unCost : C
  /-- The plain binary node. -/
  bin : V → V → V
  /-- The binary node's own cost. -/
  binCost : C

-- The grading's section variables (everything below is stated for a
-- fixed grading `g` over a fixed model `m`).
variable {P V C : Type} [LE C] {m : CostModel C} (g : Grading P V C m)

/-- The graded leaf: the plain value at the primitive's own cost. -/
def Grading.gradedPrim (p : P) : Graded C V :=
  ⟨g.leaf p, g.primCost p⟩

/-- The graded unary node: the plain node's value; the cost composes
    the node's own cost with the operand's. -/
def Grading.gradedUn (a : Graded C V) : Graded C V :=
  ⟨g.un a.val, m.compose g.unCost a.cost⟩

/-- The graded binary node: the plain node's value; the cost composes
    the node's own cost with BOTH operands' — in order, no undercount. -/
def Grading.gradedBin (a b : Graded C V) : Graded C V :=
  ⟨g.bin a.val b.val, m.compose g.binCost (m.compose a.cost b.cost)⟩

/-- The graded carriers' projections, as bridges: the graded node's
    value is the plain node's, its cost is the composed one (both
    definitional — the carrier is honest data, not an abstraction). -/
theorem Grading.gradedPrim_val (p : P) : (g.gradedPrim p).val = g.leaf p := rfl

theorem Grading.gradedUn_val (a : Graded C V) : (g.gradedUn a).val = g.un a.val := rfl

theorem Grading.gradedUn_cost (a : Graded C V) :
    (g.gradedUn a).cost = m.compose g.unCost a.cost := rfl

theorem Grading.gradedBin_val (a b : Graded C V) :
    (g.gradedBin a b).val = g.bin a.val b.val := rfl

theorem Grading.gradedBin_cost (a b : Graded C V) :
    (g.gradedBin a b).cost = m.compose g.binCost (m.compose a.cost b.cost) := rfl

/-- The PLAIN evaluation: the one fold over the plain operations
    (the Universe root's initial-algebra side). -/
def Grading.eval (e : Expr P) : V :=
  e.fold g.leaf g.un g.bin

/-- The COST-GRADED evaluation: the same term, the same structure, the
    value carried ALONGSIDE the composed cost. -/
def Grading.geval (e : Expr P) : Graded C V :=
  e.fold g.gradedPrim g.gradedUn g.gradedBin

/-- The DIRECT cost accounting: a fold over the term computing the
    composition of the primitives' costs — what the graded eval's cost
    must equal for the annotation to be honest. -/
def Grading.costOf (e : Expr P) : C :=
  e.fold g.primCost
    (fun c => m.compose g.unCost c)
    (fun c₁ c₂ => m.compose g.binCost (m.compose c₁ c₂))

/-! ## The engine instantiations -/

/-- The AGREEMENT rows (the engine's only input): the plain value
    relates to the graded carrier by the value projection — per
    primitive, the graded operations' VALUES are the plain ones. -/
theorem Grading.agreeRows :
    Preserves P V (Graded C V) (fun v g' => v = g'.val)
      g.leaf g.un g.bin g.gradedPrim g.gradedUn g.gradedBin where
  prim p := rfl
  un a b h := by
    rw [gradedUn_val, h]
  bin a₁ a₂ b₁ b₂ h₁ h₂ := by
    rw [gradedBin_val, h₁, h₂]

/-- The HONESTY rows (the engine's only input, second pair): the direct
    cost fold relates to the graded carrier by the cost projection —
    per primitive, the graded operation's cost IS the composed cost. -/
theorem Grading.costRows :
    Preserves P C (Graded C V) (fun c g' => c = g'.cost)
      g.primCost
      (fun c => m.compose g.unCost c)
      (fun c₁ c₂ => m.compose g.binCost (m.compose c₁ c₂))
      g.gradedPrim g.gradedUn g.gradedBin where
  prim p := rfl
  un a b h := by
    rw [gradedUn_cost, h]
  bin a₁ a₂ b₁ b₂ h₁ h₂ := by
    rw [gradedBin_cost, h₁, h₂]

/-! ## THE theorems -/

/-- THE AGREEMENT THEOREM (01 §6's engine, instantiated): the plain
    eval and the cost-graded eval AGREE on the value — the cost is a
    lawful annotation on the same program. Per-primitive value
    preservation ⟹ whole-term agreement, by the ONE structural
    induction the engine already owns. -/
theorem Grading.agrees (e : Expr P) :
    g.eval e = (g.geval e).val :=
  Expr.preserves g.agreeRows e

/-- THE HONESTY THEOREM: the graded eval's cost is THE composition of
    the primitives' costs — the direct accounting, term-for-term. No
    silent undercount: every primitive's cost appears in the composed
    annotation, exactly once, in the model's composition. -/
theorem Grading.cost_honest (e : Expr P) :
    (g.geval e).cost = g.costOf e :=
  (Expr.preserves g.costRows e).symm

end Cost

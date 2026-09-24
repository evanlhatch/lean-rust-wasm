/-
# CostTests — the composition laws' pins, the agreement exercise, the budget teeth

Positive pins + the MANDATORY negative controls (15-patterns #5); the
sweep discipline is TestingKit's LCG tape (15-patterns #14): same seed,
byte-identical replay. The runner is TestingKit's (`mainOfSuites`).

The fixture language (MY OWN — not another agent's): Nat constants,
unary successor, binary addition over `Kit.Expr` (the engine's minimal
honest term universe), graded by `arith` — every leaf costs 1, the
unary node 1, the binary node 2.

Suites:

1. `composition` — the laws pinned as data: nested programs' costs add
   (the bind composition), EITHER nesting (bind_assoc — the model's
   associativity cited), the writer's pure laws, the model's
   monotonicity discipline.
2. `agreement+honesty` — the two engine theorems EXERCISED on concrete
   nested programs: the graded eval agrees with the plain eval on the
   value, and its cost is the direct accounting, term-for-term.
3. `budget-teeth` — the monus-shaped budget: the covered remaining IS
   the monus apply; exhaustion reports the SHORTFALL as data and STILL
   delivers the value (exhaustion is never a verdict, 01 §3); two
   sequential spends are one spend of the composed cost.
4. `sweep` — the LCG-seeded property sweep (agreement + honesty +
   budget over generated programs) with the mandatory negative
   controls: the undercounting model (a zeroed node cost — caught),
   the exhaustion collapse (claims a zero-remaining verdict — caught),
   the agreement sabotage (claims the cost leaks into the value —
   caught).

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the laws — core-triple-only or the build fails.
-/

import Cost
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import CostTests.Axioms

open Kit TestingKit Cost

/-! ## The fixture grading + language -/

/-- The arithmetic grading: Nat values, Nat costs (addition), every
    leaf 1, the unary node 1, the binary node 2. -/
def arith : Grading Nat Nat Nat natCost where
  leaf := id
  primCost := fun _ => 1
  un := Nat.succ
  unCost := 1
  bin := fun a b => a + b
  binCost := 2

/-- `3 + succ 4` — plain value 8; cost 2 + (1 + (1 + 1)) = 5. -/
def e1 : Expr Nat := .bin (.prim 3) (.un (.prim 4))

/-- `e1 + (2 + 5)` — plain value 15; cost 2 + (5 + (2 + (1 + 1))) = 11. -/
def e2 : Expr Nat := .bin e1 (.bin (.prim 2) (.prim 5))

/-! ## Suite 1: the composition laws, pinned as data -/

-- three sequential steps, one composed cost
def stepA : Graded Nat Nat := ⟨10, 3⟩
def stepB : Graded Nat Nat := ⟨20, 4⟩
def stepC : Graded Nat Nat := ⟨30, 5⟩

-- nested programs' costs ADD (the composition law, at the carrier)
theorem nested_cost_adds : (stepA.bind natCost (fun _ => stepB)).cost = 7 := by decide

theorem nested_cost_adds3 :
    ((stepA.bind natCost (fun _ => stepB)).bind natCost (fun _ => stepC)).cost = 12 := by
  decide

-- EITHER nesting (bind_assoc — the model's compose_assoc, cited)
theorem nesting_irrelevant :
    ((stepA.bind natCost (fun _ => stepB)).bind natCost (fun _ => stepC)).cost
      = (stepA.bind natCost (fun _ => (stepB.bind natCost (fun _ => stepC)))).cost := by
  decide

-- the writer's pure laws, exercised
theorem pure_law_exercised :
    (Graded.pure natCost 7).bind natCost (fun _ => stepB) = stepB :=
  Graded.pure_bind natCost (fun _ => stepB) 7

theorem bind_pure_law_exercised :
    stepA.bind natCost (Graded.pure natCost) = stepA :=
  Graded.bind_pure natCost stepA

-- the model's monotonicity discipline: more subwork, no smaller total
theorem model_mono_exercised : NatCost.compose 3 2 ≤ NatCost.compose 3 5 :=
  natCost.mono 3 2 5 (by omega)

-- subterm monotonicity: a subprogram's cost is bounded by the whole's
theorem cost_subterm_bin (e a : Expr Nat) :
    arith.costOf a ≤ arith.costOf (.bin e a) := by
  show arith.costOf a ≤ arith.binCost + (arith.costOf e + arith.costOf a)
  omega

/-! ## Suite 2: the theorems exercised (agreement + honesty) -/

-- THE AGREEMENT: plain and graded agree on the value, on nested programs
theorem e1_agrees : arith.eval e1 = (arith.geval e1).val := arith.agrees e1
theorem e2_agrees : arith.eval e2 = (arith.geval e2).val := arith.agrees e2

-- ... and the agreed value is the RIGHT one (the fixture's own pin)
theorem e1_value : (arith.geval e1).val = 8 := by decide
theorem e2_value : (arith.geval e2).val = 15 := by decide

-- THE HONESTY: the graded cost IS the direct accounting
theorem e1_honest : (arith.geval e1).cost = arith.costOf e1 := arith.cost_honest e1
theorem e2_honest : (arith.geval e2).cost = arith.costOf e2 := arith.cost_honest e2

-- ... and the direct accounting is the COMPOSITION of the primitives'
-- costs — every primitive's cost appears, exactly once
-- (bin 2 + (leaf 1 + (un 1 + leaf 1)) = 5)
theorem e1_cost_composed : (arith.geval e1).cost = 2 + (1 + (1 + 1)) := by decide
-- outer bin 2 + (e1's 5 + (inner bin 2 + (leaf 1 + leaf 1))) = 11
theorem e2_cost_composed : (arith.geval e2).cost = 2 + (5 + (2 + (1 + 1))) := by
  decide

/-! ## Suite 3: the budget teeth (the monus connection) -/

-- a step costing 5 against a budget of 10
def afford : Graded Nat Nat := ⟨7, 5⟩

-- the covered branch: remaining = budget ⊖ cost = THE monus apply
theorem budget_covered : spend 10 afford = .covered 7 5 := by decide

theorem budget_is_monus : Kit.monus.apply 10 5 = some 5 := covered_remaining_monus 10 5

-- the exhausted branch: the SHORTFALL is the data (5 - 3 = 2)...
theorem budget_exhausted : spend 3 afford = .exhausted 7 2 := by decide

-- ... and the VALUE is still delivered — exhaustion is never a verdict
-- on the program (01 §3: budget exhaustion is UNKNOWN, never silently one)
theorem exhaustion_delivers_value : spend 0 afford = .exhausted 7 5 := by decide

-- THE budget composition law: two sequential spends are ONE spend of
-- the composed cost (the Change ladder's applyCompose, cited)
theorem budget_seq_law :
    (Kit.monus.apply 10 3).bind (Kit.monus.apply · 4) = Kit.monus.apply 10 7 :=
  spend_seq 10 3 4

/-! ## Suite 4: the LCG-seeded sweep + the mandatory negative controls -/

/-- The generated fixture: `a + (succ b + c)` over tape-drawn leaves. -/
def mkExpr (t : Tape) : Expr Nat :=
  let (a, t₁) := t.below 10
  let (b, t₂) := t₁.below 10
  let (c, _) := t₂.below 10
  .bin (.prim a) (.bin (.un (.prim b)) (.prim c))

def propAgrees (t : Tape) : CheckResult := do
  let e := mkExpr t
  assert (arith.eval e == (arith.geval e).val)
    "the graded eval broke agreement with the plain eval"
  assert ((arith.geval e).cost == arith.costOf e)
    "the graded eval's cost broke honesty against the direct accounting"

def propBudget (t : Tape) : CheckResult := do
  let (c, _) := t.below 10
  let gr : Graded Nat Nat := ⟨7, c⟩
  match spend 20 gr with
  | .covered v rem =>
      assert (v == 7 && rem == 20 - c) "the covered branch broke the monus bookkeeping"
  | .exhausted _ _ =>
      assert false "a budget of 20 exhausted by a cost below 10"

/-- The UNDERCOUNTING model: the binary node's own cost silently zeroed —
    the model the honesty theorem forbids. Its eval still AGREES (the
    value is untouched) but its cost misses the direct accounting. -/
def arithUnder : Grading Nat Nat Nat natCost where
  leaf := id
  primCost := fun _ => 1
  un := Nat.succ
  unCost := 1
  bin := fun a b => a + b
  binCost := 0

def negUndercount (t : Tape) : CheckResult := do
  let e := mkExpr t
  -- SABOTAGE: claims the undercounting model is honest. Caught: the
  -- node's own cost (2) is missing from every binary node.
  assert ((arithUnder.geval e).cost == arith.costOf e)
    "the undercount sabotage was not caught"

def negExhaustCollapse (t : Tape) : CheckResult := do
  let (c, _) := t.below 10
  let gr : Graded Nat Nat := ⟨7, c + 10⟩
  -- SABOTAGE: claims exhaustion collapses to a zero-remaining verdict —
  -- the forbIDDEN collapse (exhaustion is data, not a verdict). Caught:
  -- the true outcome is .exhausted with the shortfall.
  assert (spend 5 gr == .covered 7 0)
    "the exhaustion-collapse sabotage was not caught"

def negAgreementLeak (t : Tape) : CheckResult := do
  let e := mkExpr t
  -- SABOTAGE: claims the cost LEAKS into the value — grading adds
  -- annotation, never control. Caught: the cost is strictly positive
  -- on every generated fixture (three leaves + two nodes).
  assert (arith.eval e == (arith.geval e).val + (arith.geval e).cost)
    "the agreement-leak sabotage was not caught"

def specAgreement : Spec := Spec.ofList "cost-agreement"
  propAgrees
  [ ("undercount", negUndercount),
    ("agreement-leak", negAgreementLeak) ]
  12 20250721

def specBudget : Spec := Spec.ofList "cost-budget"
  propBudget
  [ ("exhaustion-collapse", negExhaustCollapse),
    ("covered-bookkeeping", fun _ =>
      -- SABOTAGE: claims the covered remaining is the UNSPENT budget
      -- (the delta dropped) — caught: the monus subtracts the cost.
      assert (spend 10 afford == .covered 7 10)
        "the covered-bookkeeping sabotage was not caught") ]
  12 20250722

def main : IO UInt32 := mainOfSuites [("Cost", [specAgreement, specBudget])]

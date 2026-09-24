/-
# Cost — the umbrella module

One import point for the library. Submodules:

- `Cost.Basic` — the cost model (`CostModel`: the zero + the
  composition + the monotonicity discipline; `natCost` the canonical
  instance) + the grading discipline (`Graded`: the writer shape, the
  value ALONGSIDE the cost, `bind` composing both carriers; the three
  writer laws).
- `Cost.Expr` — the cost interpretation pair (01 §6): plain eval vs
  cost-graded eval over `Kit.Expr`, the AGREEMENT theorem (`agrees`:
  the cost is a lawful annotation — the engine's generic theorem
  instantiated) + the HONESTY theorem (`cost_honest`: the graded
  eval's cost is THE composition of the primitives' costs, no silent
  undercount).
- `Cost.Budget` — the budget discipline: monus-shaped state (01 §1,
  `Kit.monus` cited), exhaustion as observable data (01 §3: UNKNOWN,
  never a verdict), the sequential-spend composition law.

Named exclusions (each lands with its first consumer — the leftover
rule): probabilistic cost distributions (the named fourth-root
trigger), amortized/potential-based accounting, cost models with
non-commutative observable orders (the TraceModel crossing), the
Kripke-style stateful cost relation.
-/

import Cost.Basic
import Cost.Expr
import Cost.Budget

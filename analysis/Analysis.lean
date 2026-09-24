/-
# Analysis — the umbrella module

One import point for the library. Submodules:

- `Analysis.Basic` — the framework: the concretization γ, the
  transfer functions (step + soundness field, bundled — an unsound
  transfer does not construct), the abstract domain's join + cover
  law, the bridge to the kit's `Abstraction` grade.
- `Analysis.Intervals` — the worked domain: bounded intervals over ℤ
  (the classic — overflow analysis, the bounded-Nat lane, the fuel
  budgets are the future consumers): the transfers + their soundness,
  the cage (the declared bound), the escape detection (the honest
  trichotomy), the finite-height discipline (the widening's
  termination note).
- `Analysis.Checker` — the checker shape: the tiny expression language
  (constants + negation + addition), the concrete eval, the abstract
  eval, and THE soundness theorem — `Kit.Expr.preserves` applied (the
  relational engine's ONE generic theorem, per 01-core §6; the
  abstract↔concrete pair is one of its six named interpretation
  pairs).
-/

import Analysis.Basic
import Analysis.Intervals
import Analysis.Checker

/-
# Datalog — the umbrella module

One import point for the library. Submodules:

- `Datalog.Basic` — the typed fragment: predicates, ground atoms, terms,
  literals, rules; the range-restrictedness checker + the loud refusal;
  the executable grounding engine (`matchArgs`/`matchAll`).
- `Datalog.Semantics` — the monotone consequence operator (`step`,
  `step_mono`), the finite fact universe + the closure theorem, the
  stabilization theorem (`exists_fix` — the fuel is the height bound,
  a THEORETIC bound), the evaluator (`eval`, `eval_fix`, `lfp_least`),
  and the evaluation-correctness bridge (`deriv_iff_eval` — sound +
  complete against the inductive LFP reading `Deriv`).

Named exclusions (02-data-plane §9): stratified negation (a negated
literal fails the safety check AND is inert under the operator),
aggregation, arithmetic generation, recursive bag weights, external
effects — each lands with its named law.
-/

import Datalog.Basic
import Datalog.Semantics

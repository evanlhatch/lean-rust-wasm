/-
# LeanSubstrait.Proto

The wire-faithful model of the Substrait plan — plain total Lean data
mirroring the `substrait.proto` message shapes, no proofs.  This is the
low-level currency of the package: the typed layer lowers into it and the
emitters read from it.

Modules:

- `LeanSubstrait.Proto.Type`: `Type` (with `Param`), nullability.
- `LeanSubstrait.Proto.Expression`: `Expression`, `Literal`, functions, casts.
- `LeanSubstrait.Proto.Rel`: `Rel` and every relation message.
- `LeanSubstrait.Proto.Extensions`: URNs and simple extension declarations.
- `LeanSubstrait.Proto.Plan`: `Plan`, `Version`, `PlanRel`.

The namespace is `LeanSubstrait.Proto`.
-/
import LeanSubstrait.Proto.Type
import LeanSubstrait.Proto.Expression
import LeanSubstrait.Proto.Rel
import LeanSubstrait.Proto.Extensions
import LeanSubstrait.Proto.Plan

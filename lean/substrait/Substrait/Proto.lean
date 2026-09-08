/-
# Substrait.Proto

The wire-faithful model of the Substrait plan — plain total Lean data
mirroring the `substrait.proto` message shapes, no proofs.  This is the
low-level currency of the package: the typed layer lowers into it and the
emitters read from it.

Modules:

- `Substrait.Proto.Type`: `Type` (with `Param`), nullability.
- `Substrait.Proto.Expression`: `Expression`, `Literal`, functions, casts.
- `Substrait.Proto.Rel`: `Rel` and every relation message.
- `Substrait.Proto.Extensions`: URNs and simple extension declarations.
- `Substrait.Proto.Plan`: `Plan`, `Version`, `PlanRel`.

The namespace is `Substrait.Proto`.
-/
import Substrait.Proto.Type
import Substrait.Proto.Expression
import Substrait.Proto.Rel
import Substrait.Proto.Extensions
import Substrait.Proto.Plan

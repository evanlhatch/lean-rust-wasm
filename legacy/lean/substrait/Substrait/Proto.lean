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

module

public import Substrait.Proto.Type
public import Substrait.Proto.Expression
public import Substrait.Proto.Rel
public import Substrait.Proto.Extensions
public import Substrait.Proto.Plan

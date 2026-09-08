/-
# Substrait.Typed

The schema-indexed typed layer: well-typed plans over a `Schema`.

- `Substrait.Typed.Schema`: schemas, the `SType` universe, `HasCol`
  (by-name column lookup through head/tail instance search).
- `Substrait.Typed.Expr`: `Expr s t n` — typed expressions, `FunctionSig`,
  the dotted operator family (`+.`, `-.`, `>.`, `==.`, ...).
- `Substrait.Typed.Rel`: `Rel inS outS` — the relation family.
- `Substrait.Typed.ToProto`: lowering to `Proto` with anchor assignment
  computed at emission.

The public entry points are `Rel.toProto : Rel inS outS → Proto.Rel` and
`Rel.toPlan : Rel inS outS → Proto.Plan`.

Rules of the road for users: schemas must be declared as **`abbrev`** (not
`def`) so `HasCol` instance search sees through them; column references carry
their type and nullability explicitly (`col "health" .i32 true`); nullability
is `false` = required, `true` = nullable.
-/
import Substrait.Typed.Schema
import Substrait.Typed.Expr
import Substrait.Typed.Rel
import Substrait.Typed.ToProto
import Substrait.Typed.Builder

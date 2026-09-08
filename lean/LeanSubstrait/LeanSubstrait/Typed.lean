/-
# LeanSubstrait.Typed

The schema-indexed typed layer: well-typed plans over a `Schema`.

- `LeanSubstrait.Typed.Schema`: schemas, the `SType` universe, `HasCol`
  (by-name column lookup through head/tail instance search).
- `LeanSubstrait.Typed.Expr`: `Expr s t n` — typed expressions, `FunctionSig`,
  the dotted operator family (`+.`, `-.`, `>.`, `==.`, ...).
- `LeanSubstrait.Typed.Rel`: `Rel inS outS` — the relation family.
- `LeanSubstrait.Typed.ToProto`: lowering to `Proto` with anchor assignment
  computed at emission.

The public entry points are `Rel.toProto : Rel inS outS → Proto.Rel` and
`Rel.toPlan : Rel inS outS → Proto.Plan`.

Rules of the road for users: schemas must be declared as **`abbrev`** (not
`def`) so `HasCol` instance search sees through them; column references carry
their type and nullability explicitly (`col "health" .i32 true`); nullability
is `false` = required, `true` = nullable.
-/
import LeanSubstrait.Typed.Schema
import LeanSubstrait.Typed.Expr
import LeanSubstrait.Typed.Rel
import LeanSubstrait.Typed.ToProto
import LeanSubstrait.Typed.Builder

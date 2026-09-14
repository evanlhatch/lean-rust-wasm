/-
# QLang

The query-language package: a lean-LINQ-shaped authoring surface over the
`Substrait` package's typed layer (the flatland dig's transfer plan —
`~/flatland/notes/lean/research-lean-linq.md`, flatland lineage).

Two surfaces, one substrate (the ergonomics answer):

- **The typed surface** — `Substrait.Typed.Rel`, the schema-indexed GADT.
  Column references resolve by instance search over literal schema
  `abbrev`s; a misspelled column fails at elaboration time. This package
  adds no Rel nodes — the substrate owns them (read/filter/project/aggregate/
  sort/fetch/join are all there).
- **The dynamic surface** — `QLang.DExpr` + `QLang.Query`. Column references
  are plain names resolved at `compile` time against the schema *value*
  (instance-as-data, not search — the flatland `DslExpr` pattern); each
  pipeline step accumulates validation errors instead of aborting, and
  `Query.checked` turns the log into an `Except String` at the end.

The package-boundary rule (notes/lean/research-lean-substrait-pkg.md): the
substrate owns Substrait semantics + serialization; this package owns the
authoring surface and communicates by the `Substrait.Typed.Rel`/`Plan` types
only.

Deliberate exclusions (the flatland dig's SKIP list): the write/DML surface
(flatland's `Rule.lean` — UPDATE/emit-mapping is an engine concern, not a
query-language concern) and the extension-rel surface. Join is available at
the typed surface only: a dynamic-surface join needs a two-pipeline combinator
whose condition schema is the *concatenation* of both sides — deferred until
a consumer needs it.
-/
import QLang.Error
import QLang.Registry
import QLang.DExpr
import QLang.Query

/-
# Query — the relational fragment's umbrella (02-data-plane §2/§3/§4)

Owned by: the Query agent (the mandate tree, `query/`).

The five questions (notes/v3/01-core.md):
- **Root**: the data plane's query fragment — the relational center's
  executable face: the SAME expression as executable query + logical
  proposition (the spec reading) + (later lanes) incremental input +
  explanation source.
- **Carrier grade**: the typed fragment `Query.Q` — the result row type
  is COMPUTED from the query structure (projection's `Cols`, join's
  `fs ++ gs`), and the key-backed cardinality is the Keys lane's
  proven determinacy, never a hope (02 §3).
- **Spine reading**: none — the fragment the data-plane lanes consume.
- **Ladder rung**: hand theorems of the small kind — the bridge
  (`evalQ_true_iff`, pattern #1) + the weight-polymorphism instance
  (`evalQ_wmap`, THE ONE THEOREM of 02 §4).
- **Gate rows**: the axiom report + QueryTests (positive pins + the
  mandatory negative controls).

Parts: `Query.Basic` (the row carrier's orderable discipline: the byte
image over the ONE codec, the lex order, the `CanonKey`/`DecidableEq`
instances, the row append/field readers), `Query.Expr` (the typed
fragment + the Prop-level spec `QSat` + the key-join surface),
`Query.Eval` (the weighted evaluation + the bridge + the
weight-polymorphism).

Honest boundary (02 §2, named): negation, aggregation, universal
conditions, and ordering semantics are NOT in this fragment — each
needs explicit additional semantics with named laws, and none is
smuggled in here.

Core-only (imports SchemaCore + ZSet — the cone rule).
-/

import Query.Basic
import Query.Expr
import Query.Eval

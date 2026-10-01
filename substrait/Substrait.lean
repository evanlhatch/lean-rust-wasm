/-
# Substrait — the substrait port's seed umbrella (14-build-map's substrait row)

Owned by: the substrait port agent (the mandate tree, `substrait/`).

The wire story (the legacy's, kept): `Typed` → `Proto` → text, with
`Typed` → `Eval` the SECOND reading (the execution). The port carries:

- `Substrait.Proto` — the wire-faithful message shapes' honest core
  (read/filter/project/join/aggregate/sort/fetch/set plus the
  fuller-plan rows cross/write + the literal/field/scalarFunction
  expression core; every narrowing named in the module header).
- `Substrait.Typed` — the schema-indexed typed layer RETARGETED onto
  SchemaCore's closed `Ty` (the legacy's parallel `SType` universe dies
  per the doctrine: literal payloads ARE `SchemaCore.Value t`; the
  `HasCol` by-name lookup keeps its `resolves` proof field — the WF
  discipline's first rung) with the typed-correctness bridge theorems
  (`toProto_ords`, `toProto_width` — the width bridge covers all eight
  rel arms), plus the slice-2 shapes: `AnyExpr` (the type-erased
  package), `Measure`, `SortKey`, and the aggregate/sort/fetch/set
  rel arms (every narrowing named).
- `Substrait.Text` — the canonical text: the token tables (the legacy
  Grammar tables' port, ONE table read by both directions) + the type
  fragment's emit/parse with the fuel-driven round-trip theorem + the
  rel grammar's NAME-TOKEN tables (sort directions, set ops, join
  types — `findName_self` is the ONE generic self-lookup lemma) + the
  canonical rel LINES (`relText` — the substrait-explain shapes, total
  over the narrow union; the parse half is the decode ladder, Phase 4).
- `Substrait.TypedDecode` — the TYPED decode (the read direction's
  face, Phase 4 landed): `decTypedRel?` / `decTypedPlan?` turn the
  wire's rel trees into `Substrait.Typed.Rel` with the
  well-typedness DISCHARGED BY CONSTRUCTION (the field rung constructs
  the `HasCol` from the ordinal's lookup hit; the GADT's refinements
  are the refusals — SS0004/SS0005; project refuses SS0007 — the wire
  carries no output names), with the CONDITIONAL RETRACTION laws
  (`decTypedRel?_ok`, `decTypedPlan?_ok` — the domain condition
  `Rel.decodable` names the two honest gaps: no project node, the
  measures' arity tie). The full circle composes this with the wire
  law (`decPlan?_encPlan`) — pinned in SubstraitTests.
- `Substrait.Eval` — the typed rels' in-memory evaluation (the second
  reading): the Row GADT over the schema, the SQL-null cells riding
  `Option (SchemaCore.Value t)`, the built-in i64/bool kernels, and
  the QUERY-LANE CONNECTION (the honest state): the filter bridge
  BOTH WAYS (`filterRowsM_ok_sound`/`_complete` — the `QSat.select`
  reading) and the join's conjunctive soundness
  (`evalJoinPairs_ok_sound` — the `QSat.join` reading); the type-level
  `Rel → Query.Q` conversion is the NAMED BOUNDARY (the row carriers
  differ; the conversion lands when a consumer forces it — the Eval
  module header).

THE REL CENSUS (the typed layer vs the vendored `algebra.proto`'s
`Rel` oneof — the full universe of 13): read/filter/project/join/
aggregate/sort/fetch/set + cross + write LANDED end to end (typed
ctor, width law, wire spelling, evaluation, typed decode); `keep` /
`join'` are typed-only (no wire spelling — the named refusals); the
extension rels (`extension_leaf/single/multi`) are the honest
boundary: their `detail` is `google.protobuf.Any` — an opaque
operator has no typed carrier. Exchange/window/expand rels are
ABSENT from the vendored proto (later substrait additions) — out of
scope by the byte-tie.

Named exclusions (each lands with its first consumer — the leftover
rule): the anchor/extension ladder (legacy `Typed/ToProto.lean`'s
ExtCtx + the `=== Extensions` section), ifThen/cast expressions, the
full plan-line grammar + the rel lines' parse half, and the decode
ladder's parser core (Phase 4: re-homes onto the grammar layer — its
LEMMAS port as content).

Core-only (imports SchemaCore + TextKit — the cone rule).
-/

import Substrait.Proto
import Substrait.Typed
import Substrait.Text
import Substrait.Eval
import Substrait.Wire
import Substrait.TypedDecode

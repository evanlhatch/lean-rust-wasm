/-
# Faults.Spec.Demo — the order-fault registry's snapshot (seed spec)

The demo failure modes are DECLARED in `Demo.lean` — the schema
authoring surface — since W10.1's one-fault unification: the registry
IS the wire variant's SSOT, and the fold (`derive_fault_variant
OrderError`) must run at the schema module's elaboration, before
`watchOrders`' `@[schema_fn]` reifies the variant reference. THIS
module only SNAPSHOTS the replayed extension: `derive_fault_registry`
reads the `@[fault]` registrations (append-only, codes from position —
E100, E101, …) into the coded registry at elaboration. Codes mean the
same thing in Lean elaboration errors and fast-observe traces.
Append-only: a mid-list insert would reallocate every later code (the
CI byte-tie pins this).
-/

import Faults.Registry
import Demo
import SchemaLang.Meta.Derive

namespace Faults.Spec

open SchemaLang

-- The guest registry: the `@[fault]` registrations (Demo.lean — the
-- fold's SSOT home), replayed through the extension and snapshotted
-- at elaboration. Name uniqueness + code collision-freedom are the
-- framework's `by decide` proof fields — a dup fails to ELABORATE.
-- (Line comments, not a doc comment: `/--`-before-custom-command trips
-- the declaration parser.)
derive_fault_registry apiFaults

-- DERIVED at elaboration from the schema registry
-- (`SchemaLang.Meta.derive_schema_type_names`): the demo universe's
-- type-position names (records + variants — `OrderError` included, via
-- the fold), snapshotted from the env extension at THIS module's
-- elaboration. Not a hand mirror: editing Demo.lean's universe
-- re-derives this list automatically; the Tests' tie-check (registry
-- reload) stays as the independent regression control, and its
-- stale-list negative control still fails.
derive_schema_type_names knownTypes

end Faults.Spec

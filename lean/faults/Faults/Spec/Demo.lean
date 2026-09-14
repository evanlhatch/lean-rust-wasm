/-
# Faults.Spec.Demo — the order-fault registry (seed spec)

The demo failure modes, aligned with the schema demo's OrderError
universe. Codes are allocated here at emission — E100, E101, … — and
mean the same thing in Lean elaboration errors and fast-observe traces.
-/

import Faults.Registry
import Demo
import SchemaLang.Meta.Derive

namespace Faults.Spec

open SchemaLang

def apiFaults : List FailureModeItem :=
  [ { name := "notFound", display := "entity not found: {id}"
    , category := .content, advice := "check the id exists"
    , payload := [("id", .u64)] }
  , { name := "invalidItem", display := "invalid cart item: {id}"
    , category := .content, advice := "check cart state"
    , payload := [("id", .u64)] }
  , { name := "upstreamTimeout", display := "upstream timed out after {ms}ms"
    , category := .transient, advice := "retry with exponential backoff"
    , payload := [("ms", .u64)] }
  , { name := "engineInvariant", display := "engine invariant violated"
    , category := .invariant, advice := "file a bug with the report id"
    , payload := [] } ]

-- DERIVED at elaboration from the schema registry
-- (`SchemaLang.Meta.derive_schema_type_names`): the demo universe's
-- type-position names (records + variants), snapshotted from the env
-- extension at THIS module's elaboration. Not a hand mirror: editing
-- Demo.lean's universe re-derives this list automatically; the Tests'
-- tie-check (registry reload) stays as the independent regression
-- control, and its stale-list negative control still fails.
derive_schema_type_names knownTypes

end Faults.Spec

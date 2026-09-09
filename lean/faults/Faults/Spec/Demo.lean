/-
# Faults.Spec.Demo — the order-fault registry (seed spec)

The demo failure modes, aligned with the schema demo's OrderError
universe. Codes are allocated here at emission — E100, E101, … — and
mean the same thing in Lean elaboration errors and fast-observe traces.
-/

import Faults.Registry

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

/-- The known schema type names — the schema-lang demo universe's
    `Item.typeNames` (records + variants, registry-name form: the same
    names `Ty.check`/`universeCheck` resolve `.ty` refs against).
    Hand-mirrored here because the registry lives in an env extension;
    the Tests tie-check loads the demo registry and asserts this list
    IS `Item.typeNames` of it (drift = red suite). -/
def knownTypes : List String := ["User", "OrderItem", "Order", "Role", "OrderError"]

end Faults.Spec

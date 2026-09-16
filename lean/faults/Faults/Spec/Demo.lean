/-
# Faults.Spec.Demo — the order-fault registry (seed spec)

The demo failure modes, aligned with the schema demo's OrderError
universe. Per-item `@[fault]` registrations (W7.4 — the hand list
literal is gone); `derive_fault_registry` snapshots them into the coded
registry at elaboration. Codes are allocated from position — E100, E101,
… — and mean the same thing in Lean elaboration errors and fast-observe
traces. Append-only: a mid-list insert would reallocate every later
code (the CI byte-tie pins this).
-/

import Faults.Registry
import Demo
import SchemaLang.Meta.Derive

namespace Faults.Spec

open SchemaLang

@[fault] def notFound : FailureModeItem :=
  { name := "notFound", display := "entity not found: {id}"
  , category := .content, advice := "check the id exists"
  , payload := [("id", .u64)] }

@[fault] def invalidItem : FailureModeItem :=
  { name := "invalidItem", display := "invalid cart item: {id}"
  , category := .content, advice := "check cart state"
  , payload := [("id", .u64)] }

@[fault] def upstreamTimeout : FailureModeItem :=
  { name := "upstreamTimeout", display := "upstream timed out after {ms}ms"
  , category := .transient, advice := "retry with exponential backoff"
  , payload := [("ms", .u64)] }

@[fault] def engineInvariant : FailureModeItem :=
  { name := "engineInvariant", display := "engine invariant violated"
  , category := .invariant, advice := "file a bug with the report id"
  , payload := [] }

-- The guest registry: the `@[fault]` registrations above, snapshotted
-- at elaboration. Name uniqueness + code collision-freedom are the
-- framework's `by decide` proof fields — a dup fails to ELABORATE.
-- (Line comments, not a doc comment: `/--`-before-custom-command trips
-- the declaration parser.)
derive_fault_registry apiFaults

-- DERIVED at elaboration from the schema registry
-- (`SchemaLang.Meta.derive_schema_type_names`): the demo universe's
-- type-position names (records + variants), snapshotted from the env
-- extension at THIS module's elaboration. Not a hand mirror: editing
-- Demo.lean's universe re-derives this list automatically; the Tests'
-- tie-check (registry reload) stays as the independent regression
-- control, and its stale-list negative control still fails.
derive_schema_type_names knownTypes

end Faults.Spec

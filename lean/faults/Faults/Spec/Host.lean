/-
# Faults.Spec.Host — the HOST fault registry (Stage C)

The steel-host's capability/engine faults flow from the same registry
discipline as the guest's: names, displays, categories, advice, and
payloads live HERE; codes are allocated at emission (E110, E111, … via
`allocateHost`) and mean the same thing across the boundary. The
generated module is `src/host_faults_generated.rs`; steel-host includes
it — the hand-written `valves` enum was deleted.

Namespace note: guest faults start at E100 (apiFaults), host faults at
E110 (allocateHost) — one E-code space, disjoint by construction.
-/

import Faults.Registry

namespace Faults.Spec

open SchemaLang

/-- Host-side faults: engine plumbing + capability denial. These never
cross INTO the guest — they are what the host reports when the guest
(or the engine) misbehaves. -/
def hostFaults : List FailureModeItem :=
  [ { name := "notInstantiated", display := "component not instantiated"
    , category := .invariant, advice := "call instantiate() before call()"
    , payload := [] }
  , { name := "missingExport", display := "missing export: {name}"
    , category := .content, advice := "check the component world exports (wasm-tools component wit)"
    , payload := [("name", .string)] }
  , { name := "unsupportedResult", display := "unsupported result type: {ty}"
    , category := .invariant, advice := "return a scalar or handle it via typed bindings"
    , payload := [("ty", .string)] }
  , { name := "engine", display := "engine: {message}"
    , category := .transient, advice := "inspect the chained wasmtime error text"
    , payload := [("message", .string)] } ]

end Faults.Spec

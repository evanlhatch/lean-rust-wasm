/-
# Faults.Spec.Host — the HOST fault registry (Stage C)

The steel-host's capability/engine faults flow from the same registry
discipline as the guest's: per-item `@[host_fault]` registrations
(W7.4 — the hand list literal is gone), snapshotted by
`derive_fault_registry … host`. The host code start is DERIVED from the
guest registry's size (`100 + guest count`, read from the replayed guest
extension — hence the `Faults.Spec.Demo` import) — one E-code space,
disjoint at ANY guest-registry size; a hardcoded start (the old E110
fiat) silently collided the moment guest faults grew past it. The
disjointness obligation is an executable test (`Nodup` over both
allocations), not a comment.

The generated module is `src/host_faults_generated.rs`; steel-host
includes it — the hand-written `valves` enum was deleted.
-/

import Faults.Registry
import Faults.Spec.Demo

namespace Faults.Spec

open SchemaLang

/-- Host-side faults: engine plumbing + capability denial. These never
cross INTO the guest — they are what the host reports when the guest
(or the engine) misbehaves. -/
@[host_fault] def notInstantiated : FailureModeItem :=
  { name := "notInstantiated", display := "component not instantiated"
  , category := .invariant, advice := "call instantiate() before call()"
  , payload := [] }

@[host_fault] def missingExport : FailureModeItem :=
  { name := "missingExport", display := "missing export: {name}"
  , category := .content
  , advice := "check the component world exports (wasm-tools component wit)"
  , payload := [("name", .string)] }

@[host_fault] def unsupportedResult : FailureModeItem :=
  { name := "unsupportedResult", display := "unsupported result type: {ty}"
  , category := .invariant, advice := "return a scalar or handle it via typed bindings"
  , payload := [("ty", .string)] }

@[host_fault] def engine : FailureModeItem :=
  { name := "engine", display := "engine: {message}"
  , category := .transient, advice := "inspect the chained wasmtime error text"
  , payload := [("message", .string)] }

-- The host registry: the `@[host_fault]` registrations above, codes
-- starting after the guest space (derived, not hand-set).
derive_fault_registry hostFaults host

end Faults.Spec

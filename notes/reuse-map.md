# The reuse map — what we've built and what it's for

The template's value = this layer. A new project (schema + functions +
runtime) instantiates EVERYTHING below by writing only the last row of
each table. The audit instruction: anything here without a consumer or
a reuse story is dead weight — delete it.

## TestKit — the test/gate harness (core + LSpec)

| Module | What | Reuse story |
|---|---|---|
| Harness | `CheckResult`/`assert` + the DetSpec substrate | the project-agnostic harness; the DetSpec/DiffSpec = the corruption-negative gate discipline |
| PropSpec | plausible-based property sweeps + the MANDATORY negative control | every property suite; the vacuity tripwire |
| DetSpec | deterministic seeded generators, pinned seeds (CI replays) | conformance/gen suites |
| DiffSpec | engineered corruptions, each must FAIL with context; the identity-corruption control | every differential gate |
| GateKit | the byte-tie loop (`--check`/`--update`), the argv contract, `AuditRule`/`auditFindings` (the emitted-text self-audit) | every byte-tied artifact; the 6.5.3 emitter audits |

## CodegenCore — the emitter framework (core-only)

| Module | What | Reuse story |
|---|---|---|
| Emit.Core | CommentStyle/header (the GenMeta: the clock+git+content-hash), the emitter-plugin model (buf/protoc), the driver contract | every new artifact type |
| Emit.Rust | the Rust item formatter (the Format-based), the mangler (the keyword-safe names) | any Rust emission |
| Emit.Certified | proof-carrying emission: the law over the CONCRETE spec data fails elaboration | "reproducible-AND-correct" artifacts |
| GuestGate | `@[guest]`/`@[guest_std]` — the elab-time runtime ban (Nat/IO/Task/Thunk) | any compiled-to-wasm surface |
| Registry | `mkRegistryExt`, `loadRegisteredItems`, the code allocation, the importModules preamble | every name↔item registry |

## schema-lang — the schema layer (the template's core; substrait-free)

| Module | What | Reuse story |
|---|---|---|
| Ty | the CLOSED boundary type universe + `EqAns` (the proof-carrying equality) | the closed-universe pattern: new types = extend every emitter (compiler-enforced) |
| Item | records/variants/funcs/resources + FuncSem (nullSem/determinism/delivery) + `body` | any interface definition |
| Meta.Reflect | `@[schema]`/`@[schema_fn]`/`@[schema_resource]` → the registry; the funcSem arg axes | the SSOT reflection |
| Diff/Migration | compat diff + the remedy half (the breaking gate's verdicts) | any evolution story |
| Snapshot | the wire codec for the universe (the baselines) | the breaking gate; the spec versioning |
| Emit.Wit/Registry | tyWit/typeDecl/funcDecl/worldOf; the emitter list + the jobs manifest + the paths/jobs audits | the WIT surface |
| Observe | spanName/spanFields — the observability as spec data | the fast-observe seam |
| Codec | the encode/decode combinators + the round-trip lemmas | any wire format |
| Session | the typed sessions (the stream/once boundary choreography) | the protocol conversations |
| Field | the HasCol GADT (the misspelled field = the elaboration error) | the schema-indexed expressions (the validators' phase 2) |
| DidYouMean | the edit-distance valid-space error enumeration | EVERY error path |
| Pipeline | the stage machine (proved acyclic; the driver runs THROUGH it) | any multi-phase driver |
| Vortex/* | the dtype lowering + the spec wiring | the columnar story |
| Bridge (OPT-IN) | Ty → Substrait SType | the query-language integration — NOT core |

## dbsp / Machines — the delta + protocol theory

| Module | What | Reuse story |
|---|---|---|
| ZSet/Incremental | the delta application = the group sum | the change-data-capture semantics |
| Replicas | two_replica_converge, batch_order_irrelevant (the wire's reordering license!), retract_is_inverse | any replica story |
| ChangeSpec | the certified patch/valid contracts (the generated trait's source) | the CRUD/delta impls |
| Circuit/Subsystems/Recursive/NestedCycle | the incremental-computation semantics | the staging/cycle stories |
| Machines.Core/Sync/LinearMachine/Compose | the guarded machines, the trace predicates, the linear composition | the stateful components |
| Session | the choreography + duality proved | the protocol spec layer |

## faults / std / wasm-backend — the surface layers

| Module | What | Reuse story |
|---|---|---|
| faults.Registry/Emit | the E-code registry, one writer, host+guest resolved from ONE registry | every error taxonomy |
| std (GuestlangStd) | the guest-impl surface + StrOps (the guest-legal string ops) | the guestlang runtime library |
| wasm-backend.Wat/Layout | (IN FLIGHT — the WAT AST + the proved canonical-ABI layout) | the compiler line's structure |
| wasm-backend adapters | the canonical-ABI record/string/stream lowerings | the boundary ABI |

## The instantiation checklist (what a new project writes)

1. A spec module: `@[schema]` records + `@[schema_fn]` functions (+ the
   variants/resources) — the SSOT.
2. The impl module: the bodies (+ `@[guest]`/`@[guest_std]` — the
   elab-time runtime ban).
3. `schema-gen` → the artifacts (the WIT/Rust/observe/faults/jobs, all
   byte-tied, all with the GenMeta header).
4. The guest build via the backend → the component; the duel rows =
   Lean's evals; TestKit's gates; `forge` byte-tie + push.
5. The host: the generated bindings + the span-manifest-governed call
   path.
Everything else — the harnesses, the gates, the emitters, the proofs —
comes from the layers above. The template's promise: the new project's
code = the spec + the impls; the machinery = inherited.

Step 1–2 are MACHINERY too now: `just new-project <name>` instantiates
`template/` as `lean/<name>` — the spec/impl skeletons with the renames
applied, the lean_pkgs + packagePrefixes registration done, and the
manual follow-ups (the world's fold, the lint row) printed.

# 08 — The capability catalog

The concrete specs. Each entry: the shape, the roots it rides (01), the
kit home, the acceptance test, the guard that keeps it honest. This is
the inventory — the detail lives in the named design docs where they
exist (notes/design-*.md); this file's version is the contract.

**Status discipline (the leftover rule applied to this file):** every
entry is exactly one of — LANDED (in the tree, gated), PARTIAL (the
landed scope is named in the entry; the named remainder is SPEC and
lands under the leftover rule like anything else), SPEC (designed,
accepted, scheduled — the full spec above is earned at build time),
WATCH (one line + its trigger). A SPEC entry that lands moves to
LANDED in the same commit; a PARTIAL entry's named remainder is the
only honest way anything is "half-built". The discipline is MECHANICAL
(B5): the status table below is the gate's data — `gates docs-check`
RESOLVES every LANDED/PARTIAL row's decl citations against the gated
tree's environments (a landed scope names a real declaration) and
REFUSES a SPEC/PARTIAL `pending` citation that resolves (the section
landed; the promotion is owed). A LANDED/PARTIAL row without a
citation is a finding. The table:

| § | status | landed (must resolve) | pending (must NOT resolve) | the scope note |
|---|---|---|---|---|
| 1 | LANDED | `WireCodec` `deriveRender` | | the records + the deriving protocol (the reflection path is `Describe`) |
| 2 | LANDED | `KeyDecl` | | keys + foreign keys — determinacy theorems driving API shape |
| 3 | LANDED | `UpdateItem` | | the v2 updates: multi-set/insert/delete over declared keys |
| 4 | LANDED | `CheckItem` | | the table invariants, discharged at the computed tier |
| 5 | LANDED | `EntityMachineDecl` | | the entity-machine preset (`schema_entity_machine`) |
| 6 | LANDED | `Contract` | | the pre/postconditions (the contracts lane's obligation mounts) |
| 7 | LANDED | `replayEvents` | | the event sourcing (the generated replay/inversion/codec laws) |
| 8 | PARTIAL | `Effect` | | the closed lattice + the footprint laws landed; "effect rows derive from registry items" is the lane's named exclusion |
| 9 | LANDED | `Session` | | the dual-checked sessions (`Machines.Session`) |
| 10 | PARTIAL | `Verdict` | `until` `eventually` `alwaysEventually` | the bounded exploration landed (`Machines.Explore`); the liveness ops exist nowhere in the tree — SPEC |
| 11 | LANDED | `ShrinkerV` | | the shrinking (`TestingKit`'s validity-preserving shrinkers) |
| 12 | SPEC | | | the relational spec layer (02 §1) |
| 13 | LANDED | `IsBag` | | the weighted relations — the ℤ instance; the provenance-polynomial weight kind stays SPEC (the lane's named exclusion) |
| 14 | LANDED | `evalQ` | | the query fragment (the constraint-driven result typing) |
| 15 | LANDED | `checkDeltaInc` | | the incremental violation relations (03 §8's ΔV face — `SchemaCore.IncViolate` + `Violate`'s queries; the commit gate is the empty-result verdict, the agreement proved, the fallback named) |
| 16 | SPEC | | | the materialized queries (02 §10) |
| 17 | LANDED | `ViewDef` | | the writable views (`SchemaCore.View`) |
| 18 | LANDED | `Confluent` | | the coordination classifier (`SchemaCore.Confluence`) |
| 19 | LANDED | `upcastDelta` `CompatChange` | | the migrations (`SchemaCore.Migrate` + `SchemaCore.Diff`) |
| 20 | LANDED | `whatIfJournal` | | the what-if inspector (`Inspector.WhatIf`) |
| 21 | SPEC | | | the WIT error channel |
| 22 | SPEC | | | the causal error tree |
| 23 | SPEC | | | the wires |
| 24 | SPEC | | | the connector library |
| 25 | SPEC | | | the capacity (bounded Petri nets) |
| 26 | SPEC | | | the runtime monitors |
| 27 | SPEC | | | the semantic diffs with witnesses |
| 28 | SPEC | | | the checked operational plans |
| 29 | SPEC | | | the routing |
| 30 | SPEC | | | the middleware |
| 31 | SPEC | | | the dependency injection |
| 32 | SPEC | | | the transport semantics |
| 33 | SPEC | | | the caching |
| 34 | LANDED | `ConfigSchema` `applySources` `lowerPair` | | the configuration (the face: the schema record + the override ORDER as data — the noncommutative fold, the CF refusals; the sources' text formats are TextKit.ConfigFormat's grammar values; the dogfood is the gates' knobs — Gates.Common's `gatesItem`/`knobOf`/`knobsOfText`) |
| 35 | SPEC | | | the property taxonomy |
| 36 | LANDED | `wp` | | the contracts (`requires`/`ensures` with wp-composition) |
| 37 | SPEC | | | the systems observability lane |
| 38 | LANDED | `Profiled` `Fixed` | | the semantic-profiles lane (16 §4.5 + D24/D38: the phantom-indexed scalar semantics — `Profile`'s closed `plain`/`deterministic`/`fast` slots; the deterministic fixed-point carrier with exact checked add, named floor rounding, total order, codec legality; the fast hop's forfeits as theorems + the exactness tooth; the erasure proved — `Profiled.erase`/`Profiled.iso`, the f64/2^53 hazard's profile law; the codegen face rides `Emit.Profiles` into the Rust const-generic phantom + the TS brand) |

The WATCH entries carry no decl (one line + its trigger, unchanged
below).

## The declaration surface (the product core)

1. **Records + the deriving protocol** (05 §3) — the record is the spec;
   capabilities derive lazily. Home: schema-lang Meta. Guard: curated
   failures land with the first capability.
2. **Keys + foreign keys** — declared keys are determinacy theorems
   (02 §3): they drive API shape (Option vs List results), join
   cardinality, update unambiguity, writable-view derivability. Home:
   schema-lang Keys. Guard: conservative inference — unproven uniqueness
   yields collection results, never invented uniqueness.
3. **Updates (v2)** — multi-set/insert/delete over declared keys, total,
   order-free under disjoint keys (proved once, cited). v1 is demoted
   (no new users). Home: schema-lang Update2. Guard: the byte-tie of
   the updates' emitted surface.
4. **Table invariants** — aggregation predicates over row-sets
   (uniqueness, conservation, cardinality bounds), discharge at the
   computed tier. Guard: the obligation's evidence stays closed.
5. **The entity-machine preset** — `schema_entity_machine` derives the
   machine + keyed transitions + legality + typestate + obligations.
   Guard: hand-built machines carry a written reason (the preset
   rejected them empirically, or they predate it with byte-tie weight).
6. **Pre/postconditions** — obligations at the caller's tier (pre) and
   the function's tier (post). In-type contracts (`{r // P r}`) where
   the authoring surface carries them — Prop erasure makes them free on
   the wire.
7. **Event sourcing** (`@[event_sourced]`) — delta variant + journal
   codec + replay + upcasters derived; replay/inversion/codec laws
   generated. Guard: the command/delta/event trichotomy holds (03 §7).
8. **Effects** — the closed lattice (read/write/guestCap/fail/consume/
   clock/hostIO/observe): effect rows derive from registry items, never
   hand-written; composition joins; an over-permissive composition fails
   to elaborate. Effects (upper bounds, set union) and resources (usage
   accounting, context splitting) are SEPARATE structures — union cannot
   enforce linearity (`{consume h} ∪ {consume h}` loses the double-spend).
   The footprint laws: reads depend only on the declared footprint;
   writes preserve everything outside it; the frame rule composes.
9. **Sessions + boundaries** — protocols as dual-checked sessions; the
   guest boundary's contracts (once/stream/async) as boundary types with
   adapters generated from them. Guard: boundaries closed per app.
10. **Liveness + finite model-checking** — eventually/always-eventually/
    until over the enumerated finite machine, decide-discharged, with
    counterexample traces as data; the honest trichotomy everywhere
    (proved / refuted / unknown-with-reason; budget exhaustion is
    UNKNOWN). Guard: finite only; the TraceModel's heavy half (POR,
    vector clocks) follows its first genuinely-concurrent consumer.
11. **Shrinking** — failing sweeps report the minimal counterexample +
    the shrink path; validity-preserving shrinkers for refined types
    (shrinking `Packet.length` without `bytes` is malformed, not
    smaller); valid values → property tests, raw malformed → boundary
    tests. Home: TestingKit.

## The data plane (02's inventory)

12. **The relational spec layer** — valid worlds as the validity
    boundary (02 §1); constraints as the shared authority.
13. **Weighted relations** (02 §4) — the semiring-K layer with ℤ first
    (dbsp is the instance; do NOT rewrite its proven surface) +
    provenance polynomials second.
14. **The query fragment** — relational logic's honest fragment (02 §2
    + §9's Datalog discipline) over schema-core types, with the
    constraint-driven result typing (02 §3).
15. **Incremental violation relations** (03 §8) — constraints compiled
    to maintained violation queries; the commit gate is the empty-result
    verdict. The product's strongest single composition.
16. **Indexes/caches/subscriptions as materialized queries** (02 §10) —
    one maintenance equation; representation relations to storage.
17. **Writable views** (02 §7) — the derived fragment + explicit
    policies or refusals elsewhere.
18. **The coordination classifier** (02 §8) — invariant confluence as
    a per-operation analysis with named remedies.
19. **Migrations** — the diff computes the change set (a Z-set of
    items: composition = group addition — `v1→v2 + v2→v3 = v1→v3`);
    upcasters derived for the closed change enum; the LOCAL preservation
    equation per migration, replay preservation by one induction;
    stable identities required (renames are not delete+add).
20. **The what-if inspector** — rewind/replay-with-modification over
    the journal (composition of landed machinery).

## The boundary + operations (03's inventory)

21. **The WIT error channel** — typed `result<T, fault>` crossing;
    guests answer typed errors, never traps (W10.2's shape).
22. **The causal error tree** — guest faults map into the host's causal
    tree; reports render both sides' frames; report goldens byte-tied
    (design-faults-observability.md).
23. **Wires** — format × delivery × protocol as declared data (the
    connector library's content; FFI is the synchronous in-process wire:
    the lean-ffi postmortem — a wire with no protocol and no consumer
    dies). Guard: an undeclared channel is a finding.
24. **The connector library** — pipe/rpc/pubsub/queue/sharedMem as
    first-class connector types with protocol semantics; wiring
    mismatches (the protocol incompatibility hiding in the wiring) fail
    at elaboration via duality + effect-row joins.
25. **Capacity (bounded Petri nets)** — counted shared resources: places
    hold token counts, transitions consume/produce; boundedness/deadlock/
    conservation decidable for finite nets (budget-bounded; unbounded
    answers are LOUD). The machine row is the one-token special case.
26. **Runtime monitors** — the monitorable contract fragment compiled
    to observers with the satisfied/violated/inconclusive verdict;
    separates implementation-violated-guarantee from environment-
    violated-assumption. A new obligation mount (gate/lint/test/obligation/
    duel/MONITOR).
27. **Semantic diffs with witnesses** — the breaking gate's verdict
    carries a distinguishing input (searched, checked against both
    versions, shrunk while preserving the difference) or a proved
    observational-equivalence statement.
28. **Checked operational plans** — a goal → a sequence of lawful
    operations, each step's pre/post checked; untrusted planner searches,
    the verified checker validates composition. Honest boundary: the
    plan proves modeled transitions safe under assumptions; the runtime
    executor checks observations and handles failures.

## The authoring/transport stratum

29. **Routing** — route tables are TextKit grammars; disjointness = the
    unambiguity certificate; extraction = the payload correspondences;
    404 = the curated ParseError with the valid space.
30. **Middleware** — ordered transformer chains with a precedence poset
    (decidable) + effect-row joins.
31. **Dependency injection** — the provider DAG; instantiation = the
    cascade's topological fold; acyclicity + satisfiability are
    Statements (this lane re-earns the DAG concept — the leftover rule's
    redemption path).
32. **Transport semantics** — delivery guarantees as data (atMostOnce /
    atLeastOnce / exactlyOnce); at-least-once generates the idempotency
    obligation (decidable for finite handlers); exactlyOnce claims need
    the journal + idempotency-key row, never asserted bare.
33. **Caching** — the coherence obligation (`lookup c k = some v →
    compute k = v`) per cache, discharged at the appropriate tier.
34. **Configuration** (LANDED: `SchemaCore.Config`) — a config = a
    schema record + the override ORDER (last-wins is NOT a semilattice
    — noncommutative; sparse overrides merge per-field via the update
    lane's ColPath write spine; the append law is the honest
    associativity, the noncommutation + the disjoint commutation are
    theorems) + the schema's own validation (the check rows). The
    sources' text formats are `TextKit.ConfigFormat`'s grammar values
    (file/env/CLI, the proved round trips); the refusals ride the CF
    E-code family. FIRST CONSUMER: the gates' own knobs (the C4
    dogfood — `Gates.Common`'s `gatesItem` schema, the config file the
    validated base layer, the env vars the override source with the
    envNat semantics preserved).

## The systems-semantics stratum

35. **The property taxonomy** (Alpern–Schneider as doctrine) — safety /
    liveness / fairness / refinement / contract, classified in the
    battery row data, each kind's home named (safety → machine
    invariants; liveness/fairness → trace props under named assumptions;
    refinement → the refinement kit; contracts → boundary statements).
36. **Contracts** — requires/ensures with wp-composition (the contract
    lanes' composition engine: `wp (p >>= k) Q = wp p (fun x => wp (k x)
    Q)`) — scoped to the contracted lanes; total pure functions keep
    direct proofs.
37. **The systems observability lane** — the causal trail (spec row →
    artifact → obligation → verdict → duel) as data; the E-code is its
    spine.

## The watch list (triggers named; build ONLY when one fires)

- **Statecharts** (hierarchy + orthogonal regions) — trigger: the first
  honestly two-dimensional lifecycle.
- **Kahn process networks** (blocking-read FIFO determinism) — trigger:
  push-based async-concurrent dataflow.
- **Morphic systems** (machines whose states are architectures; dynamic
  topology) — trigger: runtime-created/torn-down topologies per
  deployment. Almost certainly out of this product's scope; named so
  nobody rediscovers it ad hoc.
- **Probability as a fourth root** — trigger: a randomized-semantics
  lane.
- **PolyFun's indexed interfaces / handler independence / WP layer** —
  triggers per notes/studies/polyfun-study.md.
- **The categorical migration apparatus (adjunctions)** — trigger:
  migrations composing in practice; the composition law (19) covers the
  near term.
- **L* automata learning** — trigger: a legacy system to onboard
  behaviorally.
- **W9.8 semantic preservation** (the wasm backend's correctness
  against a Lean-side semantics) — the research item, last.

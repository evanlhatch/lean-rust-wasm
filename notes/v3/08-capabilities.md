# 08 — The capability catalog

The concrete specs. Each entry: the shape, the roots it rides (01), the
kit home, the acceptance test, the guard that keeps it honest. This is
the inventory — the detail lives in the named design docs where they
exist (notes/design-*.md); this file's version is the contract.

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
    tests. Home: TestKit.

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
34. **Configuration** — a config = a schema record + the override ORDER
    (last-wins is NOT a semilattice — noncommutative; sparse overrides
    merge optional fields; document which) + the schema's own validation.

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

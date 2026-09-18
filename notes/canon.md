# The canon — one table of what everything IS

Status: binding design reference. Companion to lean-doctrine.md (the
rules) and vision.md (the product). This doc exists so that design
review is one question: **which row is this?**

The rule (binding): when you build or review anything — a subsystem, a
module, a feature, a test — name its row. If it's a row, it inherits
the row's laws, oracle coverage, and codegen path, and you may NOT
re-derive them by hand. If it matches no row, that is a FINDING: bring
it to design review; the canon grows deliberately, in this file, never
in a code comment.

The kernel concepts (vision.md): Universe · Correspondence · Law class
· Machine · Registry→Emitter · Surface · Obligation. The canon rows
are built from these seven and the dbsp algebra (Stream, D, I, fix,
Z-sets).

---

## Part 1 — the algebra rows (the base vocabulary)

| One side | IS | the other side | Laws you inherit |
|---|---|---|---|
| delta | = | event = patch = journal entry = undo unit | the group structure (assoc, comm, invert) |
| `D` (differentiation) | = | diff = edge-detection = change feed | D/I inverse pair (dbsp.Linear) |
| `I` (integration) | = | fold = replay = materialization = snapshot reconstruction | `derivative_integral` |
| snapshot / checkpoint | = | partial integral | `checkpoint_is_state` |
| stream | = | history = signal = time series | extensionality, `agree_upto` |
| rollback / undo / time-travel | = | group subtraction (invert + patch) | `ChangeInversion.correct_invert` |
| hot-reload | = | the same input stream through a new circuit | `incrementalize_ok` says what "correct" means |
| replica consistency | = | eventual equality under equal total input (divergence = group subtraction) | `two_replica_converge`, `batch_order_irrelevant` |
| build-system incrementality | = | incremental view maintenance | the whole incremental family |
| gate / trigger `on(p)` | = | `distinct` over the satisfaction relation = derivative sign-change | `distinct_incremental_ok` (nonlinear — needs old state) |
| observer / subscriber | = | stream tap = incrementally maintained view | linearity of the view's operator |
| cascade pass | = | pregel round = semi-naive iteration = `fix` step | `seminaive_equiv`, `fix_unique` |
| recursive query | = | least fixed point | `fix_eq`, `fix_unique` |
| tick | = | Mealy machine (cascade = combinational settle) | machine theory (Part 2) |
| order-freedom | = | confluence | `batch_order_irrelevant` (direct ZSet-fold proof, Dbsp/Replicas.lean); confluence-via-cslib (not wired — dropped 2026-09-16; re-add when a consumer order exists) |
| refinement / conformance | = | simulation (trace inclusion) | the oracle conformance machinery (`CompareMode`/`Verdict`, wasm-backend/Oracle.lean); simulation-via-cslib `IsSimulation`/`sim_trace` (not wired — dropped 2026-09-16; re-add when a consumer order exists) |
| observational equivalence | = | bisimulation | cslib `IsBisimulation` (not wired — dropped 2026-09-16; re-add when a consumer order exists); `Machines.Fusion.bisim_iff_resp_streams` (the stream-equality statement — deterministic finite case) is the current carrier |
| conservation law | = | linear equality over stocks | `linarith` discharge |
| floored stock / budget / quota | = | a canonically-ordered value with monus (nonneg BY CONSTRUCTION) | the monus lemma set |
| tech tree / schedule / dependency graph | = | DAG = partial order (dangling edges unrepresentable: `Dag n` is Fin-indexed) | acyclicity by `decide`; reachability = a fixpoint |
| registry replay (oleans) | = | event sourcing (append on add, concat on import) | determinism of the fold |
| a registry (closed, authored) | = | `CodegenCore.DataRegistry` — uniqueness in the type, a duplicate is an elaboration failure | `lookup?_ok_unique` / `lookup?_miss` |
| an environment (open, runtime authoring) | = | `QLang.Registry` — re-declaring a name IS rebinding (last-binding-wins); NOT a DataRegistry (qlang audit 2026-09-16: deliberate divergence, distinct row) | the rebinding semantics is currently unpinned — a shadowing test is the named follow-up |
| schema evolution | = | snapshot = partial I; `Diff` = D of the schema-event stream; migration = the delta transformer; breaking gate = "the old log replays through the new universe" | the whole event-sourcing row |

## Part 2 — the machine rows

| Shape | IS | Laws / artifacts you inherit |
|---|---|---|
| guarded state machine | = | `Machines.Machine` — two projections, agreement by construction (`tr_iff_step?`) |
| a machine's legal sequences | = | a regular language (entity machine = DFA; legality check = membership) | cslib automata/MyhillNerode (not wired — dropped 2026-09-16; re-add when a consumer order exists) |
| entity lifecycle | = | a machine ON a record: enum state column + transitions; transitions are deltas on the state column (W8.4) | legality relation, typestate Rust, journal antijoin check, replay/rewind — all derived |
| protocol / choreography | = | a session (Machines.Session): payload-typed, dual-checked | duality, mid-protocol deadlock-freedom, termination |
| the guest↔host effect loop | = | a session protocol (commands out, events in — W8.6) | the session row |
| a wizard / multi-step flow | = | a SEQUENCE (indexed monad / session), NOT a machine — machines are SETS of transitions; protocols are orders | the session row |
| saga / workflow with compensation | = | a machine whose transitions carry inverses; compensation = rewind | `ChangeInversion`, `rewind_suffix` |
| retry / circuit breaker | = | a small machine + a fault policy row (the faults registry) | the machine row |
| convergence / termination | = | a decreasing variant (Machines.Convergent) OR fuel (when the cap IS the semantics) | `terminates`, `run_length_bound`; cslib `SN`/`Terminating` (not wired — dropped 2026-09-16; re-add when a consumer order exists) |
| the build pipeline itself | = | a machine (Pipeline.lean — already canonized) | its own row |

## Part 3 — the business-software rows (what the toolkit must make cheap)

| The app's concept | IS | Realized by |
|---|---|---|
| a table of entities | = | a `@[schema]` record + declared keys (W8.2); row sets are Z-sets (bags with negative weights) |
| a business rule / batch update | = | a `schema_update` (named, total, order-free; guard + write) | W8.3 grows multi-column/insert/delete |
| an event log | = | `@[event_sourced]` (W5.1): delta variant + journal codec + replay + upcasters, derived |
| a queue / mailbox | = | a stream + a cursor; redelivery = replay from cursor; at-least-once + idempotent consumer | W8.6 effects + the stream rows |
| the outbox/inbox pattern | = | journal + cursor + retry machine | composition of rows |
| idempotency key | = | `distinct` over the journal | the gate row |
| soft delete / tombstone | = | a negative-weight delta | the Z-set row |
| an audit log | = | a read-only journal projection | the stream row |
| CQRS | = | the update/query split: commands are deltas; queries are incrementally maintained views | W8.3 + W4.4/W4.5 (dbsp circuits) |
| a derived view / subscription | = | a circuit (query) maintained incrementally | W4.4/W4.5; the frontend DSL is LATER (scope lock) |
| a unique/conservation constraint | = | a table-level invariant via an aggregation predicate | W8.7 |
| a workflow status (order lifecycle, ticket state) | = | the entity-machine preset | W8.4 |
| a schedule / rate / deadline | = | stream operations (sampling, delay, comparison) | W8.5 — never a separate time system |
| a side effect (email, charge, HTTP) | = | a command VALUE returned by the guest; the host executes; the result returns as an event | W8.6 |
| a reusable schema fragment | = | a template with slots (substitution), NOT a type-level generic | W8.9 |
| `Page<T>`-style wrappers | = | monomorphized reflection | W8.12 |
| documents / trees / threads | = | recursive types behind fuel | W8.13 |
| a feature flag | = | a record + an update (the feature-flags package is the dogfood) | exists |
| a fault / error | = | a `Fault` variant: typed at the wire (`result<T, fault>`), E-coded, shared elab↔runtime | W6.5 |
| observability spans | = | schema items; trace analysis = a query over the span stream | exists + W2.7 |

## Part 4 — the toolkit-internal rows (the meta shapes)

| The mechanism | IS | Notes |
|---|---|---|
| a codec | = | a `PartialIso` (append-form law transported through bind) | W1.2, W7.14 |
| a printer↔parser pair | = | one grammar as data + ONE inversion theorem | W5.3, W7.10 |
| a transition table | = | the step function (`tableStep?_eq_step?` — data IS code) | W2.3 generates it |
| a decidable check | = | a `CheckedProp` (relation + checker + sound [+ complete]) | W1.1; the bridge is TYPED, gaps are LOUD |
| an emitter | = | a pure fold `spec → List GeneratedFile` + declared outputs + `outputs_nodup` | W7.9; drivers own IO |
| the byte-tie | = | the emitter's correspondence law, CI-enforced | exists |
| an elaboration gate | = | a decl-check mounted as attribute-gate or lint | W7.13 |
| a negative control | = | proof the test isn't vacuous; mandatory, generated by the derive skeleton | W7.3, W7.7, W7.17 |
| a cert citation | = | a theorem name resolved at elaboration/CI | Dbsp.Certs; W4.4 uses it in emitted headers |
| the differential oracle | = | a simulation discharged by testing (sabotage controls mandatory) | W6.3 |
| a generated file header | = | the artifact's self-description (spec sha + content hash) | exists |
| a debug view | = | an emitter called at elab time, never a re-render | W7.10d |
| the world (component boundary) | = | a registry item | W2.7 |

## Part 5 — the shelf (named, flip conditions — do not build until flipped)

| Pattern | Flip condition |
|---|---|
| Quotient types | no computable canonical form exists AND proof-land only (canonical forms dominate: TableEq sorts, Z-sets are Finsupp) |
| PHOAS | a binder-heavy surface (a comprehension/datalog DSL); reify immediately to the first-order core |
| Final tagless | ≥3 interpreters over one expression language drifting apart (W3.4 is the experiment) |
| Graded monads | author-visible budgets (action points, mana) — NOT engine cost (that's data) |
| Dijkstra monads | the guest lane wants fuel/capability contracts riding in action types |
| Measured monoids / finger trees | hot time-travel slicing — lands in RUST, not the model |
| Coinductive types | never — streams are `Nat → a`; `partial_fixpoint` covers recursion |
| HML / modal logic (cslib) | protocol properties need logical characterization beyond trace equivalence (not wired — dropped 2026-09-16; re-add when a consumer order exists) |
| SMT subprocess | never trusted; `bv_decide` LRAT certificates are the lane (SymCC's checked-witness shape adopted, its trust rejected) |
| Specimen (derived generators for relations) | the first relational spec needing generation (`ValidTrace`), or their Basalt port landing |

## Part 6 — using the canon in review

1. Name the row. Link it in the module header.
2. If a row exists: instantiate; do NOT re-derive the laws — cite the
   instance. A re-derived law is a review finding.
3. If no row exists and the shape recurs (≥2 sites): propose the row
   in this file FIRST (design review), then build.
4. If a row stops paying (no consumer for a release cycle): mark it
   `seed` in notes/reuse-map.md (never silent deletion of loadbearing
   rows; never keeping dead weight unmarked).

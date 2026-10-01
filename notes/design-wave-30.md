# wave 30+ — THE MASTER PLAN (every discussed addition + improvement)

The exhaustive consolidation of the session's design threads, each with
its execution shape. Doctrine citations per row; the zones + the
verification discipline per phase. The standing rules (10) govern every
landing: rows + instances or a design failure; the leftover rule; the
audit loop at each phase's end.

## PHASE A — the center + the roots' claims on the tree itself

A1. **The carrier-as-graph bridge** (16 §4.1; F1). Every carrier value
    (Iso/Retraction/Codec) induces its graph `Rel`; ONE composition
    tower; carrier `trans` vs `Rel.comp` die as parallel stories.
    Zone: kit/Kit/{Correspondence,Relation}.lean. Accept: the duel
    chain + a migration chain compose through the tower; the axiom
    surface shrinks or holds.
A2. **The one-log registry discipline** (N1 + S6; 10 Phase 5). The Lane
    substrate's per-lane extensions (a dozen+) → ONE extension with
    lane-tagged rows; the replay routes; the snapshot covers the lanes'
    rows (not just schema items). Zone: kit/Kit/Lane.lean + all
    register_lane consumers + schemacore/SchemaCore/Snapshot.lean.
    Accept: a new lane = one row + one reader; the snapshot's coverage
    theorem extends to the lanes.
A3. **The adjunction + the Galois connection + the universal property**
    (T1/T2/T3). D ⊣ I with unit/counit (the fusion bridges as the
    triangles); observers ordered by coarseness with coarsen ⊣ refine;
    ZSet as the free abelian group on the bag (the universal property:
    homs out ≅ weight-preserving maps). Zone: machines' Fusion +
    kit/Kit/Observer.lean + zset. Accept: the existing bridge/observer/
    evaluate theorems become corollaries; zero consumer breakage.
A4. **The executor-as-machine + the wp↔machine bridge** (U1/O1/O6).
    WasmCore.Exec + the guest's evalS as TraceModel instances (the
    conformance battery + finality free); `wp_sound` as the simulation
    between wp and machine semantics. Zone: wasmcore + guest/Guest/
    Correct.lean + contracts + machines. Accept: the duel restated as
    machine simulation; the contracts' VCs tied to executions.
A5. **The Crash discipline → the persistence model** (O7). The delta
    log as a machine (one transition family: append); the torn-tail
    recovery's correctness as the Crash discipline's theorems; the
    Rust side tied by the duel. Zone: machines + schemacore (the log's
    Lean model) + crates/mandate-delta (the duel rows).
A6. **The roots' self-audit repairs**: the pre-Spec test suites migrate
    to TestingKit.Spec (O4: machines' Crash/Coalg/Session + cost's);
    the parked-module deletions (Kit.Json/Kit.FreshName/Kit.Validation
    — 07's table's own rule: two phase boundaries, no trigger);
    Kit.Hyper gets its consumer deadline named (16 §4.3's lane or the
    next boundary's finding). Zone: the test libs + kit.
A7. **The macro-driver unification** (O3/F3/T7): the parse-route
    pattern (render-to-source + re-parse — wave 29's DepFold lesson)
    into 12-construction.md + 15-patterns.md as a named pattern FIRST,
    then the Derive family's quotation plumbing probed for migration
    (measure: the splice machinery's LOC vs the renderers'); machine! +
    register_lane ride Derive.Common. Zone: kit/Kit/Derive/* +
    machines/Machines/Dsl.lean + kit/Kit/Lane.lean.

## PHASE B — the system's self-conformance (the enforcement-on-self wave)

B1. **The gates' findings ride Diag + E-codes** (S3; 05 §4). LintFinding
    + the gates' finding shapes → the ONE envelope; every gate verdict
    carries its registry-allocated code. Zone: lintkit + gates +
    kit/Kit/Diag.lean. Accept: a gate failure renders the envelope with
    a live code; the code-registry coverage tooth covers the gates'
    own messages.
B2. **The feasibility gate row** (S4; 04 §5 + D21). The spec-sanity
    gate: every registered contract/spec answers feasibility (a
    satisfiable precondition witness or the declared-emptiness note);
    the contracts lane's VCs first. Zone: gates + contracts +
    kit/Kit/Obligation.lean. Accept: a vacuous `requires` fails the
    gate; the row joins gateNames.
B3. **The gates' report files ride the grammar layer** (N2; 05 §1).
    The axiom report + coverage matrix + elab-baseline + nolint-census:
    each a Grammar value + the generated round-trip laws (the registry
    text + the snapshot's item level are the precedents). Zone: gates +
    textkit. Accept: the hand renderers/parsers die; the byte-ties hold.
B4. **The legacy-immutability tooth** (S5). A gate row hashing legacy/'s
    surface; drift = a finding. Zone: gates. ~30 LOC.
B5. **The 08-status discipline made mechanical** (S1 + the enforcement
    audit's #8): docs-check extends — every LANDED entry in 08 names a
    resolvable decl; every SPEC/PARTIAL entry's named remainder checks
    against the tree. The stale rows repaired (§15 → LANDED, 13's
    deferred note → landed). Zone: gates/Gates/DocsCheck.lean +
    notes/v3/08 + 13.
B6. **The evidence-redundancy lint** (F7; D37; the enforcement audit's
    #6): census-first (a baselined report-gate on the decide-first
    pattern), the constructor-guaranteed-proof heuristic; promote per
    09 §8's trigger. Zone: lintkit + gates.
B7. **The gates as obligation values** (T5): the gates' own invariants
    enter the Kit.Obligation substrate (the baselines = discharged
    certificates; the re-baseline = the replay discipline; the
    trichotomy N9 on the gates' state). Zone: gates + kit. THE
    self-application; B1-B4 are its rows.

## PHASE C — the generated entourage's new faces (the spine's rows)

C1. **The observability face** (fast-observe; U2; 12 §8's mandate).
    Faults.Emit emits fast-observe's `error!` SYNTAX (the E-codes map
    onto `#[code]` verbatim; the category↔policy mapping aligns by
    construction; ONE registry, two faces); the CodeTarget spine gains
    the observability TargetFace (one dotted-static `scope!` per schema
    operation; high-cardinality via log kv NEVER scope tags;
    `register_statics` on wasm); the self-audit's span-coverage row
    (09 §5: generated host code without span coverage fails). THE
    HONEST COST: fast-observe needs nightly
    (`error_generic_member_access`) — the Rust lane pins nightly;
    surfaced in the docs. The observer-transparency theorem (U2): the
    instrumented host refines the plain host — the coarsening instance.
    Zone: faults/ + schemacore/SchemaCore/Emit/ + crates/ + machines
    (the observer theorem).
C2. **The bench/e2e face** (the flatland templates; U5). Benches as
    DUEL ROWS (candidate vs baseline, same seeded inputs, the threshold
    verdict — parity/within-noise/within-5%); the e2e validator
    generated per schema (the twin-world hash-chain determinism + the
    per-rule expected values with notes); `bench_profiled` riding the
    production `scope!` calls (fast-observe's bench feature); the four
    templates (codec round-trip, commit-path, encoding sweep,
    affine/pushdown) as spine rows. Zone: kit/Kit/Duel.lean +
    schemacore's Emit + crates' benches/ + vortex.
C3. **The contracts→fuzz face** (U4; 12 §8's bolero mandate). The
    generated `Arbitrary` impls from TestingKit's generators (ONE
    generator definition, the Lean sweep + the Rust fuzz as two
    consumers); the contract VCs as bolero properties at the boundary
    (the Lean proof covers the model; the fuzz covers the runtime).
    Zone: schemacore's Emit + testingkit + crates' fuzz targets.
C4. **The config face** (08 §34; the user's figment replacement). A
    config IS a schema record; the override fold IS the update lane
    (the ColPath spine; the noncommutative ORDER as data); the sources
    (CLI/env/file) are TextKit grammars; validation IS the check lane;
    the Rust config rides the codegen spine. FIRST CONSUMER: the tree's
    own knobs (N8 — the gates' GATES_ALL_JOBS/budgets/RSS ceilings as
    the dogfood). Zone: schemacore + gates + textkit.
C5. **The inspector eats qlang** (N3). The ledger/registry/snapshot as
    tables; the inspector's 15+ hand query shapes → `qlang!` queries +
    a render face. The system's introspection dogfoods the query
    language (qlang's second consumer — the leftover rule's discipline).
    Zone: inspector + query.
C6. **The op table → the duel rows** (N5; 07 R6's full consumption).
    The duel vectors generated from the op table's rows; a new op gets
    its duel coverage free. Zone: wasmcore + the duel lane.
C7. **Kit.Cli** (N6): the one exe-driver discipline (the subcommand
    table + verdict/exit + the shared flags); the gates/inspector/
    lintkit/regen exes adopt. Zone: kit + the exes.

## PHASE D — the wasm depth (the cutting edge, modeled)

D1. **wasmi: the third duel leg** (Phase 10's second embedder + the
    portability proof). Port guestlang-rt's DISCIPLINE (not the code):
    the deterministic profile AS DATA (fuel, floats-off,
    lazy-translation pinned — ONE profile table all engines share; the
    f64-refusal as a CheckedProp verdict); the stable-fuel pin; the
    rt-conformance gate = the three-way duel (Lean exec ≡ wasmtime ≡
    wasmi — needs A4's machine instances). Zone: crates/ (new
    mandate-rt) + wasmcore + the duel lane.
D2. **The WIT extension: resources + streams + futures** (WASI 0.3).
    The typed WIT AST gains the rows; the PROVED parser/renderer laws
    extend; resources ride the effects lane's resource discipline
    (double-drop unrepresentable); the async protocol (task-return/
    waitable-sets) as SESSIONS (T4: the world = the session type; the
    host/guest = dual endpoints; the linker errors = duality failures
    with typed witnesses). Zone: wit/ + machines' Sessions + effects.
D3. **The capability valves as effect rows** (N7; 10 Phase 7's
    acceptance): the WASI capability set = the JOIN of export rows
    (the effects lane's closed lattice + footprint laws), never a
    bitflag. Zone: effects + the host.
D4. **wac composition as a relation** (the component graph = nodes +
    typed edges; interface compatibility = a join; unresolved imports =
    a negation query; the composition spec in Lean → the generated wac
    file → wasm-tools validates). THE INTERPOSITION/DI SEAM: middleware
    as component composition — faults + observability FIRST, auth/
    routing LATER through the same seam (08 §29-31's specs). Zone:
    wit/ + a new composition module + crates.
D5. **OCI + the provenance-badged store** (legacy's forge oci.rs mined
    from jj history): the artifact store; the provenance annotations ARE
    the gates' outputs (the axiom-report badge); pull refuses
    `unchecked`. Zone: crates/ (forge-equivalent) + the ledger.
D6. **The legacy ports with new-tree homes** (the legacy audit's
    load-bearing five, the remainder): the skew fail-fast (component-
    type introspection vs the committed WIT — low cost), the
    @[invariant] host-gating lane (the witness checker's host face),
    the fault-typed result channel (result<T,fault> end-to-end — 13's
    boundary row; the faults lane + the WIT extension's result face),
    hot reload (the component swap discipline), the Layout theorems
    (the proved canonical-ABI layout — the offsets/size + non-overlap
    theorem port as CONTENT). Zone: per lane.

## PHASE E — the surface + the product (the flatland rewrite)

E1. **The authoring surface** (notes/design-authoring-surface.md's 7
    waves): the `table` clause macro (desugars to the SAME mounts; the
    machine! precedent; A7's parse-route discipline) + the STREAM
    idiom's words (stream/delta/view/on riding the event-sourcing
    machinery; the trichotomy as types) + the evolution workflow
    (versioned tables; diff→plan→upcaster derived; the refusals at
    elaboration) + the six-word vocabulary's acceptance test. Zone:
    schemacore + kit.
E2. **The semantic-profiles lane** (16 §4.5, ACTIVATED; D38):
    `Float Deterministic` (fixed-point, codec-legal) vs `Float Fast`
    (the forfeited laws NAMED) as phantom indices; the f64/2^53 hazard
    (the flatland study) resolved HONESTLY; Money/units erase at
    runtime. Zone: schemacore + the codec lane.
E3. **The flatland absorbables into vortex** (the study): the
    AffineKernel generalization (shiftFoR's general form: mul/dict/
    constant arms — compute pushed INTO the encoding); the dtype policy
    rows (u*-only keys, i* via FoR, f* via ALP-terminal, BitPacked
    terminal; "the compiler predicts, never searches"); the guards'
    edge-case discipline. Zone: vortex/.
E4. **The flatland-core dogfood** (16 §6, the proof): the 10K-entity
    tick slice end-to-end — schema → encodings → compute-on-compressed
    tick → wasm guest → delta log → observability → the pair-bench
    verdict vs flatland's numbers. THE MAXIMAL-CONSUME TEST: any new
    machinery it needs is a doctrine finding. Zone: a new dogfood app +
    everything.
E5. **The asyncband models** (the machines/sessions per primitive
    family: the locks' safety invariants PROVED, the channels as stream
    disciplines, singleflight as 02 §3's determinacy shape, the pool as
    the effects' resource split) + the conformance duel (model ≡
    asyncband behavior). Zone: machines + a models module + crates.
E6. **The edgepython surface growth** (strings/records/lists — the IR
    carries them; the surface exposes them) + the guest's remaining
    fragment (the RC cascade's reuse, the externs' deeper discipline).
    Zone: guest/.
E7. **The quickstart + user guide** (the authoring loop as a user
    walks it; the dogfood as the running example). Zone: notes/ + the
    scaffolder.

## PHASE F — the engine gaps + the research items

F1. **The substrait typed decode ladder** (IN FLIGHT — the
    continuation's rungs 4-6 + the full-circle pin + the tests; the
    finisher queue).
F2. **The qlang join wall** (DISSOLVED): the typed join gained the
    SHARED-BASE reading (`Substrait.Typed.Rel.join'` — both children
    read the same stream, the query lane's reading; the caller-spelled
    output via the `AppendCols` witness — the Keep pattern twice, no
    transport), the BUILT condition (`Query.TypedBridge.joinCond` —
    the lifted key reads, the type disagreement IS the resolution
    failure), the pair walk's completeness mirror
    (`evalJoinPairs_ok_complete`), and the qlang! `then join` stage;
    the agreement extends BOTH directions (`qEval_sound`/
    `qEval_complete` over the join arm). The residue is the named
    narrowings (QL0001: key resolution / key-type disagreement / the
    u64-string comparison-kernel fragment; inner-only; the wire
    spelling refuses — the keep precedent).
F3. **The DepFold fragment's extensions** (multi-index, Prop sorts,
    params — the named refusals KD0015-0019's covered set grows as
    consumers need).
F4. **The binary wasm decoder** (the encoder's sleb is one-directional
    until this lands; the read direction's codec + the round-trip).
F5. **The verified query optimizer's foundation** (T6; 02 §6): the
    semiring's equational theory (join cost, projection-pushdown,
    selection-fusion) as theorems; the optimizer as the checked-
    rewriter (untrusted search + verified check — 04 §3's certificate
    pattern). DataFusion executes; we emit PROVED-equivalent plans.
F6. **The Grammar layer's fold discipline vs the Derive generators**
    (O2's probe): does declare_fold/DepFold cover the grammar's
    recursion shape; migrate or name.
F7. **PARKED (research-grade, named not ground)**: pattern #17's
    ctor-armed recursion wall; U7 (parsing as the coalgebraic half);
    the hyperproperty lane's first consumer (Kit.Hyper's trigger:
    noninterference/schedule-independence — candidate: the asyncband
    models' schedule-independence, E5); the cone transitivity (the
    enforcement audit's #9 — fires with the first shim).

## The standing conformance teeth (every phase)

- The 07 recipe entry + the 08 spec line FIRST (the README's protocol).
- The six-word vocabulary's acceptance test for surface words.
- The evidence entourage's first question for every artifact (does the
  type already carry it?).
- The audit loop at each phase's end (DRY/conformance/consumption);
  findings convert to fixes + enforcement in the same wave.
- The parked-module table's discipline (07): triggers named; two
  boundaries without a firing = deletion.
- 08's status discipline (B5 makes it mechanical): a landing moves its
  row in the same commit.

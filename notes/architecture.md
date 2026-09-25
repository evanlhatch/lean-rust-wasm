# The architecture map

**What this file IS and is not.** The MAP of the mandate tree — the
libraries, the concepts, the data flow, the surfaces — so the
architecture is legible without the conversation. It is NOT the spec:
the committed artifact + its emitter are the spec of record
(`notes/v3/13-interfaces.md`'s own rule); every claim here points at
the code that owns it. A row here that rots is a doc to fix; a row
whose owner changed is a tree event. The doctrine lives in
`notes/v3/` — this file never re-states it, only cites it.

The architecture in two sentences (`notes/v3/01-core.md`): structure
composes; interpretations preserve structure; proofs compose through
explicit relations. The spine is ONE shape — registry → interpretation
→ artifact — and every emitter, gate, and generator in this tree is a
reading of it.

Truth anchors for this file (verify against these, never against this
file): the library list is `lakefile.toml`'s `[[lean_lib]]` rows; the
cone table is `LintKit.Cone.coneOfRoot?` (`lintkit/LintKit/Cone.lean`);
the gate set is `Gates.gateNames` (`gates/Gates.lean`); the gated set
is `Gates.Packages.gatedPackages` (`gates/Gates/Packages.lean`); the
test exes are the justfile's `test_libs`; the artifact list is `gen/`
+ the committed baselines under `notes/`.

## 1. The layer map

The cone order (`Cone` in `lintkit/LintKit/Cone.lean`):
`c0machinery ≤ c1domain ≤ c2theory ≤ c3app` — a module may sit on its
own cone and every cone below; importing cone-high is a gate failure
(the `linter.guestlang.coneImports` module linter; the table is DATA,
the lakefile records only build shape). The C0/C1 kernels additionally
ban `Mathlib`/`Batteries` (`Cone.bannedRoots`).

### C0 — machinery (any package may import)

| Lib (srcDir) | Owns | Key types / disciplines | Consumed by |
|---|---|---|---|
| `Kit` (kit/) | the crossing substrate: ONE graded-correspondence library + the relational engine + the Change ladder + obligations + the emitter spine | `Kit.Correspondence` (Iso/Retraction/Codec/Normalization/Simulation/Abstraction), `Kit.Relation` (THE generic preservation theorem), `Kit.Hyper` (`Noninterfering`), `Kit.Obligation` (closed Tier + Evidence), `Kit.Emit`, `Kit.Change` (Applicable→Additive ladder), `Kit.Observer`, `Kit.Lane` (`register_lane`), `Kit.Diag`, `Kit.CodeRegistry`, `Kit.Varint`, `Kit.Text`, `Kit.Duel`, `Kit.Mangle`, `Kit.Registry`, `Kit.CheckedProp`, `Kit.Suggest` | everything below |
| `TextKit` (textkit/) | the core-only text/parser foundation; the char level's ONLY home | `Parser` (List Char → Option), the inversion kit, the shared literal-rfl family (`TextKit.Literals`), `ParseError`; owns the ONE `Diag` + did-you-mean envelope (Kit re-exports) | Substrait; Kit (the shim) |
| `TestingKit` (testingkit/) | the shared test harness (golden discipline) | core-only; no LSpec/Plausible | Scaffold; the test exes' discipline |
| `LintKit` (lintkit/) | the env-linter engine + the cone table + the axiom allowlist | module-level linters over `env.header`; `Cone.coneOfRoot?` (the DATA table); `AxiomAllowlist` | Gates (consumes, never re-encodes); GuestStd (`GuestGate`); every gated srcDir (the `lintkit` driver) |
| `Gates` (gates/) | the gates machine: the registry + the report-gate combinator + every gate row | `Gates.gateNames` (the closed run order), `Gates.Packages` (the gated set, ONE table for every consumer) | the justfile's rows; CI |

### C1 — domain cores (+ the C1-adjacent machinery)

| Lib (srcDir) | Owns | Key types / disciplines | Consumed by |
|---|---|---|---|
| `SchemaCore` (schemacore/) | the closed type universe + the item model + the derivation layer + the schema regen | `Ty` (closed boundary universe), `Value`, `Item`, `@[schema]` + the env extension, `Describe` (D19's ONE meta-universe), `Codec` (the append-form master law), `Derive` (`law_of_rows` proved ONCE), `Snapshot` (the proved round trip), `Emit` (+ `.Journal`, the duel vectors for the Rust side) | Query, Substrait, Vortex, Inspector, Gates.GenCheck, the Rust emitters |
| `WasmCore` (wasmcore/) | the wasm domain model: ONE instruction AST over the kit's machinery | `Types`, `Instr` (the ONE AST), `OpTable` (one row per op ctor), `Validate` (Kit.CheckedProp), `Encode` (Kit.Codec), `Wat` (the Emitter row), `Exec` (the fuel-bounded machine + `step_preserves`), `Duel` | Guest (read-only); `wasmgen` |
| `Wit` (wit/) | the typed WIT target AST + the ONE renderer | misrendering unconstructible (the nodup facts ride the type); total AST → text fold | SchemaCore.Emit |
| `Machines` (machines/) | the TraceModel root's foundation: machines, traces, bounded exploration, the `machine!` DSL | `step?` + the `step_iff` bridge (pattern #1), witness-carrying `Exec`, the honest trichotomy (proved / refuted / unknown), `MachineWithInv` + the `machine!` macro | SchemaTests (EntityMachine); the conformance battery |
| `ZSet` (zset/) | the Change root's additive foundation | the canonical Z-set (canonical-rep, not a quotient), the `Kit.Change.Additive` instance, the trichotomy types (command/delta/event) | Query, Circuit |
| `Datalog` (datalog/) | the data plane's executable fragment (02 §9) | typed predicates, the safety checker + the loud refusal, LFP semantics, the fuel = height-bound evaluator + its correctness theorem | its tests |
| `Cost` (cost/) | the quantitative-semantics foundation | `CostModel`, `Graded` (the writer shape), the plain/cost-graded interpretation pair via `Kit.Relation`, the budget/monus tie | its tests |
| `Effects` (effects/) | the closed effect lattice + the resources split | the 8-atom lattice, rows as finite sets, the check boundary, the footprint laws + the frame rule | Contracts |
| `Contracts` (contracts/) | the contract lanes' wp engine | requires/ensures + wp-composition, the soundness theorem, the discharge discipline over `Kit.Obligation`, feasibility (04 §5) | its tests |
| `Analysis` (analysis/) | the abstract-interpretation foundation | the γ-carrier + soundness-field transfers, bounded intervals over ℤ, the checker shape via `Kit.Relation` | its tests |
| `Query` (query/) | the typed relational fragment over the schema | FD-driven result typing (keys are determinacy theorems, 02 §3), weighted evaluation, `evalQ_wmap` (the weight-polymorphism theorem) | its tests |
| `Vortex` (vortex/) | the encoding-selection seed | the pure static selection function (never a runtime search), the layout emitter row over the closed `Ty` | its tests |
| `Circuit` (circuit/) | the incremental circuit lane over the Z-set substrate | operator templates, the incremental face (the cross term, old-values parameters), `Ckt.incrementalize_ok` (the agreement theorem), `recursiveOpt` | its tests |
| `Repr` (repr/) | the representation-independence lane | `Represents` (relation + preservation fields + the construction gate), THE generic client theorem, `Repr.FinMap` (two honest representations) | its tests |
| `Substrait` (substrait/) | the substrait port's seed | the wire-faithful Proto types, the typed layer RETARGETED onto `SchemaCore.Ty` (the parallel universe died), the WF bridge, the text fragment + round-trip theorem | its tests |
| `GuestStd` (std/) | the guest-compilable std surface | the oracle bodies + `@[guest_std]` (LintKit.GuestGate's elaboration-time ban) | the Guest lane's compile set |

### C2 — host lanes (read the domain cores; not domain cores)

| Lib (srcDir) | Owns | Key types / disciplines | Consumed by |
|---|---|---|---|
| `Inspector` (inspector/) | the evidence-chain inspector | the obligation row + closed discharge state, the why-sweep, the replay (mirrors the gates' `loadPkgEnv`, not imported — stays a leaf), the ledger views, the citation census | the `inspector` exe |
| `Scaffold` (scaffold/) | the application-scaffolding generator | the `AppSpec` (a declarative Lean VALUE), the curated validation, the total generator to Lean source (01 §5's engine reading), the seeds-once `Flow.lean` rule | DemoApp, LedgerApp |
| `Guest` (guest/) | the LCNF→wasm guest-compiler lane | `Guest.Lcnf` (the host-side reader; `import Lean` is the lane's disclosed discipline), `Guest.IR` (the frontend-agnostic contract), `Guest.Lower` (consumes ONLY the IR), the component emission through the emit spine | `componentgen`; ComponentTests |

### C3 — apps

| Lib (srcDir) | Owns | Discipline | Consumed by |
|---|---|---|---|
| `ScaffoldDemo` (`.` → `DemoApp.*`) | the adopted generated skeleton (the compiled-ness proof) | generated `Reg`/`App`/`Tests` committed verbatim, byte-tied; `DemoApp.Flow` hand-owned | ScaffoldTests |
| `ScaffoldLedger` (`.` → `LedgerApp.*`) | the dogfood skeleton | same discipline; `LedgerApp.Flow` is the fill obligations' home | ScaffoldTests |

The external `[[require]]` rows are tooling, not layers: `Cli`
(lean4-cli, the gates exe's argv parser), `lean4lean` + `batteries`
(the kernel-check gate's independent double-check; the tree's own
libraries import nothing from batteries — the cone rule).

## 2. The concept map

The cross-cutting machinery of `notes/v3/01-core.md` — which module
owns each, who consumes it.

| Concept (doctrine slot) | Owner | Consumers |
|---|---|---|
| the ONE carrier (graded correspondences, 01 §4) | `Kit.Correspondence` | WasmCore.Encode/Validate, SchemaCore.Codec/Derive, Repr |
| the relational engine (01 §6) | `Kit.Relation` | Cost, Analysis, Repr, Query (the weight-poly theorem), Contracts |
| the Change capability ladder (01 §2) | `Kit.Change` | ZSet (the Additive rung), Circuit |
| the observer parameter (04 §4) | `Kit.Observer` | Machines.Trace |
| the discipline layer — obligations (01 §7) | `Kit.Obligation` | Contracts, Inspector, SchemaCore (the obligation view) |
| the emitter spine (01 §5: an emitter IS an interpretation) | `Kit.Emit` | SchemaCore.Emit, WasmCore.Wat, the component lane |
| the registry + replay (the spine's accumulate phase) | `Kit.Lane` (`register_lane`), `Kit.Registry`, `SchemaCore.Register` | every lane's mount; the drivers' env replay |
| the diagnostics discipline (05 §4) | `TextKit.Diag`/`Suggest` (Kit re-exports) + `Kit.CodeRegistry` (the stable E-code allocation) | every curated refusal; the persisted `notes/code-registry.txt` |
| the artifact/byte-tie machinery | `Kit.Emit` (header/content-hash), `Kit.Text` (the structure carrier) | every writer exe; the gen-check + artifact-headers gates |
| the duel/differential evidence (03 §3) | `Kit.Duel` | WasmCore.Duel, SchemaCore.Emit.Journal, the Rust crates' tests |
| the hyperproperty substrate (16 §4.3) | `Kit.Hyper` | the security-lane consumers |
| the proof ladder (01 §7) | `Kit.Obligation` (Tier + Evidence) + `LintKit.AxiomAllowlist` + `Gates.NativePolicy` | the axiom sweep; the grandfathered `native_decide` set |

## 3. The data flow (the spine)

Registry → interpretation → artifact, then the gates read. The
accumulate phase is the lanes' env extensions (`Kit.Lane` +
`SchemaCore.Register`); the read phase is a fold over the replayed
registry (`Kit.Emit`'s driver fold). Writers and readers:

### The writers (one writer per artifact path — `just gen`, `just wasmgen`, `just componentgen`, `scaffoldgen`)

| Artifact (committed) | Emitter (the ONE writer) | Contents |
|---|---|---|
| `gen/schema-slice.wit` | `SchemaCore.Emit` → `Wit`'s renderer | the schema slice's WIT world |
| `crates/schema-generated/src/lib.rs` + `tests/differential.rs` | the Rust emitter (via `SchemaCore.Derive`) | the generated Rust crate (the only hand file is its `Cargo.toml`) |
| `notes/universe.snapshot` | `SchemaCore.Snapshot` | the universe baseline (snapshot-check + breaking read it) |
| `gen/wasm-slice.wat`, `gen/wasm-slice.wasm` + `.hdr` | `WasmCore.Slice`'s `wasmSliceEmitter` (validator at generation; invalid refuses loudly, nothing written) | the binary lane's text + bytes + sidecar |
| `gen/component-slice.{wit,wasm}` + `.hdr`, `gen/component-string-slice.*` | `componentgen` (`Guest.Gen.mandate`'s registered surface — manifest-driven, never a hand list; the skew check at generation) | the component lane's world text + bytes |
| `gen/wasm-duel/*` (`.wasm` + `.hdr` + `manifest.txt`) | `WasmCore.Duel`'s emitter | the execution-duel vector set |
| `DemoApp.*` / `LedgerApp.*` generated modules | `scaffoldgen` over `Scaffold.Specs.adoptedSpecs` (seeds each hand-owned `Flow.lean` ONCE, never overwrites) | the adopted app skeletons |
| `notes/axiom-report.md`, `notes/coverage-matrix.md`, `notes/elab-baseline.tsv`, `notes/code-registry.txt` | the gates' `--write` modes (the deliberate, loud re-baseline) | the gate baselines |

### The readers (the gates — `Gates.gateNames`, the closed 14-row run order)

| Gate | Reads | Law |
|---|---|---|
| `packages-check` | the gate table × the lakefile | agreement both directions; a landed library without its row fails CI |
| `axioms` | every gated root's decls (kernel CollectAxioms) | the allowlist (`LintKit.AxiomAllowlist`); baseline `notes/axiom-report.md` |
| `docs-check` | every ```` ```lean ```` fence in `notes/*.md` (+ one subdir level) | non-sketch fences' decl names resolve in the gated envs; the header gate-row honesty scan |
| `gen-check` | the committed artifacts vs a fresh regen | the byte-tie (the volatile header exempt) |
| `code-registry-check` | `notes/code-registry.txt` | well-formedness + the allocation replay + self-stability |
| `snapshot-check` | `notes/universe.snapshot` | the committed baseline vs the fresh canonical render |
| `audit` | every committed generated artifact | no TODO/FIXME/`unwrap(`/`dbg!`/unsafe |
| `artifact-headers` | the same surface | the 2-line GENERATED header's presence + shape (the one-writer rule's detection face) |
| `native-policy` | the committed allowlist set | the `native_decide` grandfathering + staleness ratchet |
| `coverage` | the closed `Ty` × the emitter set | the probe-differential matrix; baseline `notes/coverage-matrix.md` |
| `kernel-check` | every gated module | the lean4lean pure-kernel replay (the independent double-check; one invocation per module, RSS-bounded pools) |
| `ownership` | the declared vs actual artifact ownership | D15: agreement both directions + cross-emitter disjointness |
| `breaking` | the snapshot vs the replayed registry | the three-way verdict; unremedied = exit 2 |
| `elab-watch` | every gated root's elaboration re-timing | the module/reference ratio vs `notes/elab-baseline.tsv`; a >2× delta flags |

`gates all` runs every row at bounded parallelism with the RSS
admission (the measured per-lane footprints; over budget a gate
queues — never dropped); the failures collect, the ordered report is
the registry's run order. The fast tier (`just check`) runs the light
rows + lint; the heavy three (axioms, coverage, kernel-check) stay in
`just gates`. `just impacted` narrows to the change set (conservatively
widening to full until the artifact ledger lands).

## 4. The language/tooling surfaces

| Surface | What | Boundary |
|---|---|---|
| Lean libraries (`[[lean_lib]]` rows in `lakefile.toml`) | the cone-ordered set of §1 — the single source of the model + the proofs | cone rule: C0/C1 stay mathlib-free; the cone table is discipline, the lakefile is build shape, `packages-check` holds them together |
| Lean exes | the drivers: `gates`, `lintkit`, `inspector` (readers); `schema`, `wasmgen`, `scaffoldgen`, `componentgen` (writers); the 25 test exes (`just test`'s `test_libs`) | writers are the ONLY writers of their paths (`just gen`/`wasmgen`/`componentgen` restore; a hand edit fails gen-check) |
| Rust crates (`crates/`) | `schema-generated` (the generated crate, byte-tied; hand tests consume, never re-spec), `mandate-delta` (the hand-written persistence lane — byte-exact port of `SchemaCore`'s codec; invents no format), `mandate-host` (the host consumer) | `just rust` runs the batteries; the byte-tie's consumer face — rot here is a gates failure |
| wasm components (`gen/component-*`) | the world text + component bytes + `.hdr` sidecar, emitted through the spine | the skew check at generation; the WIT view is the lossy one (the snapshot is the lossless baseline, 13-interfaces) |
| the justfile | the recipe surface: `build`, `test`, `rust`, `check`, `gates`, `impacted`, the per-gate rows, `gen`/`wasmgen`/`componentgen`, `ci` | CI runs exactly `just ci` (the local/CI parity discipline); no ad-hoc commands |
| `legacy/` | the pre-v3 mining source — read-only reference; builds run only from its own history | port content, never migrate in place (`notes/v3/14-build-map.md`) |

## 5. The reading guide

**The doctrine (why the tree is shaped this way):** `notes/v3/README.md`
→ `01-core.md` (three roots, one carrier, one spine) →
`02-data-plane.md` (the relational center) → then the file the change
touches (03–15). Every diff names its doctrine slot.

**The code (per concern, in this order):**

- *The substrate*: `kit/Kit.lean` (the umbrella IS the table of
  contents) → `Kit.Correspondence` → `Kit.Relation` → `Kit.Emit` →
  `Kit.Obligation`.
- *The spine, end to end*: `SchemaCore.Register` (`@[schema]`) →
  `SchemaCore.Emit` → `gen/schema-slice.wit` → `Gates.GenCheck` (the
  byte-tie closes the loop).
- *The binary lane*: `WasmCore.Types` → `Instr` → `OpTable` →
  `Validate` → `Encode` → `Wat` → `WasmCore.Slice` → `just wasmgen`.
- *The component lane*: `Guest.Lcnf` → `Guest.IR` → `Guest.Lower` →
  the component emission → `just componentgen`.
- *The Change root*: `Kit.Change` → `ZSet` → `Circuit`
  (`Ckt.incrementalize_ok`, the agreement theorem).
- *The TraceModel root*: `Machines.Basic` → `Trace` → `Explore` →
  `Events` → `Dsl` (the `machine!` surface).
- *Proof reuse*: `Kit.Relation` (THE generic theorem) → `Repr` →
  `Cost` → `Analysis`.
- *The discipline*: `LintKit.Cone` (the table) → `Gates.lean` (the
  registry) → the justfile (the recipes) → `notes/v3/09-gates-ops.md`.
- *The host faces*: `Inspector.lean` → `Scaffold.lean` → the adopted
  `DemoApp.*`/`LedgerApp.*` → the Rust crates' tests.

**The rule this file obeys:** to add a row, the code changes first;
this file's row points at it. A claim here that the code refutes is a
doc bug — fix the doc, or the code, and name which.

# 11 — The system as built (and the v3 target where they differ)

**STATUS: transitional** — this file describes the CURRENT tree (the
mining source for the fresh build, 14). It is retired the day the new
tree scaffolds; its successor is generated, not written (the module
tree + the gates are the new tree's own description).

What the toolkit concretely IS today: the libraries, the lanes, the
gates, the crates. This file describes the CURRENT tree and marks where
the v3 target diverges (10's phases close the gaps). Where a current
name contradicts the doctrine, the doctrine wins for new work (fix the
code, not the doc).

## 1. The build shape

ONE root lakefile (`lakefile.toml`, package `LeanRoot`) — every library
is a `[[lean_lib]]`/`[[lean_exe]]` target with `srcDir`/`roots`. The
per-package split died in the single-lake migration (the cone
duplication: N packages × the full dep cone). The cone rule survives as
DATA: the import-ban table (LintKit) — core-only libraries
(codegen-core, TextKit, TestingKit, LintKit) never import the mathlib
cone; guest-compiled modules stay core-only.

The gates run via the gates exe (`lean/gates/`): `just gates` = the
composition in the justfile (09 §3). Everything below passes it.

## 2. The Lean libraries (what each OWNS)

| Library | Owns | Cone |
|---|---|---|
| **codegen-core** | the kit: Iso/PartialIso (the graded carrier's current form), CheckedProp, Obligation (tiers/evidence/discharge backends), DataRegistry/CodedRegistry, the Emit spine (Emitter+law+runCertified, runEmitters, the JSON builder, the manglers), GenKit (freshNameCheck/didYouMeanSuffix/declare_* glue), AttrKit, the guest gate (GuestBan) | C0 |
| **TextKit** | the total parser core (Parser monad over `List Char`, scanners, the inversion-lemma kit) — re-homed out of substrait | C0 |
| **TestingKit** | PropSpec (mandatory negative controls), the LCG (deterministic seeded generation), GateKit, the harness/verdict machinery | C0 |
| **LintKit** | the env/text linter engine + the linter table (axiom allowlist, dupDefBodies incl. the upstream-dup extension, packageNamespace, noNewPartial, bareChecker, unregisteredRoundtrip, didyoumeanDiscipline, coreHasNoClaim, …) | C0 |
| **gates** | the gate driver (gen-check/axioms/native-policy/kernel-check/manifest-check/coverage/docs-check + the report-gate combinator + the audit channel) | C0, host-side |
| **Machines** | Machine (step?/run/traces), Sessions (dual-checked protocols), Convergent (decreasing variants), Rewind (ChangeInversion), the machine! macro + the states:/payload: entourage, the Fusion bridges (machines↔dbsp: journal = D∘run, dI iso, bisimulation as stream equality) | C2 (mathlib) |
| **dbsp** | ZSet (signed bags), Stream, D/I, the operators, the circuits (Ckt + the certified Ckt→Rust emitter with `incrementalize_ok` cited), replicas, determinism, the relational operators | C2 (mathlib) |
| **schema-lang** | the schema toolkit: Ty (the closed boundary universe incl. KeyTy), Item (the item model), Wf (WellFormed relation + checker bridge), the VExpr predicate layer + ExprLang interface, the codecs (Codec/CodecValue/EnumWire/WireCodec deriving), the row layer (RowVals, the record Iso deriving), the lanes (Update2, Keys, TableInvariant, Refine, PrePost, EntityMachine, Scheduling, Commands, EventSourced/Delta/Trace/Migration, Witness/WitnessCheck/WitnessSpec, Obligation, Lens (SchemaPath/CasePrism)), the Meta registration/deriving machinery, the emitters (Emit/*: WIT/Rust/typestate/machine/circuit/invariant/update/witness/snapshot/vortex), the breaking gate, the snapshot codec | C3 (app) |
| **substrait** | the query-plan wire: the Proto types, the typed expression/relation layer, the canonical text format + the decode ladder (proof-carrying parse∘emit inversions), the Grammar tables | C1 (core-only), public surface |
| **qlang** | the demo query language (compiles to substrait; retargeting onto schema-core is the plan) | C3 |
| **wasm-backend** | the guest compiler: LCNF→WAT (WasmBackend.lean, the foldImpure fold, the intrinsic table), the oracle (the row universe + verdicts + the manifest), the world generator (WasmGenMain), the bounded-Nat lowering, the guest intrinsics | C3 |
| **std** (GuestlangStd) | the guest stdlib: the intrinsic bodies, the guest demo impls | guest-compiled |
| **ledger / feature-flags / faults / edgepython / proofkit** | the dogfoods + product lanes: the event-sourced ledger; the feature-flags + templates package; the faults registry (fast-observe generation); the Python frontend; the guestlang proof utilities | C3 |
| **edgepython** | the second frontend (the multi-frontend evidence) | C3 |

## 3. The Rust crates (what each OWNS)

| Crate | Owns |
|---|---|
| **guestlang-host** | the wasmtime host: component loading, the skew fail-fast (component-type introspection vs the committed surface), the witness verification calls, the span/fault consumption, hostgen (the snapshot parser's Rust port — the differential twin), the test evidence suites |
| **guestlang-rt** | the wasmi standalone runtime (the differential-duel second engine): fuel metering, snapshot/restore, conformance |
| **wasm-delta** | the host-side persistence: the append-only delta log (byte-exact port of the Lean codec/trace/delta) + inversion |
| **oracle-runner** | the oracle CLI (replay + explain — the debug loop) |
| **forge** | the pipeline orchestrator: `forge gen` drives the emitters + the byte-tie; the OCI layout store |
| **guest-demo / splicer-mw** | the wit-bindgen fixtures |
| root crate | the demo binary (fast-observe wiring) |

Deleted in the consolidation (recoverable from jj history if a consumer
returns): wire (dead, non-wRPC), lean-sys-v433 + lean-ffi (unwired),
forge's push/pull lane, the guestlang-rt pool lane.

## 4. The lanes (schema-lang's working surface)

The registration/derivation surface: `@[schema]` (records/variants/funcs/
resources — the attributes register items in the env extensions),
`schema_keys`, `schema_invariant`, `schema_update` (v2), `@[event_sourced]`,
`schema_entity_machine`, `schema_template`, `deriving WireCodec`, the
row-bridge deriving, `declare_enum_wire`, `register_check_attribute`.

Every lane's shape (the recipe): the registry extension (append-only,
the compile-time event log) → the derived surface (the GenKit/family!
machinery) → the obligation rows (tiers computed, evidence closed) →
the emitter rows (folds; byte-tied artifacts) → the tests (folds over
the lane's data with mandatory negative controls) → the duel rows where
semantics ride.

## 5. The gates' current composition

`lean-build · lean-proof-roots · gen-check · artifact-headers ·
wit-check · lean-axioms · native-policy · kernel-check · manifest-check
· coverage · docs-check · check-schema · breaking · wasm-diff-check ·
budget-check · splice-smoke · rt-conformance · lean-lint` — the details
live in the justfile; each row's contract in 09 + the gates exe's own
headers.

## 6. The current divergence from the v3 target (the honest list)

- The kit's correspondence is the two-constructor form (Iso/PartialIso);
  the GRADED library (01 §4) is Phase 2's work.
- The relational data plane (02) is partially present (keys, table
  invariants, Z-sets) — the valid-worlds re-centering + weighted
  relations + FD-driven APIs are Phase 1-2.
- The TraceModel (01 §3) is v2-doctrine; the transition-authoritative
  correction (review 1 §3) lands with Phase 8.
- The bidirectional discipline (03) is partially landed (the skew check,
  the witness lane, hostgen); the propose→check→commit adapter and the
  complement lens are Phase 1.
- TextKit is the parser core only (03 §1's typed bidirectional grammar
  layer is Phase 4).
- The gates' baseline gates (axiom report, coverage matrix, artifact
  manifest) exist; the negative-dependency correction to the demand-set
  is Phase 11.

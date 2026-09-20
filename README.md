# lean-rust-wasm — the guestlang template

## The pitch

You write two Lean modules and nothing else:

- **A spec module**: plain `@[schema]` records and variants,
  `@[schema_fn]` function signatures, `@[schema_resource]` handles — see
  [lean/schema-lang/Demo.lean](lean/schema-lang/Demo.lean). Wrong field types
  and misspelled references fail at elaboration, not at runtime.
- **An impl module**: the function bodies, marked `@[guest]`/`@[guest_std]`
  so the elaborator rejects any host-only runtime (IO, tasks, thunks) on the
  compiled-to-wasm surface.

You get free, because the layers supply them:

- **Proved schemas** — the spec of record is kernel-checked Lean; the
  registry reflects it; no hand-maintained type list survives.
- **Byte-tied codegen** — pure emitters fold the registry into WIT worlds,
  Rust types, Vortex dtypes, fault registries; every artifact is committed
  and drift fails CI (`just gen-check`).
- **The dual-engine differential duel** — Lean's own `resultOf` evals are
  the oracle; the shipped wasm replays the manifest under wasmtime *and*
  wasmi, with a sabotage control that must fail.
- **WASIp3 components** — async functions, streams, resources at the WIT
  boundary; wit-bindgen and wasm-tools validate what we emit.
- **Observability as spec data** — spans and fields are schema items; the
  host's call path is span-manifest-governed.
- **The breaking gate** — schema evolution is diffed against a committed
  snapshot; breaking changes fail unless a registered migration remediates.
- **CI that means it** — `just gates`: axiom check (zero `sorry`), byte-tie,
  wit-parser round-trip, differential replay, lint, compat diff, all green
  or the build fails.

The machinery — harnesses, gates, emitters, proofs — is inherited from the
packages below. `just new-project my-thing` instantiates all of it.

## 30-second quickstart

Prerequisites: [Nix](https://nixos.org) with
[devenv](https://devenv.sh), and [elan](https://lean-lang.org/lean4/doc/setup/)
(the toolchain is pinned at Lean 4.33.0). Then:

```sh
git clone <this-repo> && cd lean-rust-wasm
devenv shell --profile wasm     # wasm toolchain + wasip3 guest linking
just new-project my-thing       # scaffold lean/my-thing from template/
```

The loop:

```sh
# edit lean/my-thing/MyThing.lean (spec) and MyThingFn.lean (bodies)
just gen            # regenerate every artifact from the spec
just wasm-compile   # LCNF → WAT → component; regenerates the oracle manifest
just gates          # the full lean↔rust drift check, one shot
```

`new-project` auto-registers the package in the gate loops and prints the
manual follow-ups (the WIT world's fold, the gen driver, the lint row).
The recipe self-verifies via `just scaffold-test`. Details:
[notes/reuse-map.md](notes/reuse-map.md).

Docs: the Starlight site under [docs-site/](docs-site/) (the 30-second
quickstart as a guide page, plus the generated API reference);
`just docs` regenerates and builds it.

## The proof story — three tiers, honestly labeled

The template's claim is *tiered*, and the tiers mean different things:

**PROVED** — kernel-checked theorems, zero `sorry`/`axiom` (`just lean-axioms`
enforces; the allowed set is the core triple plus disclosed `native_decide`):

| Claim | Where |
|---|---|
| The canonical-ABI flat record layout has no field overlap | `lean/wasm-backend` — `WasmBackend/Layout.lean` (`go_pairwise`) |
| The emitted WAT fragment is type-safe (well-typed programs never stack-underflow) | `lean/wasm-backend` — `WasmBackend/Sem.lean` (`exec_typed`) |
| Delta application is the group sum; two replicas converge; batch order is irrelevant | `lean/dbsp` — `Dbsp/Replicas.lean` |
| Protocol session duality | `lean/Machines` — `Machines/Session.lean` |
| decode ∘ emit round-trip inversions (the substrait text surface) | `lean/substrait` — `Substrait/Decode.lean` |
| Schema nullability lowers correctly to Vortex dtypes | `lean/schema-lang` — `SchemaLang/Vortex/Lower.lean` |
| The pipeline stage machine is acyclic; the oracle ⊆ the WIT world | `lean/schema-lang` — `SchemaLang/Pipeline.lean`, the registry fold |

**TESTED** — empirically total, not proven:

| Claim | Where |
|---|---|
| The compiled wasm agrees with Lean's semantics (the duel: 440-row manifest, Lean evals → JSON → replay under wasmtime + wasmi; sabotaged rows must fail) | `just wasm-compile`, `just rt-conformance`, `guestlang-host`'s `wasm_diff` |
| Every differential gate catches its own corruption (DiffSpec negative controls; a vacuous suite fails) | `lean/TestKit` — `TestKit.DiffSpec`/`PropSpec` |

**CHECKED** — mechanical identity or acceptance, not semantics:

- The byte-tie: `just gen-check` regenerates in memory and byte-diffs every
  committed artifact (sha256-verified OCI store). Identity is not correctness.
- The WIT round-trip: the canonical parser (wit-parser) must accept what our
  emitters print — it, not our printer, is the acceptance authority.
- The lint gate: `just lean-lint` (env-linters over each package's oleans).

**The honest boundary**: the engines' instruction semantics agreeing with
Lean's is EMPIRICAL (the duel), not proven. Closing that gap — a Lean model
of the emitted-WAT fragment plus a translation-correctness theorem — is the
**Talos line**, the project's open frontier
([notes/full-remaining-work.md](notes/full-remaining-work.md)). We do not
claim it.

## Architecture

```
        ┌─────────────────────────────────────────────────┐
        │ YOUR SPEC (Lean, kernel-checked)                │
        │ @[schema] records/variants  @[schema_fn] sigs   │
        │ @[guest] impl bodies (runtime-banned at elab)   │
        └───────────────────────┬─────────────────────────┘
                                │ reflection at elaboration
                                ▼
        ┌─────────────────────────────────────────────────┐
        │ REGISTRY (env extension; importModules replays) │
        └───────────────────────┬─────────────────────────┘
                                │ pure emitters: List Item → List GeneratedFile
     ┌──────────┬───────────────┼──────────────────┬───────────────┐
     ▼          ▼               ▼                  ▼               ▼
   WIT world  Rust types   Vortex dtypes    fault registry   observe spans
     └──────────┴───────────────┴──────────────────┴───────────────┘
                                │
                                ▼
        ┌─────────────────────────────────────────────────┐
        │ forge (Rust driver): writes artifacts, byte-tie │
        │ (`gen --check`), OCI artifact store, provenance │
        └───────────────────────┬─────────────────────────┘
                                ▼
        ┌─────────────────────────────────────────────────┐
        │ guest component (wasm32-wasip3; wasm-tools lift)│
        │ crates/wire = the transport layer between comps │
        └──────────┬───────────────────────────┬──────────┘
                   ▼                           ▼
        wasmtime host (guestlang-host)   wasmi standalone rt
        typed bindings, generated    (guestlang-rt): same
        faults, delta impls,         demo.wasm, same manifest
        wasi 0.3 async               — the dual-engine duel:
                   ▲                 Lean evals are the oracle
                   └──────────────────────────┘
```

## Repo map

Rust crates (`crates/`):

| Crate | What |
|---|---|
| `forge` | codegen orchestrator: drives lake emitters, byte-tie, OCI store, component linking |
| `guestlang-host` | the wasmtime host: typed bindings from the generated WIT, delta tests, the differential gate |
| `guestlang-rt` | the standalone embeddable runtime (wasmi): deterministic profile enforced at load |
| `guest-demo` | the demo guest component (the template's dogfood target) |
| `splicer-mw` | the first real middleware: an in-wasm counter interposer composed via wac |
| `wire` | transport adapter layer (noq/Quinn first) |

Lean packages (`lean/`, downstream imports upstream, never the reverse —
[notes/lean-doctrine.md](notes/lean-doctrine.md)):

| Package | What |
|---|---|
| `LintKit` | env/text linters (axiom allowlist, package namespaces, …) |
| `TestKit` | the test/gate harness: golden byte-tie, property sweeps with mandatory negative controls, corruption gates |
| `codegen-core` | emitter framework, certified (proof-carrying) emission, the registry machinery |
| `Machines` | guarded state machines, refinement, session types with proved duality |
| `substrait` | the query-expression surface: proved decode∘emit inversions, the schema-indexed GADT |
| `schema-lang` | the schema layer: the closed `Ty` universe, attributes, WIT/Rust/Vortex emitters, compat diff, migrations, codecs |
| `faults` | the error registry: host+guest faults resolved from ONE registry |
| `dbsp` | delta theory: Z-sets, the replica-convergence proofs, ChangeSpec |
| `std` | the guest-impl surface (`GuestlangStd`, guest-legal string ops) |
| `wasm-backend` | the compiler line: LCNF → WAT → wasm; proved layout, stack typing, the oracle |
| `ledger` | the dogfood project — a scaffold instance, not a library |

## Status

**Production-shaped:**

- All Lean packages axiom-clean; `just gates` is the full drift matrix and
  runs green.
- 13 byte-tied artifacts, one writer per path, audited (`pathsUnique`,
  `jobsCoverEmitters`).
- The provenance gate: `forge pull` refuses artifacts whose axiom-report
  annotation is absent or `unchecked`.
- The deterministic wasmi profile enforced at load (a hand-encoded f64
  module is refused; the feature set mirrors the closed `Ty` universe).

**Demo-stage — the honest list:**

- The demo world is 13 exports in one gateway world; a new project wires
  its own world fold by hand (4 manual follow-ups after `new-project`).
- The `@[invariant]` validators lane is designed, not built: validators are
  scalar-first; the record-param adapter (the inverse element lowering) is
  the remaining ABI piece.
- The general codegen path's layout proofs and the walk's region
  disjointness are the same shapes as the proved cases but not yet
  discharged ([notes/seam-contract.md](notes/seam-contract.md)).
- The engine-semantics gap is empirical-only (the Talos line above).
- Publishing is deferred until APIs stabilize.

Pre-alpha. Decisions live in [notes/](notes/), one file per decision, with
rejected alternatives and failure evidence.

# design-bolero-integration — bolero as the Rust-side exploration lane

- Status: DESIGN (v1). Implementation not started beyond the adoption
  wave's first two target files (see §8).
- Provenance: every bolero claim below was verified against a fresh
  clone of `camshaft/bolero` at v0.13.4 (the version our Cargo.toml
  pins: `bolero = "0.13"`; the registry cache holds bolero-0.13.4) —
  clone at /tmp/bolero, file/line citations inline. Every tree path
  cited was checked to exist.
- Owner directive: "fuzzing generated for arbitrary + bolero wherever
  additive". This doc is the design for the bolero half; the generated-
  `arbitrary` half already exists (`src/gen_generated.rs`, the
  `arbitrary` feature lane).
- Composition with the adoption wave (landed while this doc was
  written): `crates/wasm-delta/tests/fuzz_decode.rs` and
  `crates/guestlang-host/tests/fuzz_hostgen.rs` are the first two instances
  of the harness shape in §5. This doc does not duplicate them; it
  names them as the pattern and fills the pieces they don't cover
  (engines beyond the test engine, Kani, emitter extension, corpus
  law, negative controls).

---

## 1. The engine matrix — what runs where

bolero's engine selection is a compile-time cfg chain
(`lib/bolero/src/lib.rs:12-27`): `fuzzing_libfuzzer` → LibFuzzerEngine,
`fuzzing_afl` → AflEngine, `fuzzing_honggfuzz` → HonggfuzzEngine,
`kani` → KaniEngine, else **TestEngine** (the default under plain
`cargo test`).

| Engine | Deps | Toolchain | Runs for us |
|---|---|---|---|
| **TestEngine** (default) | none — pure Rust, `cargo test` | stable OR nightly | everywhere: every dev run, CI, nextest |
| **libfuzzer** (cargo-bolero default for campaigns) | `cargo-bolero` binary; Linux needs `binutils-dev`/`libunwind-dev` or nix `libbfd libunwind libopcodes` (book/cli-installation.md) | nightly for sanitizer coverage (book/rust-stable.md); `--sanitizer NONE` works on stable | on-demand local (`just fuzz`); we have nightly (the `-Z build-std` wasm lane proves it) |
| **afl** | AFL system tool + afl.rs | nightly | skip — redundant with libfuzzer for us |
| **honggfuzz** | system honggfuzz | nightly | skip |
| **kani** | `cargo kani` (downloads its own verification toolchain; network install, Linux x86_64) | its own | on-demand only (§2) |
| **miri** | rustup miri | nightly | optional; book/features/miri.md (isolation must be off to read corpora) |

**TestEngine semantics** (verified `lib/bolero/src/test/mod.rs` +
`lib/bolero-engine/src/rng.rs`): each run = (a) seeded inputs from
`BOLERO_RANDOM_SEED` if set, (b) every file under the target's
`corpus/` and `crashes/` dirs (see §6), (c) N RNG iterations. `N` comes
from `with_iterations(n)` in the harness or `BOLERO_RANDOM_ITERATIONS`;
without it the bound is **time** (1 s default, `BOLERO_RANDOM_TEST_TIME_MS`).
`BOLERO_RANDOM_MAX_LEN` caps input size (default 4096). A failure prints
`[BOLERO_RANDOM_SEED=<n>]`; re-running with that env var replays the
exact case. This is the deterministic, offline, CI-safe lane — it is
what the adoption wave's targets use (`with_iterations(512)` /
`(256)`).

**The `cargo bolero` CLI** (bin/cargo-bolero/src/main.rs) has exactly
five commands: `test`, `reduce`, `new`, `list`, `build-clusterfuzz`.
There is **no `run` command** (removed in 0.6.0; CHANGELOG: "`cargo
bolero fuzz` deprecated in favor of `cargo bolero test`").

- Correction: the justfile's `fuzz name` recipe says `cargo bolero run
  {{name}}` — verified against v0.13 source, `run` does not exist; the
  recipe is stale. Fix: `cargo bolero test {{name}}` (§9, D4).
- `cargo-bolero` is not installed on this box (no ~/.cargo/bin, not in
  devenv.nix) — W-B1 installs it; until then only the plain-`cargo
  test` lane runs.

**Where each lane runs:**
- CI (`.github/workflows/ci.yml`): the lean-floor job + the rust/wasm
  lane (`just gates` + nextest). The TestEngine lane rides `just test`
  for free — fixed iterations, deterministic, no new deps. No campaigns
  in CI (slow, coverage-guided, nondeterministic-by-design).
- Local on-demand: `just fuzz <target>` = a bounded libfuzzer campaign
  (minutes), corpora in gitignored scratch, crashes promoted (§6).
- Kani: local on-demand, separate install, never in the gates (§2).

## 2. Kani — the honest v1 scope

**What Kani proves** (book/features/unified-interface.md, Kani section):
memory safety, absence of panics, absence of index-out-of-bounds,
absence of arithmetic overflows, and custom assertions — by symbolic
execution (CBMC-backed) over **proof harnesses**, exhaustive over the
bounded input space rather than sampled. That is a different
quantity than bolero's TestEngine lane (sampling) or a libfuzzer
campaign (coverage-guided sampling): Kani gives *absence*, bolero gives
*finds*.

**Candidates in our tree** (rule: pure, unsafe-free, loop-bounded code
only):
- `crates/wasm-delta/src/` — `#![forbid(unsafe_code)]` (lib.rs:33);
  `codec.rs`/`row.rs`/`value.rs` are the byte-level decode primitives
  (varint/u64/length-prefixed reads, slice indexing). **Best v1
  candidate**: never-panic, no-overflow, no-OOB over the primitive
  decoders.
- `crates/guestlang-host/src/hostgen.rs` — the snapshot parser (pure, the
  fuzz_hostgen target's subject). Kani-able in principle for the
  *tokenizer*; the whole-parser proof is likely too big (§2 cost).
- `src/schema_generated.rs` and the other `*_generated.rs` types — pure
  data, trivially in-scope where a harness touches them.
- NOT Kani-able: `crates/guestlang-host/src/engine.rs`/`runtime.rs`/
  `bindings.rs`/`valves.rs` (wasmtime/wasmi glue, IO, threads),
  `crates/guestlang-rt` pool/engine (filesystem, threads, wasmi
  internals), anything touching `std::fs`/network/wall-clock. Kani
  models neither real IO nor the wasmtime runtime.

**Cost (observed from the source + docs, to be measured in W-B6):**
- Install: `cargo kani` download + `kani setup` — a network operation
  and a pinned toolchain; NOT offline-friendly. One-time per box; not
  in CI v1.
- Runtime: CBMC-style symbolic execution is exponential in loop
  iterations and string/heap operations. Our honest v1 harnesses are
  the *bounded primitives* (`codec.rs` decode fns with bounded
  lengths — `kani::unroll`/bounds where needed), not `open_with` over
  a whole arbitrary journal and not the whitespace-text snapshot
  parser's full grammar. The panic-freedom of the *composition* stays
  with bolero's sampling lane; Kani pins the primitives.
- Harness discipline: `#[cfg_attr(kani, kani::proof)]` on the harness
  test (book Kani section) so one harness source serves both engines
  (`cargo kani --tests --harness <name>` is exactly what cargo-bolero's
  kani engine shells out to — bin/cargo-bolero/src/kani.rs:9-11).
  bolero-kani also emits `kani::cover!(was_valid, "the generator
  should produce at least one valid value")` — satisfiability of the
  generator is checked, with the caveat (their own TODO in
  lib/bolero-kani/src/lib.rs) that an unsatisfiable generator does not
  yet fail the harness. Our vacuity guard (§7) covers that gap.

**v1 Kani scope, one sentence:** prove the `wasm-delta` codec
primitives (and, if budget allows, hostgen's tokenizer) are
panic/overflow/OOB-free over ALL inputs up to a stated bound; everything
else stays bolero's business.

## 3. The generated-TypeGenerator story (emitter extension)

Current state (verified):
- `src/schema_generated.rs` — the Lean emitter
  (`lean/schema-lang/SchemaLang/Emit/Rust.lean`) generates the schema
  records with `#[derive(Clone, Debug, PartialEq[, Eq])]`, no generator.
- `src/gen_generated.rs` (`Emit/GenRust.lean`, feature `arbitrary`) —
  Lean-authored generators over `arbitrary::Unstructured`,
  budget-threaded, collision-pooled. Consumed by bolero via the
  `arbitrary` feature (`check!().with_arbitrary::<T>()`; guestlang-rt's
  `tests/module_bytes/main.rs` is the landed instance of that shape).
- bolero-generator-derive (v0.13.4, verified): `#[derive(TypeGenerator)]`
  works on structs/enums/unions, auto-bounds generics
  (`T: TypeGenerator`), and supports a per-field
  `#[generator(<expr>)]` attribute where `<expr>` is any
  `ValueGenerator` (generator_attr.rs: `attr.path().is_ident("generator")`,
  expression passed through verbatim; also the `#[generator(_code =
  "...")]` escape hatch).

**Bounds ARE supported** (verified `lib/bolero-generator/src/range.rs`
+ `bounded.rs`): `core::ops::Range`/`RangeInclusive`/`RangeFrom` over
any `BoundedValue` type are `ValueGenerator`s. So `#[generator(0u32..
=100)]` on a field, or `check!().with_generator((0..100u64, 10..50))`,
is real bolero API — the book's own example (lib.rs doc comment:
"one being between 0 and 100"). Our schema's ranged refinements
(`u32 0..100` — `lean/schema-lang/SchemaLang/Refine.lean`, "ranged
refinements: NUMERIC type + a range constraint") map directly onto
inclusive ranges. This is the verification the design needed: **no
bolero feature is missing for ranges**.

**Design — two lanes, both additive (decision D3):**

- **Lane A (v1, no emitter change):** bolero targets consume the
  EXISTING generated types via `with_arbitrary::<T>()` (the
  `arbitrary`-feature lane) and raw bytes via `.for_each(|input: &[u8]|)`
  for parsers/codecs. This is what the landed targets do. The
  Lean-authored `gen_generated.rs` generators remain the ORACLE
  generator (they produce oracle vectors for the differential, §4);
  they are not re-fuzzed against themselves.
- **Lane B (v2, W-B5):** the Rust emitter gains a `TypeGenerator`
  emission mode: `#[cfg_attr(feature = "fuzz",
  derive(bolero::generator::TypeGenerator))]` on generated structs/
  enums, and — where the spec carries a range refinement —
  `#[cfg_attr(feature = "fuzz", generator(<start>..=<end>))]` on the
  field. Details that matter:
  - The `cfg_attr` wrapper is mandatory: `generator` is a derive
    *helper attribute* registered by the derive; with the derive
    cfg'd out the bare attribute would be an unknown-attribute error.
    Gate the whole thing on a new root-crate feature `fuzz =
    ["dep:bolero"]` (`bolero` optional) so production builds carry no
    bolero dep — same shape as the existing `arbitrary` gate.
  - The derive emits structure-aware *mutate* as well as generate
    (derive lib.rs: `mutate_method`) — that is the payoff over
    `Unstructured`: under a libfuzzer campaign, mutations preserve
    structure instead of re-drawing from scratch.
  - Byte-tie law: this is a GENERATED-file change — the emitter is the
    only writer, regen lands as a reviewed diff, `just gen-check`
    binds it. No hand-editing of `schema_generated.rs`.
  - One-writer rule: the emission belongs in `Emit/Rust.lean` (the
    artifact's existing writer) — a new artifact path would need a new
    Registry row and emitter, which is not worth it for an attribute
    on an existing file.
- The division of labor stays: **Lean PropSpec = proving lane** (the
  seeded, shrinking, negative-controlled properties over the spec's
  semantics — `lean/TestingKit/TestingKit/PropSpec.lean`), **bolero = Rust
  exploration lane** (never-panic floors + differential oracles over
  the Rust twin), **Kani = bounded proof lane over Rust primitives**.
  Nothing moves between lanes without a note in this doc.

## 4. The oracle pattern — standard harness shape

Our differential discipline: Lean computes the expectation, Rust
replays it. bolero's `check!().for_each(closure)` is the exploration
wrapper. The standard per-surface harness has three targets, in
increasing strength; targets 1-2 are the floor for every surface,
target 3 where a Lean oracle exists:

1. **ARBITRARY FLOOR** — any input; the surface must never panic and
   must produce Ok-or-structured-Err (enumerate the allowed error
   variants explicitly, as `fuzz_decode.rs:assert_open_contract` does).
2. **VALID-THEN-MUTATED** — a genuinely valid input built through the
   REAL writer path, then one seeded random edit (flip/delete/truncate);
   the contract is "Ok with invariants kept, or structured Err; never
   invents structure". `fuzz_decode.rs` target 2 and `fuzz_hostgen.rs`
   target 2 are the landed instances.
3. **FIXTURE-DIFFERENTIAL (Lean-seeded)** — the corpus of each
   campaign-iteration is seeded with Lean-generated vectors (the
   `snapshot-fixtures` pairs; the oracle manifest `diff.json`). The
   bolero closure checks the Rust result against the Lean expectation
   carried in the vector, not just against self-consistency.
   `fuzz_hostgen.rs` target 2 is the partial instance (unmutated snap
   parsing Ok IS the Lean expectation; exact dump equality stays in
   `snapshot_differential.rs`).

Per surface, the mapping:
- **codec** (`wasm-delta::codec`): targets 1+2 landed; Kani harness
  W-B6 adds the bounded proof.
- **parsers** (`hostgen`, WIT fixture sweep): target 1+2 landed
  (`fuzz_hostgen.rs`); target 3 = feed `snapshot_fixtures.txt` pairs
  as campaign seeds.
- **delta log** (`DeltaLog::open_with`): targets 1+2 landed in
  `fuzz_decode.rs`; target 3 would seed campaigns with
  Lean-replay-derived journals when a Lean journal writer exists.
- **generated records** (schema types): Lane A `with_arbitrary` for
  round-trip surfaces (write→read == identity, the Rust twin of the
  Lean RoundTripSpec); Lane B TypeGenerator under campaigns later.

Replay law (already the landed discipline, keep it): every randomness
inside the closure (mutation schedules, fixture choice) is a pure
function of the input bytes via the file-local `Lcg` — the printed
seed reconstructs everything. No `rand::thread_rng` inside a closure.

## 5. Corpus + byte-tie discipline

Verified mechanics: under plain `cargo test`, TestEngine replays every
file in the target's `work_dir()/corpus` and `work_dir()/crashes`
(`lib/bolero/src/test/mod.rs`, `tests()`) before the RNG iterations.
For harnessed (dir-layout) targets, `work_dir()` =
`tests/<target>/__fuzz__/<test_name>/` (bolero-engine
target_location.rs:119-135). cargo-bolero's `new` even drops a
`corpus/.gitkeep` there and the book says "committed or S3".

Our law overrides the book's default suggestion:

- **Corpora are coverage exhaust, not evidence — NOT committed.**
  `tests/*/__fuzz__/` is gitignored wholesale (W-B4), with scratch
  campaign state living in devenv state (`DEVENV_STATE/bolero-corpus`,
  per the existing justfile comment) where corpus_dir is redirected.
- **Crash artifacts ARE evidence — committed.** A crash file in
  `crashes/` is (a) auto-replayed by every subsequent `cargo test` run
  (the mechanism above — a crash can never regress silently), and (b)
  promoted into the appropriate fixtures file when it deserves a name
  and a Lean-side twin. Crash files are raw bytes (no comment header
  possible), so each committed crash gets a one-line ledger row in this
  doc's §10 or the relevant test file's header naming what it caught.
- **Seeds deterministic, always:** `with_iterations` pinned per target
  (no time-bounded runs in committed code — a time bound is not
  reproducible), `BOLERO_RANDOM_SEED` for reproduction, the closure
  pure in its input.
- CI runs zero campaigns: the CI lane's value is the auto-replay of
  committed crashes + fixed-iteration exploration. Campaigns are a
  local/nightly-box activity (`just fuzz`), and their findings enter
  the tree only as crash artifacts or fixtures.

## 6. Negative controls — translating PropSpec's mandate

**Observed:** bolero has no `should_panic`-style negative control, no
"this harness must be able to fail" notion, and (per bolero-kani's own
TODO) even its Kani satisfiability check does not fail on a vacuous
generator. Nothing in bolero enforces our PropSpec rule ("a vacuous
suite fails the gate").

**Inferred:** the mandate must be carried by OUR harness discipline,
not by the dependency.

**Design — the negative control as a sibling test in the same file
(the TestingKit shape, in Rust):** every fuzz file ships a
`negative_control` test that runs the SAME checker machinery against a
deliberately-sabotaged subject and REQUIRES the violation to be caught.
Two concrete forms, both verified writable against the API:

- **Checker-discrimination control** (for Ok-or-structured-Err
  contracts): the property's contract lives in a pure
  `fn assert_contract(result: ...) -> ()` (panic-based, the Rust norm).
  The control hand-builds a value that VIOLATES the contract by
  construction (e.g., a decoded result naming an unregistered table —
  the exact case `assert_open_contract` rejects), wraps the call in
  `std::panic::catch_unwind`, and asserts the panic HAPPENED. If the
  contract check is ever loosened to trivially-true, the control goes
  red: "control NOT caught — the fuzz layer proves nothing". The
  outer `catch_unwind` is what keeps bolero's own panic hook from
  turning the control into a target failure — bolero's engine catches
  escaping panics (bolero-engine/src/panic.rs) and fails the test; the
  control must *contain* the sabotage instead.
- **Sabotage-stub control** (for never-panic floors): run the harness
  machinery over a deliberately-panicking twin of the subject (a stub
  decoder that panics on the first malformed byte) for 1 fixed-seed
  iteration, catch inside the closure, require the catch. This proves
  the harness path (engine → driver → closure) actually executes the
  subject — the counterpart of a stubbed `propSuite` in PropSpec.

Plus the two runtime anti-vacuity measures the adoption wave already
landed and this doc ratifies as standard:
- the **iteration counter guard** (`ran >= ITERATIONS`, in both landed
  files) — proves the target RAN;
- Kani's `was_valid` cover (§2) — noted, not relied on.

And the heavyweight backstop already in our culture: `just
mutation-proof` (justfile) is the mutation battery for the Lean gates;
W-B3 adds one fuzz-gate mutation to it (delete a committed crash file
or neutralize a contract assert → the gate must go red).

## 7. Verification gates (per the AGENTS.md runbook)

Rust side: `just test` (nextest — the TestEngine lane runs inside
nextest; the landed targets' `with_iterations` makes them
time-bounded-safe under nextest's per-test supervision), `just clippy`,
and — for emitter changes — `just gen-check` + `just gates`. Lean side
untouched by this design except W-B5 (emitter). Kani and campaigns are
NOT gates; they are on-demand (`just fuzz`, `cargo kani`), with
findings entering the tree only as artifacts (§5).

## 8. Relation to the adoption wave (composition, not duplication)

Landed by the bolero-adoption agent while this doc was written (read
and verified):
- `crates/wasm-delta/tests/fuzz_decode.rs` — decoder floor +
  valid-then-mutated, 512 iterations, Lcg-from-input, vacuity guard.
- `crates/guestlang-host/tests/fuzz_hostgen.rs` — parser floor +
  fixture-differential, 256 iterations, same discipline.
These are instances of §4/§6 and are NOT re-specified here. The doc's
additive contributions: engine matrix + `just fuzz` repair (W-B1),
corpus law (W-B4), negative-control standardization (W-B3),
TypeGenerator emission (W-B5), Kani (W-B6).

## 9. W-orders (dependency-ordered, prescriptive)

**W-B1 — Repair `just fuzz` + install cargo-bolero.**
- Change the recipe to `cargo bolero test {{name}}` (verified: no
  `run` subcommand in v0.13). Install cargo-bolero with the nix lib
  set: `nix-shell -p libbfd libunwind libopcodes` equivalent, or
  `cargo install cargo-bolero --no-default-features` (book: relaxes
  the libunwind/binutils requirement).
- Gate: `cargo bolero list` enumerates the dir-layout targets
  (`module_bytes`, `snapshot_restore_seq` in guestlang-rt — the only
  two `tests/<name>/main.rs` targets in the tree); one 1-minute
  `--sanitizer NONE --engine libfuzzer` campaign runs clean.

**W-B2 — CI carries the TestEngine lane.**
- Verify `just test` (nextest) picks up `fuzz_decode.rs` +
  `fuzz_hostgen.rs` in the rust/wasm lane; nothing new to write, only
  to confirm (they are plain `#[test]`s). If nextest's env strips
  `BOLERO_RANDOM_SEED` reproduction, document the reproduction
  procedure in each file's header.
- Gate: CI green with the fuzz files included; a deliberately seeded
  failure replays via `BOLERO_RANDOM_SEED` (one manual check).

**W-B3 — Negative controls standardized (§6).**
- Every fuzz file gains `negative_control` (checker-discrimination
  form; sabotage-stub where there is no structured error to hand-build)
  + the header text "the control is the PropSpec mandate's Rust twin".
- Gate: the control test passes; neutralizing the contract assert in a
  scratch build turns the control red (verified once, by hand).
- Extends `just mutation-proof` with one fuzz mutation (W-order for a
  later cycle, not blocking).

**W-B4 — Corpus law (§5).**
- `.gitignore`: `**/tests/**/__fuzz__/` with a `!`-unignore for
  `crashes/` dirs (or invert: ignore everything but committed crash
  paths, listed explicitly). Ledger row per committed crash.
- Gate: `cargo test -p <crate>` replays a temporarily-committed crash
  file (watch the file show up in the test run), then remove; `just
  gates` still clean.

**W-B5 — TypeGenerator emission (Lane B).** Depends on W-B1-W-B4
standing and on a campaign demonstrating structure-aware mutation
pays (decision D3).
- Root crate: `bolero = { version = "0.13", optional = true }`, feature
  `fuzz = ["dep:bolero"]`. Emitter: cfg_attr derive + ranged-field
  `#[cfg_attr(feature = "fuzz", generator(<start>..=<end>))]` from
  `Range.mk?` data. Regen + commit the byte-tie diff.
- Gate: `just gen-check`; `cargo check -p lean-rust-wasm --features
  fuzz`; one `with_type::<User>()`-style harness compiles and runs
  under both the test engine and one libfuzzer minute.

**W-B6 — Kani v1 (§2).** Independent of W-B5.
- Install kani (network, one-time). Harnesses:
  `crates/wasm-delta/tests/proof_codec.rs` (cfg(kani)-gated) over the
  primitive decoders in `codec.rs`: no panic, no overflow, no OOB,
  bounded lengths. Optionally hostgen's tokenizer.
- Gate: `cargo kani --tests --harness proof_codec -p wasm-delta` clean,
  locally; measured runtime recorded in this doc's §10. NOT wired into
  `just gates`.

**W-B7 — Campaign script (optional).** `just fuzz-campaign target` =
bounded libfuzzer run + promotion prompt for crashes. Only after W-B1/
W-B4.

## 10. Risks

- **Engine availability/offline:** cargo-bolero + kani are network
  installs; the registry cache already holds all bolero-0.13.x crates
  (verified), so the TestEngine lane builds offline. Campaigns/Kani
  degrade to unavailable, not to broken — the CI lane never needs them.
- **Nightly:** only campaigns-with-sanitizer need it; we already have
  it for `-Z build-std`. A future stable-only box still runs the whole
  CI fuzz lane.
- **Kani cost:** exponential in loops/strings; scope-hold to bounded
  primitives (§2). If even those blow up, the fallback is kani on
  individual functions (`--harness` per fn) — the design survives v1
  being only `codec.rs`.
- **CI time:** TestEngine lane adds seconds (512+256 fixed iterations).
  Campaigns/Kani stay out of CI.
- **Byte-tie churn:** W-B5 rewrites a generated file — one reviewed
  regen, then stable; the cfg_attr wrapper must be exactly right or
  the production build breaks (caught by `just check` immediately).
- **nextest interaction:** `check!` resolves its target via thread
  name/path — works in-process; verify under nextest in W-B2 rather
  than assume.

## 11. Owner decisions (with recommendations)

- **D1 — Corpus commitment policy.** Recommend: corpora gitignored,
  crash artifacts committed (§5). The book's "commit the corpus"
  default is for projects without a byte-tie culture; ours treats
  generated-only-as-evidence as law.
- **D2 — Kani in CI.** Recommend: not in v1; local on-demand with
  measured runtimes recorded, revisit once harness scopes settle.
  Kani's cost profile (§2) is wrong for the gates' budget-check
  discipline today.
- **D3 — TypeGenerator emission timing.** Recommend: defer (Lane B /
  W-B5) until a libfuzzer campaign demonstrates a find the
  byte-mutation + `Unstructured` lanes could not reach; the derive's
  value is structure-aware *mutation* under coverage feedback, which
  only campaigns exercise.
- **D4 — `just fuzz` default engine.** Recommend:
  `just fuzz name engine=""` → `cargo bolero test name` (test engine,
  stable, deterministic) with an explicit engine arg for libfuzzer;
  sanitizer-ful campaigns stay an explicit nightly act.
- **D5 — Where the fuzz feature lives.** Recommend: root crate gets
  the optional `bolero` dep + `fuzz` feature (generated types live
  there); test-only crates (guestlang-host, wasm-delta, guestlang-rt) keep
  their unconditional dev-dependency as landed. No new dependency in
  production builds.

## 12. Follow-ups outside this doc's write access

- `notes/README.md` index row for this file (the index edit belongs to
  the owner or a W-order).
- The justfile `fuzz` fix (W-B1) is a tree edit — not made here (this
  task was design-only; the tree beyond notes/ is untouched).

# Execution plan 2026-09-15 — subagent work orders

Atomic, independently gateable. Sources: `code-review-2026-09-15.md`
(findings), `lean-cohesion-plan.md` (the refactors), this session's
ecosystem pass. Verification for EVERY item: `just lean-build && just
lean-axioms && just gates` green; byte-tied artifacts unchanged unless
the item says otherwise. Rules for agents: never edit GENERATED files;
compile after every declaration; no sorry/axiom; module headers keep
ownership/exclusions/decision only.

## Wave 0 — correctness fixes (do first, small)

- **W0.1 Oracle single-source.** `wasm-backend/GenMain.lean:235`
  `oracleSrc` (string literal) vs `Oracle.lean` (library, has the
  Plausible `genRows` supplement) disagree; regenerating drops 130
  rows. Make GenMain emit FROM Oracle.lean's data (or delete the
  library and own the string). One source, one artifact.
- **W0.2 Contradictory comment purge.** WasmBackend.lean:543-554
  ("GATED OFF" + "RESOLUTION: LANDED") and :1218; GenMain.lean:423-426
  ("OBSOLETE"). State current truth only.

## Wave 1 — the kit + consolidations (no behavior change)

- **W1.1 Liberate the correspondence kit.** Move `Iso`/`PartialIso`/
  `Denotes`/`ReprOp`/`iterateBounded` from `Machines/Foundations.lean`
  to a core-only home (codegen-core or new `kit` package); drop the
  mathlib-linter imports (they need zero mathlib). `Dag` stays in
  Machines pending its scheduler consumer.
- **W1.2 First instances.** `EnumWire` generates a `PartialIso` value
  per enum; `Codec` combinators get `PartialIso` wrappers (append-form
  law transported through bind); mangler round-trip tests cite
  instances. No theorem statements change.
- **W1.3 One did-you-mean.** Delete qlang's hand DP
  (`QLang/Error.lean:19-38`); use `CodegenCore.didYouMean`.
- **W1.4 One Async marker home.** `Async.Future`/`Async.Stream` move
  to schema-lang (one copy); Demo.lean and FeatureFlags.lean import,
  delete their copies. Reifier name-match updated.
- **W1.5 One equality for SType.** Delete `Decode.lean:4215-4514`
  `decEq?` (299 lines): prove `eqAns` completeness (~60 lines), define
  `DecidableEq` beside `Typed/Schema.lean` (not in Decode).
- **W1.6 Emitter spine.** `Registry.pipelineRust` → one
  `Emit.Machine.moduleRust` call (Registry already imports it);
  `worldWitOf` (wasm-backend/GenMain.lean:204) folds via
  `Emit.Wit.worldOf` instead of hand-mirroring record user / variant
  order-error; `asyncFns` derives from the registry
  (`FuncSem.delivery`/`ret`). Byte-tie must not move.
- **W1.7 `runEmitters` in codegen-core**; schema-lang/faults GenMains
  call it. Byte-tie must not move.
- **W1.8 gonzalgo: wire or drop.** Either land `just lean-dump` +
  `just lean-impact pkg decl` (per lakefile comments' promise; the
  vendored bundle is already a dbsp/Machines dep) or remove the dep
  and fix the comments. Decision: wire it — the impact query is the
  recompile-scope answer for the 15-package tree.
- **W1.9 Axiom gate dedup.** The LintKit env-linter
  (`AxiomAllowlist`) subsumes the shell `just lean-axioms` grep;
  keep ONE. Decide: env-linter wins; the shell recipe delegates.

## Wave 2 — metaprogramming (the leverage wave)

- **W2.1 Qq in Meta/Reflect.** Convert `tyToExpr`, `instTy` assembly,
  `fieldsToExpr`, the update-lane instance emission to `q(...)`
  quotations. schema-lang has mathlib in closure (via Machines) — Qq
  is free.
- **W2.2 `deriving ToExpr` (core)** replaces the quotation triple
  (W2.1's residue) if the handler covers `Ty` (String/List Nat —
  should). Verify on build; else keep one hand instance, delete two.
- **W2.3 `machine!` entourage.** The macro gains: transition-table
  emission, `tableStep?_eq_step?` proof, `DecidablePred Inv` instance,
  payload-carrying events. Deletes ~250 hand lines across Pipeline/
  OrderMachine/Update/feature-flags/Sync.
- **W2.4 `register_check_attribute` macro** for the five near-identical
  `registerBuiltinAttribute` blocks (Reflect ×3, GuestGate ×2).
- **W2.5 Error system upgrade.** Named error explanations
  (`register_error_explanation`, core 4.33) for the elaboration gates
  (`@[schema]`, schema_invariant, schema_update, HasCol misses);
  unexpanders so goals/errors show `id > 0`, not the GADT; keep the
  enumerate-the-valid-space discipline. `TestKit.CheckResult` carries
  structured errors (inductive + render), not String.
- **W2.6 Structure-side derive.** Match `derive_variant_cases`:
  schema abbrev, RowVals mirror, `toVList` — kills the hand-copied
  field lists in std/feature-flags/Demo (`userSchema`,
  `flagSentinelRow`, `userNameLenRow`).

## Wave 3 — proof automation (policy: generate > grind > omega/
decide > aesop-leaf-only in mathlib packages)

- **W3.1 Macro families.** `stream_cases` (dbsp ×9+), `binop_case` +
  `frame_tail` (Sem.lean exec_typed, ~-140), `nullability_split`
  (Decode.lean required/nullable twins, ~-350), `fuel_ge`
  (Correct.lean), one local tactic for `decodeRel_reEnc`'s ladder
  (~-200). Precedent: `err_tail` (Sem.lean:390).
- **W3.2 grind sites** (core, no dep): cascade guard matrix
  (TickCascade.lean:213-240), membership have-blocks
  (TickCascade.lean:65-167), Subschema List.mem inductions,
  Relational `_pos` family.
- **W3.3 simp sets.** `zset`: wire at the ~20 hand-listing sites or
  strip the tags — no third state. Enable core `unusedSimpArgs`
  tree-wide (library targets).
- **W3.4 VExpr finally-tagless / RawTy.** One expression language,
  three interpreter instances (evalV/evalU/evalB); the tie test
  graduates to construction; `evalBNeutral` workaround class dies.
  VCase folds in as the same family over a different leaf.

## Wave 4 — behavior substrate (dbsp/Machines loadbearing)

- **W4.1** `InfiniteRun` IS `Dbsp.Stream`; string Session layer
  deleted (generic `TProtocol P` only); `ConvergentMachine` deleted.
- **W4.2** `RewindableMachine` rebuilt over `ChangeInversion`;
  `rewind_suffix` = iterated `correct_invert`.
- **W4.3** `DeltaSystem` instance for the schema cascade
  (`cascade_two_commute` becomes `disjoint_commutes` +
  `applySeq_perm` for N updates).
- **W4.4** `Ckt Func` → Rust emitter; emitted header cites
  `incrementalize_ok` by name; `#check_cert` in CI.
- **W4.5** Substrait `Rel` → `Ckt` lowering (7/10 ctors today; add
  the linear measure operator for aggregate; sort/fetch documented
  out-of-scope).

## Wave 5 — product surfaces

- **W5.1 `@[event_sourced]`**: record → delta variant + journal codec
  + replay fold + migration lane + Rust `Change` impl. Assembles
  Delta/Codec/Trace/Migration. **ledger grows into this lane's
  dogfood** (deposits-as-deltas, balance-as-integral).
- **W5.2 Fault registry v2**: attribute registration (not def lists),
  typed `Fault` variants emitted into WIT (`result<T, fault>` at the
  boundary), one E-code space shared by elaboration errors (W2.5) and
  runtime errors. allocateCodes gains `Nodup` in the type.
- **W5.3 Substrait grammar-as-data** (the big Decode.lean rewrite;
  split the file along its sections FIRST).
- **W5.4 Module system adoption** (leaf packages first: kit,
  codegen-core; `meta` sections for the elab modules).
- **W5.5 Lake facets for codegen** (`lake build MyPkg:rust`).

## Ongoing — lints codifying the doctrine (each lands WITH its
doctrine entry, same commit)

stale-path text lint; simp-set-usage lint; schema-`abbrev` lint;
fuel-next-to-proved-measure lint; cross-package hand-mirror lint
(extend DupDefBodies); one-writer env-linter; no-new-`partial def`
ratchet; layering gate via importGraph (vendored).

## Wave 6 — interop + oracle v2 (from notes/studies/cedar-study.md)

- **W6.1 Adopt lean-sys properly (decision: embrace, don't shim).**
  Fork/vendor digama0/lean-sys and bump it to our toolchain
  (v4.33.0): fix the known rot — `st.rs` symbol names (never existed),
  `io.rs` 2-field io_result (1-field at 4.33), removed small-allocator
  exports + mimalloc default (issue #16), `lean_uint64_mix_hash` (now
  inline), the 4.33 module-init ABI (world token dropped, phase-split
  init names). Add a lean.h diff gate to `just gates`: toolchain bump
  ⇒ diff review against the bindings. Upstream the fixes if digama0
  wants them; otherwise maintain the fork — it is generally useful
  (the only Lean C-API bindings) and we become its 4.33 home.
- **W6.2 `crates/lean-ffi`**: the safe layer OVER lean-sys, cedar's
  proven shape — `OwnedLeanObject` RAII (Drop→dec, Clone→inc),
  borrowed refs with phantom lifetimes, tag-checked ctor access,
  thiserror'd error enum, init discipline (Once + per-thread
  init/finalize + `lean_set_exit_on_panic(true)`), and our marshaling
  rule: **only scalars + byte arrays cross** (payloads in our proved
  codec's wire format; NO structure-field reads on the Rust/C side).
  First exports: the oracle query fns. Bidirectionality is a goal in
  itself: this crate is also the substrate for Rust tooling driving
  Lean (build-time queries against the registry, REPL-driven agent
  loops later).
- **W6.3 Oracle v2**: comparison pushed INTO the oracle (request
  carries context; Lean emits verdicts, not rows); error-equivalence
  modes (Ignore/Identity/Full); amortized probe batches (one context,
  N probes); wasmtime+wasmi sabotage duel KEPT (our edge over cedar).
- **W6.4 Generator emitter**: Rust gen crate emitted from schema
  items, cedar's target shape — SchemaGen-style registry trait,
  lightweight Ty-mirror enum with exhaustive From, explicit depth/
  width budgets, weighted-choice macro, collision pools (90/10),
  adversarial knobs inside well-typed arms.
- **W6.5 Typed errors end-to-end**: closed `Fault` inductive per
  interface, emitted to WIT as `result<T, fault>`; soundness
  statements name the survivable fault ctors (the `EvaluatesTo`
  pattern); E-code space shared elab↔runtime (W2.5/W5.2 merge here).
- **W6.6 CI**: checkThm-style lint (proof root transitively imports
  every proof file) + doc-gen4 in CI.
- **W6.7 Module system migration** per cedar's recipe (`module` +
  `public import` + per-decl `public`), directory by directory,
  starting at kit/codegen-core. Precedent: cedar PRs #887-#912 on
  v4.33.x.
- **W6.8 `guestlang_solver`** (the loom pattern): one open discharge
  macro, `macro_rules`-extensible per package, `!`/`?` modes;
  `machine_safety` becomes its Machines rung.
- **W6.9 Velvet-shaped Sem theorems**: correctness stated
  fuel-insensitively (partial), termination/variants separate
  (Convergent). Refactors Correct.lean statement shapes, no semantics
  change.
- **W6.10 Intrinsic lane** (cedar C1): `inductive Intrinsic` + total
  `call`; StrOps bodies become the oracle arms; wasm-backend's
  `stdOp?` and the WAT emission fold the same ctors; the name mirror
  dies.
- **W6.11 Check-eliminates-error theorems** (cedar C2): per static
  check (GuestGate, banAsync, schema_invariant), a theorem naming the
  `Fault`/error ctor it rules out. Lands with W6.5's closed Fault
  universe.
- **W6.12 Style guide** (cedar C3): adopt cedar's GUIDE rules into
  notes/lean-doctrine.md — casing (Prop-returning fns UpperCamelCase),
  anonymous-hypothesis statements, simp-only/exact/spell-types proof
  stability rules. Lint what's lintable (casing, import sorting).
- **W6.13 Opacity discipline** (cedar C4): private/opaque
  representation projections on registry rows + RowVals; consumers
  via lemma interfaces; `@[expose]` audit under module system (W6.7).

# Lean code review 2026-09-15 — coherence, self-use, direction

Scope: all non-test Lean in `lean/` (15 packages, ~38.6k lines) + template/ +
src/ consumption. Method: 4 parallel full-package surveys (substrait,
wasm-backend, dbsp+Machines, 10 small packages), direct reads of
schema-lang core (Ty/Item/Reflect/Registry/codegen-core), every load-bearing
claim spot-verified in the tree. Supersedes nothing; extends
`notes/lean-code-review-2026-09.md` and `notes/lean-strategic-review.md`.

## Verdict

The core loop (@[schema] → registry → pure emitters → byte-tie → gates) is
genuinely coherent and the best thing here. The problem is RATIO and
CONNECTION: 38.6k lines of Lean machinery generate 773 lines of Rust for a
demo whose spec is ~130 lines (User/Order/getUser/watchOrders). Three
observations organize everything below:

1. **The pipeline is built ahead of the authoring surface.** Gates,
   emitters, proof kits, lint kits, docs emitters are mature. What a user
   can *express* is v1-minimal: no map/set, no generics, no recursive
   types, no multi-payload variants, no field docs/defaults/deprecation,
   VExpr = gt/eq/and/strlen over u64. For "ergonomically model an
   application in Lean", the spec language is the bottleneck, not the
   tooling around it.
2. **The tabular packages don't compose into a product.** substrait
   (plans), qlang (authoring), dbsp (incremental theory), Vortex (dtypes)
   each exist; no path generates Rust from any of them. dbsp's
   `incrementalize_ok`/`seminaive_equiv`/`stagedN_eq_jointN` certify
   nothing downstream. Substrait plans are not schema citizens.
3. **The repo breaks its own rules at the seams.** The worst confirmed
   case: the wasm oracle has TWO sources that disagree (below). Several
   "one copy" doctrines (did-you-mean, EqAns, Certs, Async markers) have
   2-3 live copies.

## 1. Where the systems aren't used (verified drift/duplication)

Ordered by severity.

### 1.1 The oracle has two disagreeing sources — silent test-strength regression
- `wasm-backend/GenMain.lean:235` `oracleSrc` (~200-line Lean program as a
  string literal) is the sole writer of `target/oracle.lean`
  (GenMain.lean:441), which `just wasm-compile` regenerates and runs
  (justfile:345-365).
- `wasm-backend/Oracle.lean` is the extracted, testable library — and it
  carries the Plausible `genRows` supplement. `oracleSrc` contains ZERO
  Plausible: the next regen silently drops 130 Gen rows from the 679-row
  manifest. The committed target/oracle.lean was last produced by a
  generator state newer than the committed GenMain.
- Fix: GenMain should render the oracle FROM `Oracle.lean`'s data (one
  authority), or Oracle.lean should be deleted and `oracleSrc` owned as
  the single source. Today: two owners, one artifact.

### 1.2 `worldWitOf` hand-mirrors the WIT the emitter already folds
- `wasm-backend/GenMain.lean:204-216` builds `demo-world.wit` by string
  interpolation with a HAND-COPY of record user / variant order-error —
  while GenMain imports `SchemaLang` (`:4`), i.e. `Emit.Wit.worldOf` is
  in scope and byte-tied. The stated excuse ("the drift surface = the
  differential duel") is backwards: the duel checks execution, not that
  two WIT spellings agree.
- Same file: `asyncFns := ["watch-orders","watch-counts","watch-users"]`
  (WasmBackend.lean:543) and `adapterShape?` keyed on hardcoded kebab
  names — both derivable from the registry (`FuncSem.delivery`, `.future`
  returns). The registry fold already drives exports; the async table
  predates it.

### 1.3 Substrait is a parallel stack, not a citizen
Verified: substrait depends on nothing in the monorepo (only LSpec +
TestKit); the arrow points the other way (schema-lang Bridge, qlang).
- THREE type universes (`Proto.PType`, `Typed.SType`, `Grammar.ScalarCtor`)
  none of them `Ty`; `Bridge.lean` is one-way `Ty → SType?`.
- `EqAns` exists twice (Substrait.Typed.Schema:117 → copied verbatim into
  SchemaLang/Ty.lean:148, acknowledged). `HasCol` exists three times
  (SchemaLang.Field, Substrait.Typed.Schema, qlang's ofIndex).
- `Emit.Text` is raw string munging — no codegen-core, no `Std.Format`,
  no Emitter-plugin shape. Deliberate ("independently publishable") but
  it means plan codegen shares nothing with the rest.
- `Proto/*.lean` mirrors `protos/*.proto` by eyeball only — no byte-tie,
  no drift gate. The vendored protos + protoc-gen-lean4 seam sit excluded
  (lakefile.toml:8-12, documented).
- Nothing generates Rust plan types. For the vortex/arrow-engine goal,
  this is the missing product: plan authoring (qlang) → typed plans →
  encode/validate in the guest.

### 1.4 Small self-use gaps
- QLang hand-rolls edit distance (`QLang/Error.lean:19-38`, 20-line DP)
  while `CodegenCore.didYouMean` exists precisely so "every error path
  reaches it core-only". QLang's is the stale copy.
- `Dbsp.Certs` `#check_cert` pattern is re-implemented, not imported, in
  SchemaLang.Invariant (`checkCitation?`) and cited-comment-only in
  feature-flags. Move `Certs` to codegen-core; three copies of a gate is
  a gate that drifts.
- `Async.Future`/`Async.Stream` marker defs are copy-pasted per authoring
  module (Demo.lean, FeatureFlags.lean:50-62 flags it as an unclosed
  dogfood finding). One copy belongs in SchemaLang (matched by NAME in
  `tyOfExpr?` — a string match that a canonical home makes safe).
- `schema-lang/EnumWire.lean:45-46` (library) imports Plausible + TestKit
  to emit PropSpec test code. Layering smell: library → test-kit edge.
  Split the PropSpec emission into a test-support module.
- `edgepython/Eval.lean` duplicates `WasmBackend.Sem` (219 lines) because
  Sem's op fragment is too small — the in-file "REPORTED" note is
  unresolved. Either grow Sem's fragment or accept edgepython as the
  probe that sizes it.

## 2. Cruft / bloat (verified)

- `substrait/Substrait/Decode/` — empty directory. `Parser.jump`
  (Decode.lean:88) — defined, `@[simp]`, zero callers.
- `wasm-backend/target/lit.lean` — 5-line dead experiment, referenced
  nowhere.
- `Machines/lakefile.toml` — `[[require]] TestKit` appears TWICE.
- `Machines/Foundations.lean` (246 lines: Iso/Dag/topoSort?/iterateBounded)
  — imported only by the root umbrella; consumed only by Machines' own
  Tests. Give Dag a consumer (the cascade scheduler is the natural one,
  per Staging.lean's SCC story) or move to Tests.
- `dbsp`: `Determinism.lean` (122), `Effects.lean` (202), `Subsystems.lean`
  (73, self-described "READINGS… one-liners") — imported only by root
  Dbsp.lean, zero instantiations. `dbsp` as a whole has no consumer
  outside Machines' two edges (Sim, LinearMachine).
- `proofkit` (152 lines) — zero importers anywhere; all three modules
  self-describe as demonstrations. Delete or fold into TestKit.
- `ledger` (113 lines) — self-described "minimal skeleton", spec stub
  `deposit` returns 0 while impl adds. Duplicates Demo/feature-flags
  coverage. Either delete or promote: a ledger is THE canonical
  event-sourcing demo (schema + updates + migration + trace conformance)
  — currently the repo has no flagship example.
- `codegen-core/Emit/Certified.lean` — `CertifiedEmitter` has no
  non-demo consumer.
- LintKit: `RecursiveSimpEqns` shipped default-OFF with an 83-violation
  census; `PackageNamespace.lean:71-92` hardcodes the workspace package
  table (a second `lean_pkgs` mirror, with a trailing-comma artifact).
- Stale references: 19 Lean files cite `notes/lean/lean-v3.md` /
  `TOOLKIT.md` / `SPEC-core.md` — no `notes/lean/` exists (notes/ is
  flat). Multiple headers reference a `Flatland` package absent from the
  tree. Header doctrine is good; stale pointers inside headers are the
  liability — keep headers to ownership/exclusions/decision + a notes/
  link.
- Comment archaeology: WasmBackend.lean:543-554 carries a "GATED OFF"
  note immediately followed by "RESOLUTION (this session): async =
  LANDED". Session transcripts don't belong in headers.

## 3. Unidiomatic Lean (representative, verified)

- `Substrait.Decode`: `SType.decEq?` ~200 explicit cross-product arms
  (`Decode.lean:4212-4514`) — one catch-all `| _, _ => isFalse (by intro
  h; cases h)` after the diagonal replaces them. Worse: the
  `DecidableEq SType` instance lives in DECODE — importing `Typed`
  without `Decode` silently lacks it.
- `Substrait.Emit.Text` `partial def expr/relWidth/relLines` (:259,:334,
  :405) block the headline `parse ∘ emit = id` at plan level; the fix
  pattern exists in-repo (`decodeRel`'s well-founded recursion with
  hand-proved `wf*_size`, Decode.lean:4706-4761).
- `Substrait.Emit.Text` `Ctx.extensions : List (Nat × Nat × Nat × String)`
  with `x.2.2.2` projections (:158-171) — a structure.
- wasm-backend: wasm types as Strings (`wasmTyOf? : Expr → Option
  String`, `Wat.Param.ty : String`); local names minted as `"l{n}"` then
  reverse-parsed by `startsWith "l" ++ toNat?` in Correct.lean:122 —
  a name↔index round trip through strings, exactly where proofs pin the
  emission. An inductive + a Nat-indexed env removes a proof-adjacent
  string channel.
- `WasmBackend/Layout.lean:76-79` `getLast!` ×2 where the match already
  proves non-empty.
- `Machines.Session.gatewayProto:295` hardcodes wire-name strings
  (`"option<user>"`) — a stringly shadow of SchemaLang.Session's typed
  instance of the same conversation.

## 4. What IS coherent (keep doing)

- `Item`/`Ty` closed universe + `universeCheck` diagnostic authority with
  did-you-mean everywhere. The "error enumerates the valid space"
  discipline is uniform and real.
- Emitters pure `GenCtx → List GeneratedFile`; drivers own IO; byte-tie +
  one-writer audit + `jobsCoverEmitters_true` as `rfl`. The forge-jobs
  manifest derived FROM the registry is the model: derivation, not
  tie-tested copies.
- `declare_enum_wire`: boilerplate family generated, round-trips proved,
  negative control mandatory. Item.lean's own enums dogfood it.
- Machines → Rust: `Emit.Machine`/`Emit.Typestate` fold a PROVED table;
  the wildcard collapse is checked against the table. This is the
  template for all behavior codegen.
- `schema_invariant`/`schema_update`: elaboration-time gates (HasCol
  misspelling, type gate, volatile scan) + `UpdatePure` instance emitted
  with `rfl` against stored data — proof checks the gate. Best
  "elaboration is the CI" example in the tree.

## 5. Where to take it further (against the stated goal)

Goal restated: model apps in Lean (mostly vortex/arrow tabular),
generate Rust/wasm buf-style, assured correctness.

### A. Authoring surface breadth (the real bottleneck; do first)
- `map k v`, `set t` in `Ty` (closed-universe rule makes this
  compiler-enforced across emitters — the machinery is ready).
- Parameterized types via monomorphizing reflection (v1 rejects
  `numParams != 0`); recursive types behind fuel exist in lowering
  (`refSem` fuel 8) but not registration.
- Variant cases with record payload (desugar to anonymous record item).
- Field docs/defaults/deprecation as item data — deprecation feeds the
  breaking gate; docs feed the docs emitter (which exists and is good).
- Two-pass registration to kill the register-before-reference ordering
  constraint (currently a v1 authoring wart the template documents).
- VExpr breadth: list length (GuestlangStd's `userComplete` gate waits
  on it), string ops, arithmetic, over all scalar tys — it is the
  behavior-modeling vocabulary and it covers one numeric type.

### B. Behavior modeling → codegen (the differentiator, half-built)
- Generalize `machine!`: today `Emit.Machine` concretely imports
  Pipeline/OrderMachine; a USER's machine registers nowhere. Give
  `machine!` a registry extension + a generic emitter so every project
  gets Rust step-fns, typestate, and conformance sweeps from one
  declaration. The proof obligations (rank, tableStep?) should be
  GENERATED with the machine, not hand-proved per instance.
- Pre/postconditions on `@[schema_fn]` as VExpr over params/result —
  the invariant lane's machinery transfers directly; emitters generate
  host-side asserts + the oracle gets rows.
- Give `FuncSem.determinism` its first REAL consumer (today: armed,
  fired only in schema_update's volatile scan): aggregation/fusion in
  the qlang→substrait lane is the natural site.

### C. The tabular data plane (the stated domain; currently shallowest)
- Arrow emitter as a sibling of `Vortex.Emit` (arrow-schema is simpler
  than vortex dtypes; absence is conspicuous given the stated focus).
- Batch data path: `Vortex.Batch` proves read-side theorems; nothing
  emits columnar encode/decode Rust. Byte-tie batch bytes against Rust
  vortex the way the codec round-trips pin Lean.
- Substrait citizenship, two options: (1) plan items in a SEPARATE
  registry with own emitters (Ty stays closed — recommended; the
  registry/emitter machinery is parameterized over Spec already), or
  (2) extend Ty — expensive, compiler-enforced. Either way: reinstate
  the protobuf codec (the ProtoGen seam is documented) or write a Lean
  encoder over Proto.*; text-only wire blocks engine interop.
- dbsp connection, cheapest-first: `Ckt Func` instantiated over Z-sets
  of schema-`Ty` records + a per-node Rust emitter citing
  `incrementalize_ok` as the certificate comment; substrait `Rel` →
  `Ckt` lowering inheriting `cycle_incremental`; THEN the journal/trace
  bridge (`Rewind.rewind_suffix` ↔ D/I inverse — today a prose
  cross-ref).
- Substrait function catalog: generate `FunctionSig`s from the vendored
  extension YAMLs instead of 8 hand `declare_binop` entries — exactly
  the schema-driven codegen this toolkit is FOR.

### D. Consolidation pass (prepaid, do alongside)
One copy each: oracle source (1.1), Async markers, didYouMean, EqAns,
HasCol, Certs. Fix worldWitOf + asyncFns to fold the registry (1.2).
Deletions from §2. Stale-ref sweep (`notes/lean/` → flat paths).

## 6. Suggested order (small, atomic, gate-green each step)

1. **P0** — oracle single-source (1.1): silent test-strength regression.
2. Deletions: lit.lean, Decode/, Parser.jump, proofkit, dup lakefile
   require, Foundations→Tests-or-delete. ledger: decide delete-or-flagship.
3. Consolidations: Async markers, didYouMean, Certs→codegen-core,
   SType DecidableEq fix.
4. worldWitOf→Emit.Wit, asyncFns→registry (1.2); substrait Emit.Text
   totality via the decodeRel WF pattern.
5. Surface breadth: map/set in Ty; VExpr list-length; two-pass
   registration.
6. machine! registry + generic emission (B); Arrow emitter (C).

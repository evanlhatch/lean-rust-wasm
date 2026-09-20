# Lean Refactor Guide — the executable work list

Companion to notes/lean-doctrine.md (the why + enforcement). This is the
what/where: every finding from the 2026-09-09 audit wave, with file:line
and the change to make. Phases in order; gates green at each boundary.

Gates:
```
devenv shell --profile wasm
just lean-build                      # per-package as you go
just gates                           # gen-check + wit-check + lean-axioms
```
Lean toolchain (no elan shims):
`PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.33.0/bin:$PATH"`,
`lake build` per package in `lean/`.

Rules for whoever executes (human or agent):
- One concern per commit (`jj describe` once the change is known).
- Never alter a theorem STATEMENT or a committed artifact's bytes except
  via regeneration; if a listed replacement fails to elaborate, revert it,
  report the exact error, move on. Do not weaken anything to make it pass.
- Bug fixes (Phase 0) change BEHAVIOR deliberately — each ships with a
  test pinning the fixed behavior.
- `@[builtin_nolint "reason"]` is the escape hatch for lint findings that
  are deliberate; the reason is required.

---

## Phase 0 — correctness bugs found by the audit (fix first, with tests)

| # | File:line | Bug | Fix |
|---|---|---|---|
| 0.1 | schema-lang/SchemaLang/Vortex/Lower.lean:52-62 | `Ty.lower` corrupts nullability 3 ways: `.option a` lowercases the ELEMENT with `.nullable` (option<list<u8>> → nullable list of nullable u8); `.ty n => sem n` drops the requested nullability (nullable ref emitted non-nullable); `.result` silently drops the err side while the header promises a tag+payload union — a wrong artifact that SUCCEEDS | element lowers `.nonNullable`; thread nullability through `.ty` (or make `sem` nullability-polymorphic); `.result` returns `none` until the union lands. Add tests pinning all three. |
| 0.2 | schema-lang/SchemaLang/Vortex/ExtDType.lean:97-101 | `deserializeBody` hardcodes `"position"` — works only because exactly one `u8Enum` exists; a second emits the wrong type | bind the suffix: `\| .u8Enum allowed suffix => … metadataRust (.u8Enum allowed suffix)` |
| 0.3 | schema-lang/SchemaLang/Emit/Rust.lean:33-42 + Delta.lean:108 | `hasFloat` treats `.ty n` as float-free → record holding a float behind a named ref gets `#[derive(Eq)]` while the ref'd type doesn't impl Eq → generated Rust doesn't compile | resolve `.ty n` against the universe (emitter has `items`), or conservatively treat `.ty` as float-containing unless resolvable-and-clean; land with 4.5's `derivesFor` helper (one fix site) |
| 0.4 | faults/Faults/Registry.lean:58-64 | `allocateHost` starts at E110 by fiat — guest fault #11 collides silently | host start = `100 + apiFaults.length` (driver-computed); add test: `(allocate apiFaults ++ allocateHost hostFaults).map (·.2)` is `Nodup` |
| 0.5 | wasm-backend/WasmBackend/Check.lean:88-92,109-117 | `@[guest_std]` renders STRICT-level reasons (banned? hardcodes .strict) | `reasons (level : Ban)`, thread the level |
| 0.6 | schema-lang/SchemaLang/Item.lean:155-159 | variant payloads escape the async ban: `variant v { c(future<u8>) }` passes universeCheck but emits WIT the canonical parser rejects | apply `banAsync` in the variant arm (extend `asyncField` or add a diag ctor); test via the WitFixture pattern |
| 0.7 | schema-lang/SchemaLang/Meta/Reflect.lean:167,213 | reifier misdiagnoses non-boundary types: field `count : Nat` reports the FIELD name as an unknown TYPE with did-you-mean against type names; `boundaryFragment` (:127) is defined and never used | add `SchemaDiag.nonBoundaryType` ctor whose render appends `boundaryFragment`; use in checkStruct + checkInductive |

## Phase 1 — structural fixes (drift channels the audits exposed)

| # | File:line | Action |
|---|---|---|
| 1.1 | wasm-backend root | Delete tracked empty debris: `patch.txt`, `WasmBackend.lean.new` (both 0 bytes, tracked). |
| 1.2 | substrait stale references | lakefile.toml comment still says "Vortex dtype model"; umbrella `Substrait.lean` doc references `Substrait.ProtoGen` (excluded) — fix both to describe the text-only surface + the documented add-back seam. |
| 1.3 | substrait/Substrait/Decode.lean:3562-3564 | Delete the shadowed first `lines` binding + stale "hmm" comment (present here, confirmed by diff agent). |
| 1.4 | schema-lang/Tests/Main.lean:198 | Golden path hardcodes `CodegenCore.Emit.header e.style "schema-lang" "Demo.lean"` — use `e.specSource`; regenerate goldens; then 6 of 11 emitters byte-tie what production actually emits. Consider asserting `goldens/<e>/<f> == src artifact` so the two byte-tie layers can't diverge. |
| 1.5 | schema-lang/SchemaLang/Emit/Registry.lean:88-95 | `pipelineRust` hand-copies the PROVED `pipelineTrans` table as `.raw` strings — fold `Pipeline.pipelineTrans` into arm text so emitted Rust is a function of the proved data (+ structural `failed` arm). |
| 1.6 | faults/Faults/Emit/Registry.lean:34-37 + schema-lang same shape | `run` re-states paths declared in `outputs` — add the per-registry test: `(e.run spec).all fun f => e.outputs.contains f.path`. |
| 1.7 | faults/Faults.lean | Split demo specs out of the lib root (mirror schema-lang): `Faults.Spec.Demo`/`Host` into their own lean_lib so downstream `import Faults` doesn't pull the order-shop demo. |
| 1.8 | faults/Faults/Spec/Demo.lean:30 | `knownTypes` hand-copies the schema demo universe's names — derive from the schema registry or emit it; minimum: a test tying it to the schema universe. |

## Phase 2 — dedup against codegen-core / core Lean

| # | File:line | Action |
|---|---|---|
| 2.1 | wasm-backend/lakefile.toml:9-11 + GenMain.lean:56,151 | Require `CodegenCore` (needs only `Emit.kebab`) instead of `SchemaLang`; drop mathlib/aesop/batteries/… from its transitive closure; drop the vestigial `` `Demo`` import (import `DemoFn` only). Verify `just wasm-compile`. |
| 2.2 | schema-lang/SchemaLang/Meta/Reflect.lean:42-47 | Use `CodegenCore.mkRegistryExt` instead of reimplementing its spec inline (Item.lean's header claims this already happened — fix the stale header too). |
| 2.3 | schema-lang GenMain.lean:27-33,35-36 ↔ Tests/Main.lean:177-184,196-197 | Extract into codegen-core: `loadRegisteredItems` (the importModules+loadExts preamble) and `writeFileCreatingDirs` (parent-dir computation + createDirAll). The 1.4 bug is what this duplication bought. |
| 2.4 | wasm-backend/Tests/Main.lean:3,43 | Drop unused TestKit import (or adopt `mainOfChecks`); add `testDriver = "WasmBackendTests"` to the lakefile for sibling consistency; move `def main` to the end. |
| 2.5 | schema-lang/SchemaLang/DidYouMean.lean:15-30 | `editDistance` → core `Lean.Data.EditDistance.levenshtein got d (maxDist+1)` (cutoff-bounded = the filter semantics; deletes the panic-on-bug DP). |
| 2.6 | schema-lang/SchemaLang/DidYouMean.lean:41-53 | `dedupStr` → core `List.eraseDups` (deletes the hand termination proof); `Wit.worldOf`'s inline dedup foldl (Emit/Wit.lean:100-102) joins it. |
| 2.7 | wasm-backend/WasmBackend/Check.lean:68-81 | `checkExprAt`'s hand-fold → `Expr.getUsedConstants` (core, memoized) + root-dedup; keep the scan-order the guards pin. |
| 2.8 | faults/Faults/Emit/Registry.lean:76-80 | `rootRel` duplicated AND double-applied (jobJson maps it again) — export `rootRel` from CodegenCore.Emit, pass raw outputs. |
| 2.9 | faults/GenMain.lean:16 | `unsafe def main` → `def main` (pure registry reads + writeFile; copy-paste residue). |
| 2.10 | wasm-backend/GenMain.lean:64-66 + oracle jsonRow | Add `| wat` (";; ") to CodegenCore's `CommentStyle` instead of hand-spelling the header; oracle JSON via `Lean.Json.mkObj`/`compress` (first string arg through the current concat path is an escaping bug). |
| 2.11 | schema-lang/SchemaLang/Item.lean:195 | Delete the overlapping `ToString (List SchemaDiag)` instance (core has the generic one — resolution roulette); make `SchemaDiag.renderList` a function. |
| 2.12 | schema-lang/SchemaLang/Field.lean:25-28 | `Field.get?` → core `List.getElem?`/`fs[i]?` (unlocks core's lemma set for `resolves`). |
| 2.13 | substrait Emit/Text.lean:71 `sep` | `abbrev sep` (or inline `String.intercalate`); then Decode's `sep_cons` (:1399 area = core `intercalate_cons_of_ne_nil`), `sep_toList_head`, `sep_len_ge*` collapse to one-rw corollaries of core lemmas. |
| 2.14 | substrait Decode.lean:3709 `joinCSep` | → `List.intercalate`; `sep_toList_joinCSep` becomes a corollary of core `@[simp] String.toList_intercalate`. |

## Phase 3 — strengthen gates and audits

| # | Action |
|---|---|
| 3.1 | substrait Tests/Axioms.lean: port the fuller gate list from the flatland lineage (~22 theorems: Typed.Rel.toProto, eval, scalarT, splitAppend_map_parseNamedCol, …) — lrw currently gates only `parsePlan`. Same review for other packages' Axioms.lean. |
| 3.2 | Registry audit trio, framework-wide (codegen-core test kit): `pathsUnique` + `jobsCoverEmitters` (exist) + NEW `run` outputs ⊆ declared `outputs` (per-registry test). |
| 3.3 | (with 1.7) faults lib/spec split. |
| 3.4 | wasm-backend: check oracle fns ⊆ `worldExports` — generate the oracle rows from `worldExports`, or `#guard` the subset relation in Tests. |
| 3.5 | schema-lang `Vortex/DType.lean` dead spec surface: `PType.byteWidth`, `wellFormed`/`fieldsWellFormed`, `DecimalDType.isValid`, `engineName`/`engineName_inj` — WIRE them (assert wellFormed over every emitted dtype in Tests; emit a byte-width table) or delete. Untested spec code is the drift this package exists to prevent. |
| 3.6 | schema-lang `Ty.eqAns`/`Ty.toType`/`TySem`: route `Diff.diff` through `eqAns` (the stated design — Diff.lean:87 comment claims it) or drop + fix the comment; mark toType/TySem as documented seeds or delete. |
| 3.7 | justfile: `check-schema` and `breaking` are TODO stubs — either wire them (schema-lang has Diff.lean!) or track openly in notes/full-remaining-work.md. |

## Phase 4 — the lifted-package sweep (substrait / dbsp / Machines)

The flatland audit findings transfer where the code matches (verified by
the diff agent: these files are near-identical modulo renames). Apply:

| # | Where | Action |
|---|---|---|
| 4.1 | substrait Decode.lean | The scalar-cluster family: 9 wrapper theorems `boolT`…`binaryT` (~919-981) delete via one ctor-generic `hscalar`; `scalarT` nullable branch ctor-generic via `Emit.Text.typeTextBase_scalar` (~110 lines); `typeDepth_le_len` shares its recursor skeleton with `parseType_typeText` (~100); `toString_toList_ne_nil`/`toString_head_isDigit` (4 sites); `startsWith_neg_of_head` replaces 4 copies; `parseExpr_lit_bool` twin branches merge; `plainChar_ne_*` septet macro/merged. **Do NOT do-notation the parser** (doctrine §8). |
| 4.2 | substrait Eval.lean:186-232, 445+ | `binKernel` helper (8 arms) + `run` local (6 measure arms); or jump straight to 4.4's `declare_binop`. |
| 4.3 | substrait Typed/Expr.lean:144-207 | `mkBinSig`/`Expr.binCall` helpers for the 8+8 sig/wrapper pairs. |
| 4.4 | substrait (metaprogramming) | `declare_binop` elab: one table drives sig + Typed wrapper + eval kernel. Precedent for the attribute+reflection style exists in schema-lang/Meta/Reflect. |
| 4.5 | schema-lang Emit/Rust.lean:90-100 ×2 + Delta.lean:108-110 | `derivesFor : List Ty → List String` — one Eq-eligibility fold (and the single fix site for 0.3). |
| 4.6 | dbsp Linear.lean:45,83,92,105,401 | Move `lifting_zero` up; add `lifting_neg`/`lifting_sub`; the 5 `add_left_cancel` re-derivations become one-liners. |
| 4.7 | dbsp Relational.lean:433-558 | Factor `distinct_mul`/`distinct_add` ℤ lemmas; three 16-line sign-analysis blocks collapse. `ite_ite` (:423) → mathlib `← ite_and` at call sites. |
| 4.8 | dbsp Circuit.lean | `CktDenote`/`IsLinearOracle` abbrevs (17 signatures); term-mode equiv refl/symm/trans. Staging.lean: `headFix`/`tailF` (15 subterm copies). StreamElim:147-168 `<;>` collapse. `cases t <;> simp` at ~11 sites. |
| 4.9 | dbsp ZSet.lean:148,165,180-183; Relational.lean:191-194 | `toSet`/`map` → abbrev; term-mode `map_linear`/`filter_linear`. |
| 4.10 | Machines Rewind.lean | Inversion lemmas `runLogged_cons_some`/`runLogged_nil_some`; the 7-site `Prod.mk.inj (Option.some.inj h)` ladder + contradiction arms collapse (~50 lines). |
| 4.11 | Machines Compose.lean | `Option.map_eq_some'` for both proj theorems; `by_cases hg <;> simp [hg]` for inl/inr. |
| 4.12 | Machines Sync.lean | Delete no-op `simp only at hinv ⊢` lines (4 sites); `safety := fun _ _ hinv => hinv` (3 sites); `guard_omega` macro in a new `Machines/Tactics.lean` (home until a shared ProofKit exists). |
| 4.13 | Machines Core.lean:114 | `@[simp]` on `step?_eq` (file's own stated discipline). Check Foundations' recursive defs the same way. |
| 4.14 | Machines Convergent.lean | Micro-idioms: `hact ▸ c.decreases …`; `obtain ⟨rfl,rfl⟩ := by simpa using h`; drop `by exact` wrappers. |
| 4.15 | All packages | `variable` rollout for ≥3-consecutive-binder-telescope clusters; `deriving DecidableEq` sweep on structures whose fields are decidable. |

## Phase 5 — TestKit investment + plausible rollout

| # | Action |
|---|---|
| 5.1 | `DetSpec`: PropSpec's positive-pass + control-caught discipline for deterministic `CheckResult`s (hand-reinvented at call sites today). |
| 5.2 | `expectErrorContaining (substrings : List String)`; `assertPointwiseEq`/`forallIn` (Dbsp/Tests has the same loop-witness 5×); `CheckM` StateT accumulator for IO drivers (substrait Tests' `results := results ++ …` pattern). |
| 5.3 | plausible instances + PropSpecs: `Proto.Expr`/`Rel`/`Plan` (the expression grammar is UNSWEPT — testExprs is a 9-item hand list); schema-lang `Item`/`Ty` (generator respects the closed universe; negative control = ill-typed/unknown-ref item must be caught by universeCheck); Machine labels/states (Session + LinearMachine conformance sweeps). Each ships with its control. |
| 5.4 | Move substrait's `PType` plausible instances out of the test file into a library `Testing` module for downstream reuse. |
| 5.5 | GateKit on TestKit.Golden: one `byteTie name path regenerate` + uniform `--update`/`--check` CLI for all gate exes (the 13-artifact byte-tie family keeps growing). |

## Status ledger (2026-09-09 audit-wave execution)

LANDED + gate-verified (`just gates` clean): Phases 0, 1, 2 (all three
package agents), 4.5–4.15, 4.1a–f (Decode.lean 3906→3664, −242), 4.2,
4.3, 5.1, 5.2, 5.4 (GateKit byteTie), 5.5.1, 5.5.7 (Codec.lean
combinators + Envelope, payoff `composite_decode_encode` closed by simp
alone). Decode.lean dead pair `splitTopLevel_join_rbracket`/
`sep_toList_joinCSep` was transformed (not deleted) — deletion candidate.

REMAINING (2026-09-15 — after the FINAL round: EdgePython + the
warm-start — the template's headline-capabilities ALL landed; the
open = the research-tail + the owner's WIP):

- **EdgePython LANED** (`lean/edgepython` + the two crates' tests): the
  SECOND FRONTEND — the Python-subset (the int-arith/ifs/while/calls)
  compiles to `Wat.Instr` with ZERO new constructors (the type-check =
  the proof: the test-file cannot name a new one!) — the IR-seam's
  neutrality = by construction; the THREE-engine conformance (the
  Lean-parity theorems (native_decide-disclosed) + wasmtime + wasmi);
  the negative controls (the buggy mul→sub DIVERGES); the honest
  finding: the heap-layer = guestlang's concern (the scalars-frontend
  needs no alloc/RC — the runtime-splice = absent).
- **The warm-start LANED**: the hot-reload's state-migration = the
  EVENT-LOG REPLAY (the wasmtime-level memory-injection = rejected
  with vendored-source evidence: no component-level memory-escape);
  the carryover = the replay's (the calls-counter = 2 post-replay);
  the negative = the no-replay = the state-lost; the soundness =
  DEPENDS on the deterministic profile (the doctrine-tie!).
- The remaining = the RESEARCH-tail: the full translation-correctness
  (emitCode's totalization + the LCNF-source-semantics), the VExpr's
  variant-family's compiled-path, the audit's dataflow, the subprocess
  pool's IPC-hardening, the EdgePython's string/list-extension (the
  heap-layer's = the reuse!), Reservoir (excluded per owner), the CI's
  first real run (owner's secrets).

- **The parameterized backend LANED**: `lean/wasm-backend/project.json`
  (the spec-modules + the impl-modules = the manifest) → `targetDeclsOf
  env` = the GUEST-MARK registry fold (`guestMarkExt` — a new
  CodegenCore extension: the def joins when `@[guest]`/`@[guest_std]`
  passes — the mark = the compile-root's contract; the std intrinsics
  excluded via `stdOp?`); the exports = the registry-`body` filter over
  the folded roots; the 31-entry hand-list DELETED; the internals ride
  the same mark. The scaffold writes `project.json` (the template
  gains it); the follow-up #3 = "DONE by the manifest".
- **The front-door LANED**: the root README = the template's pitch (the
  two-modules-you-write story, the 30-second quickstart, the
  HONESTLY-labeled three-tier proof story (the proven/tested/checked —
  the engines' semantics = empirical, the Talos line = the open
  frontier, unclaimed), the ASCII architecture, the repo map, the
  status-box). Every claim cross-checked against the notes/the sources.

- **The validators phase 2** (the variant-param validator
  `orderErrorValid` + the multi-field `userComplete` (strlen/tags) +
  the variantParam adapter + the goAlts BRANCH-JOIN bug fix + the
  host-pattern test (the validator gates the processing call; the
  refusal-counter asserted); the VExpr's variant/strlen extension =
  honestly skipped + documented.
- **The splicer phase 2**: watch-counts THROUGH the middleware (the
  ZERO-COPY handle pass-through — the naive pump DEADLOCKS: a WASI 0.3
  stream write blocks until the consumer attaches; the yield-dance =
  the demo's own trick, unavailable to wit-bindgen's async); the dead
  item-counter deleted (anti-ceremony); **the wire AUTH**: the opt-in
  per-stream token handshake (`serve_authed`, the constant-time
  compare, the refusal = the error-frame + the dead stream; 3 tests:
  the good/bad/absent; the frame protocol = public surface).
- **The worker pool LANED** (`guestlang-rt/pool.rs`, the Monty PATTERN
  not the crate): the thread-pool + the engine-level isolation (the
  per-job Engine/Store, the catch_unwind, the fuel = the budget, the
  Send+Sync = compile-pinned); the tests: the parallel jobs, the
  OutOfFuel/Trapped/BadModule × pool-survives, the capacity watermark
  negative control; the subprocess hard-isolation = the documented
  follow-up (a binary-crate companion).
- **The template scaffold LANED** (`template/` + `just new-project` /
  `new-project-clean` / `scaffold-test`): the copy+rename + the
  AUTO-registration (lean_pkgs + the packagePrefixes) + the manual
  follow-ups printed; the round-trip verified (scaffold → inventory →
  build → the axiom gate → clean); the env-traps documented (the
  gonzalgo rev-rewrite = the hardlink-seed; the lean_pkgs = the
  dir-names).
- **Talos-lite LANED**: `WasmBackend/Sem.lean` (the fragment's
  small-step semantics + the stack typing + `exec_typed` TYPE SAFETY
  proven, core-triple only; part 2's statement REPAIRED via the
  executable counterexample) + **`WasmBackend/Correct.lean`** (the
  translation-correctness: `spec_double_ok`/`spec_add_ok`/
  `tpl_add_ret_ok` PROVEN + the BUGGY-template's provable disagreement
  (`buggy_ne_spec`) + the backend's actual emitCode #guard'd against
  the Sem at build-time (double/adder shapes, lower→exec→42); the
  extraction-gap honest: emitCode = partial → the kernel-claims =
  impossible by construction (the #guard = the right tool); the i64add
  Sem-ctor added (the model's gap).
- **The WAT region-audit LANED** (`WasmBackend/Audit.lean` — the
  provenance walk over the typed AST: the stores' pointer-provenance
  (alloc/const/load-chain/param/opaque; fail-closed on raw); 20
  #guard controls incl. the clobber-class negatives; the full
  dataflow (the ranges/loops/interprocedural) = the documented
  follow-up.
- **The session-typed payload layer LANED** (the honest diff: the
  schema-tie already existed as the bridge; the REAL gap = the
  Machines' string-binding + the schema-lang's DUPLICATED duality):
  the GENERIC payload-typed `TProtocol P` in Machines (the type-param;
  no cycle) + `tdual`/`tdual_payload_mirror`/`tsession_mid_deadlockFree`
  + the `IsDualOf` class (the mismatched peer = the ELABORATION error,
  #guard_msgs-pinned, the positive control non-vacuous); the
  per-WIT-interface skeleton emission = the remaining (schema-lang-side).

- **@[invariant] validators LANED**: the RECORD-PARAM adapter landed
  (the corrected ABI fact: records ≤ 16 flat params cross FLAT, not by
  pointer — the adapter = the flat→guest-object reconstruction, the
  strings = alloc(16+len)+{tag=250,len@8,copy@16}, the tags = the
  backward cons-walk); `GuestImpl.userValid` = the first validator
  (the duel rows: the VALID = true, the id=0 = false — the negative
  rows = the point); the wasm_diff's arg-builder handles the
  Val::Record args.
- **raw → 0**: the general-path WAT emission = FULLY TYPED (the
  emitCode/emitLet/emitCases/goAlts all on the Wat.Instr AST; the only
  raw = the ;;RUNTIME-SPLICE module marker, by design). En route: the
  sproj emitter's slot-index discard FIXED (the latent wrong-offset
  bug: User.id read at 8 instead of 32 — the first slot-3 scalar
  reader would have broken).
- **Talos-lite LANED** (`WasmBackend/Sem.lean`): the fragment's
  small-step semantics + the stack typing + **`exec_typed` (TYPE
  SAFETY: the well-typed programs never stack-underflow — proved,
  core-triple only!)**; the statement REPAIR: part 2 was FALSE as
  written (the executable counterexample — the missing
  `checkStack locals base is = .ok final` hypothesis added); the
  negative controls: the underflow/OOB-trap/drop + the typing
  rejections. Wired: the WasmBackend.lean imports Sem; the Axioms.lean
  pins both theorems.
- **The splicer middleware LANED** (`crates/splicer-mw`): the REAL
  interposed component (the counting wrapper: the AtomicU64 counters +
  the inner-forward, the wit-bindgen guest); the wac composition
  (the demo's exports feed the middleware's imports; the composed =
  the 3 exports); the guestlang-host test: the calls through the
  interposer (the double 21→42, the calls 0→1→2→3), the spans =
  the spec's manifest (the `calls` export = NOT spanned — the host
  can't invent a span!); `just splicer-mw` = the standalone gate.
- The dbsp quality pass = PREVIOUS round (the vacuous theorem deleted,
  the executable delta layer + the negative control, the LocDisjoint →
  List.Disjoint, the tautologous test fixed).

- **substrait DEMOTED from the core**: `EqAns` lifted into
  `SchemaLang.Ty` (verbatim shape, the provenance noted); `Bridge` =
  opt-in (out of the umbrella; its tests import it directly) — the
  schema-lang CORE (the umbrella's closure) = substrait-free; substrait
  = the opt-in expression layer.
- **The observability seam (the fast-observe LEAN manifestation)**:
  `SchemaLang.Observe` (spanName/spanFields = the spec-side functions)
  + the wasm-gen emits `src/observability_generated.rs` (the span
  table = the world fold's twin — ONE writer); guestlang-host's `call`
  path spans EXACTLY the spec's declared exports (the lookup in the
  generated table; an unregistered fn = no span — the coverage = the
  registry by construction); the control test pins the span's name +
  the delivery tag (the spec's contract, not the host's guess). The
  emitters' headers = COMPACT (2 lines: the tool + the lean version +
  the timestamp + the spec sha + the dirty flag + the item count + the
  content hash); `gen-check`/`OciStore::verify` = the CONTENT-only
  (the header stripped from both sides — the wall-clock is byte-tie-
  safe); the emitters stay pure (the meta = the driver's IO).
  TRAP: `meta` = a Lean KEYWORD (the meta-def modifier) — never a
  binder name.
- **The IDIOMACY round (the string-template codegen → the machinery)**:
  (a) the WIT/Observe emitters → `Std.Format` (BYTE-IDENTICAL output —
  the 15-artifact dump-diff evidence; the signatures String-preserving
  for the callers); (b) **the typed WAT AST** (`WasmBackend/Wat.lean`:
  the Instr/Func/Module + the Format render — the adapters = FULLY
  typed (0 raw; the element offsets = structurally `Layout.offsets`);
  the general path = the raw-bridged (1657 raw, counted + printed by
  wasm-gen — the honest ledger); en route: a REAL BUG fixed
  (`emitModule` never wrote its state back — the state read was
  vacuously empty); (c) the dbsp/Machines quality pass: a VACUOUS
  theorem deleted (replica_consistent), the executable delta layer
  added (500 seeded instances + the negative control CAUGHT), the
  LocDisjoint → mathlib's List.Disjoint, a tautologous session test
  fixed; (d) `fnv1a` deleted (core's `String.hash` — the same
  guarantee, zero code); (e) `notes/reuse-map.md` = the FULL
  package/module inventory + the reuse stories + the instantiation
  checklist (the template's value = the layers; the new project = the
  spec + the impls only).
- **The validators phase 2 LANED**: `orderErrorValid` (the
  VARIANT-param validator — the variantParam adapter emits
  `[i32,i64]→[i32]` re-box; empty-cart → false, documented), 
  `userComplete` (the strlen/tags multi-field via the new
  `listLenU64`); the duel rows = the valid AND the invalid samples;
  the host-pattern test (the validator GATES the processing call —
  the refused row never reaches get-user); a REAL branch-join bug
  fixed en route (goAlts typed the wasm `if` from the FIRST alt only —
  the bare-return vs the nested-case arms = the i32/i64 mismatch).
  The VExpr's variant/strlen extension = honestly SKIPPED (the
  second indexed-expr family + the acyclic-edge problem — documented).
- **The splicer phase 2 LANED**: watch-counts THROUGH the middleware
  = the ZERO-COPY handle pass-through (the naive pump DEADLOCKS — a
  WASI 0.3 stream write blocks until the consumer attaches, which
  happens only after the call returns; the demo's own module = the
  yield-dance, wit-bindgen's async fn cannot yield mid-body —
  documented); the item-counter = REMOVED (dead — the items flow
  host-to-host past the middleware; the calls-counter = the
  interposition evidence). **The wire AUTH**: the opt-in per-stream
  token handshake (`serve_authed`; the first frame = `{"auth":
  token}`; the constant-time compare; the wrong/absent = one error
  frame + the dead stream; no policy = the old behavior); the frame
  protocol (encode_frame/read_frame/encode_auth) = public (the
  integration tests + the external clients pin it); 3 auth tests
  (good/bad/absent).
- **The worker pool LANED** (`guestlang-rt/pool.rs`): the Monty
  PATTERN (not the crate!) — v1 = the thread-pool + the engine-level
  isolation (the per-job Engine/Store, the catch_unwind = the trap,
  the fuel = the deterministic budget/timeout-proxy; the `Engine:
  Send + Sync` = compile-time pinned); the tests: the parallel
  jobs, the OutOfFuel ×3 with the pool surviving, the Trapped ×3,
  BadModule, the capacity watermark (2 workers, never exceeded); the
  subprocess hard-isolation = the documented follow-up (needs a
  binary-crate companion).
- **The CI LANED** (`7e1efcc`): the two-lane workflow (the Lean
  matrix + the Rust/wasm devenv), the pinned toolchains, the
  assumptions in the header. The maintainer must set CACHIX_AUTH_TOKEN
  + verify the wac pin.

- **The wasmi 2.0 profile, ENFORCED**: guestlang-rt's config = the
  closed instruction universe (floats/memory64/multi-memory/wide-arith/
  custom-page-sizes OFF at the config; simd absent at the crate level;
  LazyTranslation pinned — `Lazy` is the mode that may diverge across
  implementations). Negative control: a hand-encoded f64 module is
  refused at load. The engine's feature set = the runtime mirror of
  the spec's closed Ty universe.
- **The Lean-authority fuzz**: the oracle program grew an LCG
  supplement (200 random rows, the RNG + the expected evals IN LEAN) —
  the manifest = 440 rows, both engines replay it, the scalar subset
  crosses the u64-wrap boundary.
- **The provenance gate**: `forge pull` refuses unchecked/absent axiom
  reports (--allow-unchecked = the hatch); the provenance sidecar
  travels with the artifact; the roundtrip test pins refused/allowed/
  clean-pass.

- **The seam round (all four recommendations landed)**: (1) watch-users
  FIXED — TWO root causes: the listUser/streamUser element stores'
  hand offsets all landed at +0/+4 (the id clobbered; the typed
  "green" test loads the WIT-BINDGEN guest, not the compiled module —
  the compiled list<user> lowering was NEVER host-validated until the
  watch-users rows), and listWalkWat's areaOff=0 scratch (ptr,len)
  write landed on the NEXT bump allocation (element 1's tags array).
  The scratch store is DELETED (areaOff=0 = no memory write); the
  field offsets come from the PROVED layout. (2) **`WasmBackend/
  Layout.lean` — THE PROOF**: `offsets`/`size` (the canonical-ABI flat
  record layout) + `go_pairwise` (the offsets strictly increasing = no
  field overlap) + `go_ge` + the rfl pins (`user_offsets` = [0,8,16,24],
  `user_size` = 32) — the adapters emit FROM the proved function.
  (3) The FOLD: `worldExportsOf` = the registry join (targetDecls ∩
  the @[schema_fn] items VIA `FuncSig.body`); `wireNames` DELETED (the
  impls renamed so kebab-of-leaf IS the mapping); `FuncSem.delivery`
  (once|stream — the snapshot sem-line serializes it; the attr args
  gained the stream/once axis); the world WIT = `worldWitOf` over the
  folded rows (demo-world.wit: reorder-only byte diff, wit-parser +
  embed + the 240-row duel green). (4) OCI provenance = already in the
  mesh commit (push --axiom-report --lean-version).
- The register-the-world-fns sweep left ONE gap: `total`'s world
  export folds correctly, but the REGISTRATION-TIME universeCheck
  doesn't run over the DemoFn/GuestlangStd union (the wit-parser gate
  + the duel cover it — the check-schema gate stays Demo-only).
- **wasmi 2.0 consumed and proved (this round)**: the engine-duel now
  replays the SCALAR subset of the Lean-authority oracle manifest
  (~140 rows) under wasmi — same manifest guestlang-host replays under
  wasmtime, one authority, two engines; `invoke_core` coerces i64 args
  to the export's param types (the pick-bool I32 via introspection, no
  per-fn table); `invoke_core_fueled` exposes consumed fuel and the
  STABLE-FUEL pin (wasmi 2.0's guarantee) makes upstream fuel-
  accounting changes gate failures; the async-boundary trap has its
  own negative control (watch-counts/watch-users MUST trap loudly);
  the manifest partition (scalar-duel vs component-only) is an
  exhaustive ratchet — a new demo export must be classified.
- wasmi 3.0 roadmap (function-references / exception-handling / gc):
  watch only — the guestlang boundary needs none of it; the
  deterministic profile has no wasm-tools CLI flag yet (checked), so
  cross-engine determinism stays enforced by the duel, not a validator.
- The `body : Name` seam (FuncSig, auto-filled by `@[schema_fn]`) is
  live but UNCONSUMED: the wasm oracle still hand-mirrors rows in
  GenMain — folding `worldExports`/oracle rows from items is the drift
  killer, when the wasm-backend owner is ready.
- Deferred: migration attribute-registry (v1 = the
  `Demo.registeredMigrations` list; attribute version when a second
  consumer appears); `volatileInPureContext` firing (no pure-context
  role exists in the item algebra — honest deferral).

DONE in the triage round: dupDefBodies skips reducible decls (abbrevs);
packageNamespace is the foreign-namespace rule (core roots + other
package roots; local-namespace + local-type-ownership + unprefixed all
pass; strict mode retained behind an option, default off); schema-lang
tests no longer import LSpec directly; Demo's `Async.Stream := Future`
(marker dedup); probeDefaultFn re-signed so the attr probes aren't
dup-body; GateKit gained `AuditRule`/`auditFindings`/`audit` with
TestKit controls + the deltaWit exemplar; the two new unusedVariables in
the user's WasmBackend trampoline code prefixed per the linter's own
hint.

LANDED earlier this session: 4.4 (`declare_binop` — `@[command_elab]`
handler in Substrait/Typed/Binop.lean; 8 op pairs → table entries;
hygiene lessons in the module header), warning hygiene sweep (75 core-
linter warnings fixed, 0 false positives; substrait/Machines/schema-lang
warning-clean), 6.5.1 (FuncSem/NullSem/Determinism on fn items +
`@[schema_fn strict.volatile]` attr syntax + Snapshot round-trip),
6.5.2 (SchemaLang/Migration.lean — FieldMigration/Migration/
CompatVerdict clean|remedied|unremedied, exit codes 0/2/1,
widenU32U64_sound axiom-free), 6.x LintKit package (axiomAllowlist,
dupDefBodies, packageNamespace, noLinterDisable, testImportDiscipline
default-ON; recursiveSimpEqns default-OFF — 83-hit census dominated by
doctrine-§8 raw-equation parsers; census command in the justfile
comment). `just gates` now includes lean-pkg-inventory + lean-lint.

Wave-5 additions LANDED + gate-verified: 3.1 (substrait axiom gate 1→23),
3.5 (wellFormed asserted over every emitted dtype + negative controls;
byteWidth wired with axiom-free `byteWidth_pos`; engineName pinned
injectivity — no Rust-side names exist to tie yet), 3.6 (`Ty.eqViaAns` +
`eqViaAns_beq`; Diff field comparison genuinely eqAns-routed; required
ReflBEq/LawfulBEq Ty instances), 3.7 (`check-schema`/`breaking` wired via
SchemaLang/Snapshot.lean + schema-check/schema-breaking exes, both in
`gates:`; sabotage-tested), lean-pkg-inventory gate (`std` was missing
from lean_pkgs — caught exactly the drift class; all 9 packages now
gated), 5.3 (substrait expression PropSpec ×3 controls; schema-lang
Ty/Item generators + universeCheck PropSpec + coverage witnesses — caught
a real generator starvation bug), 5.5.2 (CertifiedEmitter in codegen-core),
5.5.3 (TestKit.DiffSpec — Corruption/DiffSpec/runDiffs; ADOPTED by the
wasm differential oracle: sabotaged fn-name/arity rows must fail with
context), 5.5.4 (dbsp/Dbsp/Effects.lean DeltaSystem via core
List.Perm.pairwise + pointDeltaSystem demo instance).

## Phase 6.5 — flatland-notes transfers (2026-09-09 mining, 19 files)

Doc-tier transfers LANDED in lean-doctrine.md §8 (enforcement ladder,
design rules, discharge ladder, differential-testing doctrine). Code-tier
items:

| # | Item | Where | Status |
|---|---|---|---|
| 6.5.1 | Fn-registry items carry `nullSem : strict \| propagate \| custom` + `determinism : pure \| stable \| volatile` + `body : Name` (mandatory executable Lean semantics — "unsigned code doesn't ship") as DATA; `volatile` in a fold/reorder context fails universeCheck | schema-lang `@[schema_fn]` items + emitters + oracle | TO DO |
| 6.5.2 | Migration soundness for schema evolution: migration = total fn old-values → new-values + theorem `replay ∘ migrate ≡ migrate ∘ replay` on preserved columns; the breaking-gate detects, this is the REMEDY story (event-sourcing upcasting) | schema-lang Diff/Snapshot — optional `migrate` payload on compatible-with-migration verdicts | TO DO |
| 6.5.3 | Emitter-output self-audit: emitters ship grep/lint audits of their OWN generated text (banned patterns fail CI) — GuestGate bans constructs in guest SOURCE; this audits EMITTED artifacts | GateKit recipe + one audit per emitter, wired into gates | TO DO |
| 6.5.4 | Extra lint rules folded into LintKit scope (steered mid-run): simp-normal-form duplicates, simp-set members listed by hand, linter-disable justification, unused-exported-structure census (report-only), Tests-never-import-LSpec | LintKit | IN FLIGHT |
| 6.5.5 | Deferred tooling notes: Reservoir criteria (public repo, root lake-manifest, OSI license), lean-action CI eligibility check, gonzalgo per-package TSV → TestKit `--affected` (run only suites depending on changed decls) | notes/full-remaining-work.md append | TO DO (notes only) |

Explicitly NOT transferred (verified superseded or flatland-specific):
Lake-facet codegen (driver-exe + byte-tie is simpler and host-language-
agnostic), lentil liveness vocabulary (lrw removed Machines.Live as dead),
Lean-zh/protobuf wire (Codec.lean covers binary in-house), cslib, PHOAS/
graded monads, all game/engine semantics.

## Phase 6 — enforcement (linters), wired into `just gates`

### Phase 6 handoff note (2026-09-09): LintKit gate is RED — 3 triage fixes

The linters work (they caught real findings on first run) but need
false-positive fixes before `just gates` goes green. Diagnosed precisely:

1. **`dupDefBodies` must skip reducible decls (abbrevs).** Fires on
   deliberate transparent aliases: `Vortex/DType.lean:94-121`
   (`FieldName`/`ExtId` = String; `StructFields`/`UnionVariants` = same
   List type) and `Demo.lean:60-62` (`Async.Future`/`Async.Stream` —
   marker types whose body-equality is the POINT; the reifier matches the
   qualified names). Fix in `LintKit/DupDefBodies.lean` `computeModuleDups`:
   skip decls where `getReducibilityStatus env decl == .reducible`.
   Consider also skipping theorems (proof irrelevance makes dup-proof
   clusters noise). Add a fixture: two abbrevs with identical bodies must
   NOT fire; two `def`s with identical bodies must.
2. **`packageNamespace` must become the foreign-namespace rule.** Current
   rule (module root → expected prefix) fires on every unprefixed local
   decl: Demo.lean's domain types (`User`, `Order`, …) and SchemaLang's
   top-level `witEmitter`/`changeSpecEmitter`. The doctrine's actual
   hazard (flatland's `Fin.ofList?` — a helper parked in CORE's `Fin`
   namespace) is FOREIGN namespaces. Revised rule: flag a decl only when
   its first name component belongs to another workspace package's prefix
   OR to core/Lean (`Lean`, `Init`, `Std`, `Fin`, `List`, `String`,
   `Option`, `Array`, `IO`, …) while the declaring module's root differs.
   Unprefixed and own-package decls pass. Keep the strict prefix rule
   behind the existing option (default off). Result: current tree clean,
   real leaks still caught. Update `LintKit/TestFixtures/Violations.lean`
   to plant a foreign-namespace decl (e.g. `def List.myHelper` in a
   LintKit test module) and assert it fires; assert unprefixed local decls
   don't.
3. **`testImportDiscipline` fired on schema-lang/Tests/Main.lean:11**
   (`import LSpec` directly). Try deleting the import — if the build
   fails, the file uses LSpec identifiers TestKit doesn't re-export;
   extend TestKit.lean's re-export surface (`export LSpec (…)`) rather
   than nolinting.

After fixes: rebuild LintKit, re-run `just lean-lint` (must be clean
package-by-package), then full `devenv shell --profile wasm -- bash -c
'export CC=$HOME/lean-rust-wasm/.devenv/profiles/wasm/profile/bin/cc; just
gates'` (the CC export is REQUIRED — the new noq/ring dep needs the wasm
profile's clang headers; without it gen-check fails in cc-rs on ring).

| # | Rule | Mechanism |
|---|---|---|
| 6.1 | Axiom allowlist as env-linter over EVERY package decl (`Lean.Util.CollectAxioms`), replacing hand-maintained `#print axioms` lists | env-linter (`Lean.Linter.EnvLinter` ships in v4.33 core) — strict coverage upgrade |
| 6.2 | Recursive defs ship `@[simp]` equation sets | env: `getEqnsFor?` + `isRecursiveDefinition` |
| 6.3 | Duplicate def bodies / defeq theorem statements within a package | env: cluster `ConstantInfo.value` |
| 6.4 | ≥3 consecutive theorems sharing binder telescopes → suggest `variable` | syntax-linter |
| 6.5 | Identical token-normalized `by`-blocks at ≥2 sites | syntax-linter |
| 6.6 | Package-namespace prefix on decls | env-linter |
| 6.7 | Core linters ON for library targets (`missingDocs`, `unusedSimpArgs`, `unreachableTactic`, `dupNamespace`, `deprecated`); Tests exempt via `weakLeanArgs` | lakefile `leanArgs` |
| 6.8 | `just lean-lint` in `just gates`; existing violations grandfathered via `@[builtin_nolint]` — ratchet, not flag day | justfile |
| 6.9 | Package-inventory check: every lean/ dir with a lakefile appears in `lean_pkgs` | justfile one-liner |

## Phase 5.5 — ports from the flatland lineage (2026-09-09 port study)

The flatland repo grew three packages this tree lacks. Full study in the
session transcript; ranked port list:

| # | Pattern | Destination | Verdict |
|---|---|---|---|
| 5.5.1 | **Binary codec combinators + `++ rest` round-trip lemmas** — self-delimiting fields, partial decode, lemmas in `dec (enc a ++ rest) = some (a, rest)` form so per-field lemmas compose into whole-structure round-trips by `simp` alone. Evidence: flatland `Flatland/RecipeWire.lean:58,84,127` (decOpt/decProd/decList), `Lifecycle.lean:333` (varint base), payoff `recipe_decode_encode` at :523 | extend `schema-lang/SchemaLang/Codec.lean` (currently Bool+UInt8 only) with `encVarNat/decVarNat` + generic `encOpt/encProd/encList/encEnum` and their append-form lemmas | **PORT — highest value.** Fills the template's biggest hole: no proved binary wire story (text+WIT only today). Zero game content in this layer |
| 5.5.2 | **Proof-carrying emission** — the emitter takes the discharged proof term of the law over the CONCRETE spec data, so the artifact is unemittable if the law fails on it. Evidence: flatland `Tests/SpawnGate.lean:45,93-95` ("the artifact is false if we proved it wrong") | codegen-core Emitter discipline convention: emitters for law-governed data take the proof term | **PORT** — strictly stronger than byte-tie alone (reproducible ≠ correct); cheap |
| 5.5.3 | **Corruption-negative gate discipline** — differential gates ship ≥2 engineered corruptions that MUST fail, and the error must name context. Evidence: flatland `Tests/ReplayGate.lean:50-77`. lrw enforces this for plausible sweeps (PropSpec) but NOT for golden/differential gates — the wasm differential smoke has only positive invokes | TestKit: documented gate-exe recipe (standalone import set + positive golden + named negatives) + one demo | **PORT the discipline** |
| 5.5.4 | **`DeltaSystem` influence algebra** — static write sets; `disjoint_commutes` contract; derived `applySeq_perm` (pairwise-disjoint batch = any permutation). Different claim from Replicas (group-commutes vs disjoint-write-commutes; works for non-commutative mutations). Evidence: flatland `Flatland/Effects.lean:40-56,140` | new module `dbsp/Dbsp/Effects.lean` — port the class + ONE demo instance (flatland only ever instantiated it once) | **PORT (medium)** |
| 5.5.5 | Rust→Lean generated mirror (inventory + opaque placeholders + rev-pinned header) | future `mirror` direction in codegen-core | **DEFER** until a host hand-owns Rust types the Lean oracle must consume |
| 5.5.6 | Encoding-erasure law structure (`read∘encode=id`, lossy exemplars explicitly excluded) | schema-lang Vortex layer | **DEFER** until Vortex lowering gains encodings |
| 5.5.7 | Versioned-envelope convention (`version + schemaFingerprint + edition` as first wire fields) | codec/emitter header convention — cheap, adopt with 5.5.1 | **PORT (with 5.5.1)** |
| — | flatland Codegen Registry, DidYouMean, ChangeSpec→trait, KernelSem differential | — | **SKIP** — lrw's versions are strictly newer/better factored |

## Line-count ledger (audit estimates)

| Phase | Net |
|---|---|
| 0 bugs | ~0 (behavior fixes + tests) |
| 1-2 structural/dedup | ~150 removed + drift channels closed |
| 4 lifted-package sweep | ~600 removed (substrait ~400, dbsp ~120, Machines ~80) |
| 5 TestKit | ~100 removed from test files + the framework default exists |
| 6 linters | the patterns stay fixed without review effort |

Sequencing note: Phase 0 and 2.1 are the only items touching behavior or
build graphs — land them first, each with `just gates` green. Phases 4.1's
Decode refactor is the largest single win; do it after the smaller
substrait items so the equation-lemma consumers are understood before the
recursor skeleton gets factored.

## The DOGFOOD (2026-09-13): `ledger` — the template's first consumer

`just new-project ledger` → a real spec (the Ledger record with
4 fields; ledger_get/ledger_valid/deposit), the GuestImpl-pattern
impls (the strlen via the std-ops), the registry live (7 items), all
gates green with the ledger in the loop. THE FINDINGS — every one a
template fix:

1. **The greedy rename**: `.replace("thing", ...)` ate "anything" →
   "anyledger". Fixed: the longest-first regex chain (ThingFn/
   ThingImpl/ThingTests → the compounds; `thing_(?=[a-z])` → the
   prefix; `\bthing\b` → the standalone). THREE bugs in one line of
   scaffold code — the dogfood's entire value.
2. **The manifest's dependency-closure**: the template's
   lake-manifest = the faults'-era snapshot; a project requiring MORE
   (the std) = the hand-append (GuestlangStd/LintKit rows) + the
   gonzalgo rev-break = the local-copy fix (the .lake/packages/
   gonzalgo from a sibling's build — the fetch = the upstream
   rev-rewrite = broken for everyone). The template README documents
   it; the ROBUST fix = the vendored tarballs (follow-up).
3. **The axiom-gate's noise-filter**: the `batteries has local
   changes` warnings = parsed as the unexpected axioms. Fixed:
   `grep -vE "does not depend|^warning:|^info:"`.
4. **The compile-set's parameterization** = the template's REMAINING
   gap: the backend's targetDecls = the demo's hand-list — a new
   project's fns compile when appended there (the manual follow-up
   printed by the scaffold). The parameterized backend (the
   targetDecls = the project's manifest) = the next structural work.

## Phase 7 — idiom notes (2026-09-14 review waves)

| # | Action |
|---|---|
| 7.1 | **Termination-witness coupling (the `mutual` trap).** A `mutual` block whose members recurse through a sibling (e.g. `dtypeRust` ⇄ `fieldsItemsRust`, `SType.eqAns` ⇄ `eqListType`) proves termination via ONE member's structural recursion. A `map`/`intercalate` one-liner that erases the recursion either (a) fails the checker ("fail to show termination", see `eqListAns`) or (b) — moved out of the block — leaves the sibling with NO decreasing edge (see `fieldsItemsRust`). The two working idioms: KEEP the structural recursion inside the block (trimmed, documented), or pass the recursion AS A PARAMETER (the `callText` `rec`-style) when the helper legitimately belongs outside. A helper moved out of a mutual is not "cleaner" — it can silently kill a sibling's termination proof. |
| 7.2 | **`abbrev` vs `def` near proofs.** Reducible helpers (`litWithSuffix`) let the module's proof-rewrites (`rw [parseLiteral.eq_N]`) see through them; opaque `def`s force `simp [name, …]` at every site. When a helper is consumed by equation-rewrites in the SAME module, make it `abbrev` and say why (the `litWithSuffix` doc does). |
| 7.3 | **The parser-monad follow-up** (Decode.lean): monad + lexers landed; the `parseType` family needs a CASE-FIRST re-proof strategy (the do-threading hides the `eq_N` shapes the inversion theorems `rw`). Classic theses: keep the equation lemmas structurally CASE-FIRST (patterns before `>>=`), so `parseType.eq_*` keep their shapes. |

## Phase 8 — the VCase COMPILED lane (designed; scoped session — do NOT half-build)

The last spec/compiled duplication (Validate.lean Phase-3 decision): the
registered variant validator (`GuestImpl.orderErrorValid`) keeps a HAND
`match` while the spec form (`orderErrorSpecValid` + `evalCase`) rides
SPEC-LEVEL only. The raw lane needs:

1. **The scalar raw subject**: `OrderError → (tag : UInt32) × (payload : UInt64)` — the
   re-boxed canonical-ABI object's READ side (discr @4, joined i64 @8). The f64 arm's
   payload stays UNREAD (the join makes the slot non-scalar — the documented v1 stance).
2. **`caseTagPos : CaseTag n cs → Nat`** (`@[guest_std]`, the constructor-position path)
   — the tag-side complement of `ColPath.get`: at runtime = the backend's existing tag-case
   dispatch. Positions = the case LIST order (the demo's `orderErrorCases` mirrors the
   ctor order — this is the contract to pin in a test).
3. **`evalCaseU {cs} (tag : UInt32) (payload : UInt64) : VCase cs .bool → Bool`**
   (`@[guest_std]`) — the `evalB` twin over the variant family: `isCase` → `tag ==
   caseTagPos`; `payload` → the u64 sproj (guarded by `caseTagPos`); `gt`/`and`/`not` →
   the `evalU` scalar spine. NO `Value` boxes constructed — the reset/reuse-pass rule.
   BACKEND GAP to close: the wasm-gen must compile `caseTagPos`/`evalCaseU` as ordinary
   targets (they are plain tag cases + sprojs — the shapes already emitted for
   `orderErrorValid`'s match) — the `VCase`/`CasePath` typeclass fields must elaborate
   as DATA (the existing `ColPath` discipline) — verify `evalCaseU`'s LCNF has no
   dictionary tails before marking `@[guest_std]`.
4. **The wired export**: the `variantParam` adapter feeds `(discr, payload)` DIRECTLY to a
   raw impl (`order-error-valid` → `evalCaseU orderErrorSpecValid`), dropping the RE-BOX
   for this shape — then `orderErrorValid` becomes `def orderErrorValid e :=
   evalCaseU e.tag e.payload orderErrorSpecValid`-derived and the hand match is gone.
5. **Pins**: the schema-lang eval tests extended to `evalCaseU` vs `evalCase` agreement
   over the demo rows (the differential duel rows stay the authority); the guard "the
   case list ORDER is the ctor order" pinned as its own test.

The demo row set is small enough that (2)-(4) land in one backend session; the design
decision to re-verify first = (3)'s "no dictionary tails" claim — probe the LCNF of a
minimal `@[guest_std] def probe (cs) (t : UInt32) (p : UInt64) : VCase cs .bool → Bool`
BEFORE writing the emitter support.

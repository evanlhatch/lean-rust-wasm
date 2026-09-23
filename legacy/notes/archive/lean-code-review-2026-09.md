# Lean code review 2026-09 — DRY / elegance pass

Scope: every hand-written Lean module in `lean/` (10 packages, ~31K lines —
LintKit, TestKit, Machines, codegen-core, substrait, schema-lang, faults,
dbsp, std, wasm-backend, ledger). Method: full-file reads of the emitter/
backend layer + parallel scans of the mathlib-backed packages, then
individually verified and applied (build + `lake exe <Pkg>Tests` per
package; wasm-compile gate for the backend).

State at review time: TestKit / Machines / codegen-core / substrait /
schema-lang / dbsp all build and test green with the applied changes.
faults / std / wasm-backend / ledger are mid-flight under the parallel
"middleware + wire auth + hot-reload" lane (their builds fail on THAT
lane's in-flight files — Sem.lean +467 lines, Item.lean churn) — the
reviews below for those packages are read-only; the applied backend edits
were verified green earlier in the session (wasm-compile gate, byte-tied
output).

---

## APPLIED (verified — statement-preserving, byte-neutral where emitting)

### wasm-backend
1. **`emitModule` computed the identical `sigs` fold twice.** The second
   copy ("Trampoline signatures" label) was a byte-identical re-fold;
   `sigs` is immutable between them. Deleted the duplicate.
   `WasmBackend.lean` (~1030-1050).
2. **`goAltsRaw` / `goAlts` — one alt-chain walk written twice.** The two
   differed only in the scrutinee local's name (`value` vs `tag`). Merged
   into one `goAlts (scrut : String)`; both call sites pass their local.
   `WasmBackend.lean` (~277-308).
3. **The variant re-box, two verbatim copies** (`variantParam`,
   `listUser`'s local `variantBox`). Extracted `variantBox (disc payload)`
   next to `stringCtor`/`consChain`/`pairRel`. `WasmBackend.lean`.
4. **The user-record type list `[.u64,.string,.string,.list .string]`
   written 6×** (Layout.lean ×2 pins, Audit.lean stride, WasmBackend.lean
   ×3). New `Layout.userTys` abbrev is the single source; the pins stay
   `rfl` through it.
5. **`Wat.instrW` duplicated all 16 flat arms of `Wat.lineOf`.** The
   renderer now routes every flat form through `lineOf` (the structural
   forms stay); deleted the dead `rawCountOf`/`Module.rawCount` (zero
   consumers — GenMain prints the emitter state's `S.rawCount`) and fixed
   the stale header claim that named `Module.rawCount`. Emitted WAT
   byte-identical (wasm-compile gate: differential smoke green).
6. **`GenMain.emitModuleWasm` dead first decl-collection loop** — the
   `decls` variable was built, reversed, and never read (`decls2` feeds
   the module). Deleted.

### codegen-core
7. **`checkGuest` / `checkGuestStd` — 34 duplicated lines** differing only
   in the ban level. One `checkGuestAt attrName level`; both attributes
   delegate (the level-pinned `reasons` lives in the shared body).
   Deleted the zero-consumer `banned?`/`bannedStd?` aliases (their only
   reference was the re-export list in wasm-backend/WasmBackend/Check.lean,
   updated).
8. **FNV-1a doc/label lie.** `GenMeta.contentHash` doc + the generated
   header's "content fnv1a" label said FNV-1a; the actual hash is
   `String.hash` (block comment already admitted it). Doc + label fixed
   (header text is byte-tie-stripped, so no artifact churn).

### TestKit
9. **The "run specs, print, count failures" driver loop, written three
   times** (`PropSpec.runSpecs`, `DetSpec.runDets`, `DiffSpec.runDiffs`).
   One generic `Harness.runVerdicts`; the three drivers are one-liners.

### schema-lang
10. **`SchemaLang.Observe` — dead module** (zero consumers; its claimed
    emitter never existed and the actual observability fold lives inline
    in wasm-backend GenMain). Deleted the module + its 2 imports.
11. **`Delta.lean`: the "keyed record?" test re-derived four times**
    (`changeTy`/`changeWitDecl`/`changeRustItems`/`changeTestItems` each
    matched the field list). New `Item.keyOf`; all four use it.
12. **`Migration.verdictOf` + `BreakingMain` both inlined the
    "anything-but-`.added`" filter.** New `Migration.breakingOf`; both use
    it.
13. **Test file re-defined `validatesCase` as `evalCaseBool`** (same
    namespace, same body). Deleted the copy; 4 call sites renamed.

### Machines
14. **The five change-structure classes + five `groupSelf` instances +
    `group_rollback` verbatim-copied from `Dbsp.ChangeSpec`** (~60 lines,
    the file's own TODO). Machines now requires dbsp and imports
    `Dbsp.ChangeSpec` (both mathlib-only, no cycle); LinearMachine keeps
    only its `patch`/`patch_zero` aliases + a `group_rollback` restatement.
    `lake update Dbsp` regenerated Machines + schema-lang manifests
    (schema-lang requires Machines transitively).

### substrait
15. **Dead typed-layer API deleted**: `litI64`, `litBool`, `oneArg`,
    `pushArg`, `noArgs` (Expr), `sortKey` (Rel), `Schema.width`,
    `Schema.types` (Schema) — all zero consumers.
16. **`Emit.Text.joinWidth` — dead alias** for `JoinType.width`; 2 call
    sites now call `r.joinType.width` directly (the decoder already did).
17. **`Emit.Text.measure` verbatim-restated `expr`'s `.scalarFunction`
    arm.** Shared `callText` (recursion passed in as a parameter so it can
    sit outside the recursive `expr` without a mutual block).
18. **`Decode.parseLiteral` repeated the suffix-map tail 4×.** `abbrev
    litWithSuffix` (reducible — the module's proof-rewrites must see
    through it; two `rw` lines adjusted accordingly).
19. **`Decode.parseExtensions` built the FnCtx twice + three identical
    declaration-block arms** differing only in kind number. `fnCtxOf`
    helper + `kindOf` table collapse the three arms to one.
20. **`ToProto.withNullable` — 28 bool-dispatch arms** (14 rebuild-pairs).
    `setNull` sets the nullability once per ctor; `withNullable` is the
    2-line dispatch.
21. **`schema-lang/Vortex/Emit.fieldsItemsRust` — hand recursion for a
    `map`+`intercalate`.** The one-liner is architecture-blocked: the
    helper is the `mutual` block's termination witness for `dtypeRust`,
    which the checker cannot see through a `map`-fold, so the fold must
    stay a structural list-recursion (see the documented comment in the
    file — this is the same class of constraint as the `eqListAns`
    termination fight).

### dbsp
22. **`Incremental`: the `del*_invariance` triple duplicated the
    `@[simp]` twins** (`delay_incremental`/`I_incremental`/`D_incremental`
    — same statements, zero consumers, not `@[simp]`). Deleted the
    `_invariance` triple + the zero-consumer `chain_incremental` (the
    consumed `incremental_comp` stays).

---

## REVIEWED, NOT APPLIED (with the reason)

23. **Machines.Session string↔typed duality** — the string layer's 6
    theorems + `dual` re-prove the generic `tdual` family (`TStep String
    = Step` definitionally). The scan agent's reduction is sound
    (statements become one-line aliases), but it rewrites ~150 proof
    lines on a theorem surface the schema-lang Session module consumes by
    name. HIGHEST remaining value; deferred because the Machines build is
    being churned by the parallel lane — apply when the tree is quiet.
24. **SchemaLang/Session.lean re-proves `tdual_types` /
    `typed_directions_oppose`** that `Machines.Session` already proves
    generically. Same deferral; delete the copies once 23 lands.
25. **substrait `relLines` — the ref-output + child-wrap clause in 3-4
    arms** (Filter/Sort/Fetch). Collapsing needs the recursion
    passed-through again (the `callText` dance); ~15 lines saved — noted,
    not chased.
26. **substrait `eqListType`/`eqListParam` — identical 11-line pair.** A
    generic `eqListAns` fails the mutual-block termination checker at
    both `def` and `abbrev` transparency (the SCC `eqAns ⇄ eqListType`
    loses its decreasing edge). Reverted; 22 lines left as-is.
27. **substrait `parseSepList` unification** (`parseTypeList` vs
    `parseExprList`) — proof-rippling (`parseType_mono`,
    `parseTypeList_invert`, `structT` state equations about the concrete
    parser). Mechanical but wider than the value; UNVERIFIED.
28. **substrait `typeTextBase`'s nine scalar arms through
    `ScalarCtor.ofPType`** — the inversion proofs make this risky;
    UNVERIFIED.
29. **substrait `aggInt`/`aggFloat` — same fold in two types**
    (sum/min/max/avg). The typeclass ceremony (`[OfNat][Add][LT][Div]`
    with different division) costs more than the 12 duplicated lines.
    Leave until a third numeric aggregate exists.
30. **`Dbsp.Tests` `applyDeltasInt` vs `Replicas.applyDeltas`** — same
    fold; unifying needs the `noncomputable` marker removed from
    `applyDeltas` (flag's load-bearing-ness UNVERIFIED).
31. **~40 zero-consumer declarations** (dbsp NestedCycle/StreamElim/
    Relational/ZSet/Linear dead vocabulary; Machines `Iso`/`PartialIso`/
    `Refines`; Incremental's inversion/bijection cluster, `I_push`/
    `D_push`/`D_push2`/`add_incremental`). Several are documented "engine
    rewrite licenses" for external flatland consumers — verify against the
    external surface before deleting. The safe subset (the `_invariance`
    triple, `chain_incremental`) went in (see 22).

---

## Deliberate duplication (checked, LEAVE ALONE)

- **Ty→string spellings in Wit/Rust/Snapshot/flatTyOf** — independent
  artifact contracts; the bytes must not drift together.
- **`EqAns` in SchemaLang.Ty vs Substrait.Typed.Schema** — cross-package;
  the Bridge module pins their agreement.
- **Emitter↔decoder name tables** (joinTypeName vs joinTypeOfName, …) —
  mirror-image by design, separate error handling.
- **`CertifiedEmitter` restating `Emitter` metadata** — the documented
  registry-audit convention.
- **GenMain.oracleSrc vs the Oracle module** — byte-compat invariant,
  documented.

---

## Gate status (this review's changes)

- lean-build / tests: TestKit 20 ✓, schema-lang 48 ✓, substrait 58 ✓,
  Machines 17 ✓, dbsp 7 ✓, codegen-core 4 ✓ — all 0 failures.
- wasm-compile: green (my emitter changes are byte-neutral; the demo.wat
  golden does not move).
- NOT re-runnable at review end: std / faults / wasm-backend / ledger —
  blocked by the parallel lane's in-flight build breaks (Sem.lean,
  Migration work), not by this pass.

---

## SECOND WAVE (2026-09, dispatched) — applied + verified

24. **Machines: `Machine.run_cons_some` / `Machine.step?_eq_some`** — the
    cons-inversion ladder (the same 12-line `simp only [run] at h; split
    at h; · contradiction; · …` dance) was copied into `run_preserves`,
    `run_length_le`, `run_sim`. Two inversion lemmas (mirroring
    `runLogged_cons_some`); the three sites are now `obtain … :=
    run_cons_some m h; subst` (and `step?_eq_some` gives the guard
    directly — the dead guard-false branch disappears). Statements
    byte-identical; MachinesTests 17/17.
25. **dbsp: `agreeUpto` → `agree_upto`** — one concept, two spellings in
    one package (`agreeUpto` camel def vs `agree_upto_0` snake theorems
    vs `agree_upto2` row-wise sibling). Pure identifier rename, 53
    tokens across 5 files; `agree_upto2` untouched; DbspTests 7/7.
26. **substrait: namespace/path hygiene** — the Grammar module was
    double-nested (`Substrait/Substrait/Grammar.lean` declaring
    `namespace Substrait.Substrait`, referenced via fragile prefix-trim
    `Substrait.ScalarCtor`). Moved to `Substrait/Grammar.lean` +
    `namespace Substrait.Grammar`, all refs become `open …` short names
    (program text unchanged). Decoder's stray `.Text` layer
    (`Substrait.Decode.Text`) now matches its path (`Substrait.Decode`).
    Grep sweep: 0 strays. SubstraitTests 58/58.
27. **TestKit discipline**: sole direct-LSpec usage in Tests code found in
    dbsp's main (`LSpec.lspecIO` → `TestKit.mainOfSuites`); everything
    else already compliant (the text linter's report). Audit table of all
    21 Tests files is in the agent transcript; substrait's `runChecks`
    noted as a `CheckM` adoption candidate.
28. **faults/GenMain** now uses `CodegenCore.Emit.writeFileCreatingDirs`
    (the shared driver write path) instead of re-implementing
    parent-dir creation. Builds green.
29. **codegen-core header pin fixed** — my "content fnv1a" → "content
    hash" label change had drifted the `headerCheck` pin; updated to
    `"content hash {…}"`. CodegenCoreTests 4/4.

## SECOND WAVE — roadmap (grounded, not yet applied)

- **Decode.lean parser monad.** 17+ `List Char → Option (α × List Char)`
  signatures, 7 explicit `fuel : Nat` params, 23 top-level parse defs.
  A 10-line `Parser` (`StateT (List Char) Option`) + primitives
  (expect/scanNat/takeWhile) turns the parsers into do-blocks and kills
  the fuel threading; the decode∘emit round-trip sweeps (58 checks) are
  the safety net. Largest idiomatic win remaining; a session-sized
  refactor, not a diff.
- **observability_generated.rs is byte-tie-less.** It IS committed
  (`git ls-files` shows it) and included by steel-host, but no
  just/forge gate regenerates-and-compares it (forgeJobs only covers
  schema-lang's registry emitters). Add a regen-verify step to
  `just wasm-compile` when the hot-reload lane lands.
- **CertifiedEmitter stays a demo.** Wire the discharged-proof pattern
  for real: `emitAdapter` already reads `Layout.offsets` — make the
  stream/list adapters consume the PROOF (`offsets userTys = …`) so a
  layout change without a re-proof fails elaboration, not CI.
- **VCase compiled lane** (schema-lang.Validate Phase 3 is spec-only):
  when the backend emits the discr+joined-payload raw evaluator,
  `GuestImpl.orderErrorValid`'s hand `match` authority merges with
  `orderErrorSpecValid` — the one remaining spec/compiled duplication.
- **LintKit: cross-module dupDefBodies** (package-scoped flag) — would
  have caught the six userTys-literal-class copies; per-module default
  stays. Also: a v4.33 no-`unusedImports`-linter gap means unused
  imports are uncheckable without writing that linter — candidate LintKit
  extension (needs per-import usage tracking).
- **TestKit: `export LSpec (TestSeq, …)`** so Tests files can drop
  `open LSpec`; adopt `CheckM` in substrait's runChecks.

---

## THIRD WAVE (2026-09, dispatched + direct) — applied + verified

30. **Machines.Session string↔typed DUALITY** — the string layer (6
    theorems + `dual`) re-proved the generic typed core; now `dual :=
    tdual (P := String)` and every string theorem delegates
    (`flip_step`/`dual_dual`/`dual_map_payload`/`dual_length`/
    `dual_payload_mirror` → their `tdual_*` twins), and the two
    variant theorems share one `pos_variant_decreases` lemma. The
    typed core moved above the string layer (its only dependency is
    `Dir.flip`); `Dir.flip_ne` hoisted with it. MachineryTests 24/24.
31. **SchemaLang/Session re-proofs eliminated** — local `tdual_types`/
    `typed_directions_oppose` were re-proving the generic theorems at
    `P := Ty`; now `simpa [tdual]`/`unfold tdual` delegates. The
    bridge (`tdual_toWire`) still carries the schema-side content.
32. **TestKit `export LSpec (TestSeq test checkPlausibleIO)`** — all
    Tests files dropped `open LSpec`/`import LSpec` (zero direct LSpec
    outside TestKit internals; the export parser is space-separated in
    v4.33).
33. **New DetSpec suites** (each with mandatory negatives): codegen-core
    mangler inverse laws over a corpus (`words∘camel`, `camel∘snake`,
    `kebab = snake.replace`, `rootRel`, `jsonStr`, `rustIdent` — the
    agent hand-traced `words` first); schema-lang `breakingOf`/
    `changeTypeName`/`keyOf`/`changeTy`/`changeWitDecl` pins; Machines
    doubler incremental-agreement corpus sweep (s₀×δ×trace grid, the
    δ·2 sabotaged chain as the control).
34. **Decode.parser monad — PARTIAL (data, per protocol)**: `Parser`
    monad + `result/bind/fail/peek/rest/jump/consumeChar/takeWhile` +
    `scanIdent`/`scanName`/`scanNat`/`scanInt` converted to do-blocks;
    the `parseType` family + its inversion-proof layer fought the
    do-notation past 3 attempts and was REVERTED (the proofs `rw`
    parser equation lemmas that the do-threading obscures). The
    full-module conversion needs a case-first re-proof strategy —
    session-sized. 58/58 green either way.
35. **wasm-backend byte-tie + certified layout** (A9): `just
    wasm-compile` snapshots and strips+compares the regenerated
    observability surface (drift aborts; negative experiment
    verified). The stream/list/optionUser adapters now CONSUME the
    discharged `Layout.user_offsets`/`user_size` proofs (a layout
    change without re-proving the ABI table fails ELABORATION — the
    CertifiedEmitter discipline made real; negative experiment
    verified at the `rfl` pin). WAT byte-identical.
36. **Two real bugs fixed en route (A9)**: `stdOp?` now maps the
    schema-root `SchemaLang.string_len` (the WIP's `evalU` wiring
    emitted calls to an undefined func → WAT parse failed); `consChain`
    builds an ALLOCATED `{rc, tag=0}` nil block instead of a NULL
    accumulator (the nil-tail deref read allocator freelist bytes →
    220 differential failures).
37. **wire auth tests → candidate runner** — the lane's three auth
    tests hardcoded `127.0.0.1`, which hangs under WSL2 mirrored
    networking (the file's own running pattern uses the LOCALHOST →
    10.255.255.254 candidates). Converted to the candidate-loop shape;
    wire 14/14.

## Gate state (all after the third wave)

- lean-build 11/11; lean-axioms 11/11 clean; lean-lint clean WITH the
  new cross-module dupDefBodies.
- Tests: TestKit 20, codegen-core 5, substrait 58, schema-lang 50,
  Machines 24, dbsp 7 — 0 failures (the `strlen` pin is the lane's
  in-flight Validate wiring — a NEW pin appeared mid-wave; not this
  pass).
- wasm-compile (incl. the new observability byte-tie), splice-smoke,
  forge gen --check: green. steel-host 27, wire 14, forge 2.
- Deferred with reasons: substrait `runChecks`→CheckM (error-abort
  semantics + display); the VCase compiled lane (feature, backend
  design session); unused-import linter (no linter exists in v4.33).


---

## GIT-RECOVERY POST-MORTEM (2026-09-14)

The Decode.lean monad agent's recovery step (`git checkout` from HEAD,
mid-run) set the subtree back beyond its own file. Verified set-backs
and fixes:

1. Decode.lean — lost my wave-1 refactors (`litWithSuffix`/`intLitTail`/
   `fnCtxOf`/`kindOf`) + A3's `Substrait.Decode` namespace fix + the
   Tests refs: RE-APPLIED, build + 58/58 re-verified.
2. substrait/Typed/Schema.lean — `Schema.width` resurrected (zero
   consumers): RE-DELETED.
3. `fieldsItemsRust` — wave-1's claimed one-liner never landed (the
   wave-1 batch aborted BEFORE the Vortex edit — a phantom in the
   doc); final state = the mutual-bound structural recursion (see #21).
   Review-doc claim corrected.
4. dbsp Incremental.lean header still cited the deleted
   `chain_incremental`: fixed.
5. Sweep of ALL other packages' wave markers (Machines A1 + duality,
   dbsp rename, codegen-core GuestGate/Core, TestKit runVerdicts +
   export LSpec, LintKit cross-module, wasm-backend variantBox/goAlts/
   userTys/cert, faults writeFileCreatingDirs): INTACT.

Lesson: the git recovery operated on a shared working copy without
stating its pathspec; the coordinator's presence-check sweep (each
wave's marker) is what caught the losses — a cheap gate to run after
any subagent reports a git operation.

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

REMAINING (2026-09-09 late — after the LintKit-triage round):
- wasm-backend `lake test` identity-control failure is the USER's
  in-flight trampoline/mesh WIP (their `GenMain.lean`/`WasmBackend.lean`/
  `demo-world.wit` edits landed mid-session; `def rows` changed under us).
  Not an agent item — coordinate with the owner.
- 6.5.3 REMAINING wiring: one `auditFindings` exemplar is live
  (deltaWit); the other emitters' rule sets are unwired.
- Deferred follow-ups: `body : Name` fn-item field; migration authoring
  surface; fire `SchemaDiag.volatileInPureContext` when a pure-context
  role exists in the item algebra. 6.5.5 notes: DONE
  (notes/full-remaining-work.md tail).

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

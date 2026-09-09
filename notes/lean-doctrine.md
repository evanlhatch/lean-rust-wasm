# Lean Doctrine — how the guestlang workspace works and what enforces it

The living spec: every pattern the Lean packages follow, where it lives,
and what enforces it. When a lint or gate lands, this table updates in the
same commit — an entry marked `convention-only` is a TODO for the lint
framework, not a finished discipline.

Enforcement levels, weakest to strongest:

1. **convention** — written here, enforced by review.
2. **lint / test-audit** — a Lean check (env-linter, `#guard`, registry
   audit test) fails CI in `just gates`.
3. **structural** — the code is generated/derived so the wrong shape is
   inexpressible (attributes, macros, generators, import layering).
4. **gate** — `just gates` fails the build (byte-ties, axiom check,
   wit-parser round-trip, differential replay).

Always prefer the strongest applicable level. A convention that matters
should become a lint; a lint that keeps firing should become structural.

---

## 1. The stack and its layers

```
Lean (spec of record, kernel-checked)
  @[schema]/@[schema_fn]/@[schema_resource] reflect decls → registry items
  emitters fold items → WIT / Rust / Vortex / fault artifacts (pure)
  forge (Rust driver) writes artifacts, byte-ties (gen --check)
WIT = the component boundary contract (canonical parser validates)
Rust hosts (steel-host, guestlang-rt) consume generated types
```

Package layers (downstream may import upstream, never the reverse):

```
TestKit, codegen-core            (core-only — importable by everything)
  ← Machines, substrait          (Machines: mathlib; substrait: core-only)
  ← schema-lang, faults, dbsp    (mathlib OK)
  ← wasm-backend                 (should be core+codegen-core only — see
                                  REFACTOR-GUIDE 2.1; mathlib crept in
                                  via an unneeded SchemaLang require)
```

| Rule | Level | Notes |
|---|---|---|
| Demo/spec content lives in a separate `lean_lib` root from the library | structural (lakefile) | schema-lang does this (`Demo` is its own root so `lake exe schema-gen` can `importModules`); faults currently violates it (Spec.Demo/Spec.Host in the lib root — guide 3.3). |
| Emitters are pure `List Item → List GeneratedFile`; drivers write | convention → lint | Emitter.run-vs-outputs audit test per registry (guide 3.2). |
| One writer per artifact path; every emitter's outputs are covered by the driver's job manifest | test-audit (`pathsUnique`, `jobsCoverEmitters`) | Exists in schema-lang AND faults registries. The gap: `run` re-states paths and nothing checks them against `outputs` (guide 3.2). |
| Every artifact carries a provenance header citing its spec source | structural (`Emitter.specSource` → `CodegenCore.Emit.header`) | Currently defeated in the golden path: Tests/Main.lean:198 hardcodes the header instead of `e.specSource`, so 6 of 11 emitters byte-tie a header production never emits (guide 1.4). |
| Closed universes stay closed (no escape-hatch ctors); new ctors break every emitter until handled | structural (exhaustiveness) | `Ty` (18 ctors), `MetadataShape` (no `Raw`). This is deliberate — do not "fix" the parallel folds over `Ty`. |
| Unsupported constructs in a backend THROW; never emit comments | structural | `WasmBackend.unsupported`; pure-only ctors discharged by `absurd`. |
| Boundary policies are pure predicates + elab-time attribute gates with `#guard` positive AND negative controls | structural + test | `WasmBackend.Check` (`@[guest]`, `Ban.strict/.std`). The shape: policy as pure data, attribute only renders. |

### Dependency policy: core / Batteries / mathlib (verdict 2026-09-09)

**The split holds — no blanket mathlib adoption.** mathlib belongs in
packages whose subject matter is math (dbsp: Finsupp Z-sets, big
operators; Machines: well-founded recursion, Order machinery). The
wire/emitter/test packages (substrait, codegen-core, TestKit) stay
core-only: mathlib would buy them almost nothing and costs them their
role as the dependency-light public surface.

Evidence from the audit of what core-only code actually handrolls — every
finding had a CORE v4.33 replacement, no mathlib needed:
`String.intercalate` + `toList_intercalate` / `intercalate_cons_of_ne_nil`
(the sep/joinCSep collapses), `List.zipIdx`, `List.eraseDups`,
`Lean.Data.EditDistance.levenshtein`, `Expr.getUsedConstants`,
`List.mergeSort` (stable), `Option.map_eq_some_iff`, `List.getElem?`.
The tactics the core packages use (`omega`, `decide`, `native_decide`,
`simp`) are all core. Mathlib's unique value (Finsupp, the algebraic
hierarchy, big operators, Order) is irrelevant to wire codecs and emitter
folds. Cost side: mathlib drags the transitive closure (batteries, aesop,
Qq, …) into every downstream package — wasm-backend's manifest went
17→5 entries when its accidental SchemaLang require was dropped.

**Batteries**: already vendored transitively at a pinned rev; mathlib
packages MAY import it selectively where it replaces a handroll (e.g.
`List.IsChain`). Core-only packages do NOT take Batteries — the public
wire library's purity is the product (substrait/lakefile comment).

## 2. Definitions, instances, simp

| Rule | Level | Notes |
|---|---|---|
| Schemas / field lists / type lists used in instance search are `abbrev` (reducible), never `def` | convention → lint | The `Row.setN`/`HasField` lesson; repo AGENTS.md records it. Instance search must see through them. |
| One-line forwarders are `abbrev` or deleted | lint | Opaque `def sep := String.intercalate` (substrait Emit/Text.lean:71) forced Decode.lean to re-prove intercalate lemmas. |
| Every recursive def ships `@[simp]` equation lemmas | lint (env: `getEqnsFor?` + `isRecursiveDefinition`) | Known violations: `Machine.step?_eq` (Machines/Core.lean:114). |
| Don't re-prove a lemma core already has | convention → lint | **Search-before-proving**: before any List/Option/String/UInt/Finsupp lemma, `#search` (LeanSearchClient ships with mathlib). If you write "core has no X" in a comment, cite the check you ran — the audit found multiple false claims (core HAS `List.getElem?`, `List.zipIdx`, `List.eraseDups`, `Lean.Data.EditDistance.levenshtein`, `Expr.getUsedConstants`). |
| Structures with decidable fields derive `DecidableEq` (+ `Repr`, `BEq`) | lint | substrate: Machines/Dsl.lean:119 already does; gaps elsewhere (guide 4.x). |
| No orphan instances; `BEq` implies `LawfulBEq` when hand-used in proofs | lint | |
| Generated files are generator-owned — fix the generator, never the artifact | gate (byte-tie) | Includes deriving clauses: want `Repr` on generated structs? Teach the emitter. |

## 3. Proofs and axioms

| Rule | Level | Notes |
|---|---|---|
| Zero `sorry`/`axiom`; headline theorems print only propext / Classical.choice / Quot.sound (+ disclosed native_decide) | gate (`just lean-axioms`) | Weakness: coverage is hand-maintained `#print axioms` lists — substrait gates 1 theorem here vs ~22 in the flatland lineage (guide 3.1). Target: env-linter over `Lean.Util.CollectAxioms` covering EVERY decl, no list. |
| A missing theorem is information; a stub is a lie | convention | |
| Shared tactic idioms become macros, not copies | convention → lint | dbsp's `zset` simp attr is kept; the unused `zset`/`beq_cases` tactic macros were deliberately REMOVED (Tactics.lean removal note) — if Flatland is rebuilt on this template and needs `beq_cases`, it lands in a shared core-only ProofKit module, not inside dbsp. |
| `variable` for binder telescopes shared by ≥3 consecutive theorems | lint | |
| No vacuous theorems (`Eq a a`, `⟨_, rfl⟩` witnesses) without a doc note | lint | Preferred fate: convert to executable plausible/differential properties. |

## 4. Testing (TestKit)

All test code flows through TestKit (CheckResult / Golden / PropSpec).
Every sweep or property ships a **mandatory negative control**: the
sabotaged sibling must be caught or the suite fails (the vacuous-green
lesson). This discipline already appears in: `TestKit.PropSpec`
(plausible), `Machines.Testing` (phantom `labels_complete` param — a
partial label enumeration can't pass vacuously), `pipelineGuardControl`
(dead-event machine must FAIL guard coverage), the wasm differential
gate's flipped-instruction sabotage row (Rust-side).

| Rule | Level | Notes |
|---|---|---|
| Every package's lakefile sets `testDriver`; tests run via `mainOfChecks`/`mainOfSuites` | convention → lint | wasm-backend violates (no testDriver, unused TestKit import, guards after `main` — guide 2.4). |
| `#guard` is for compile-time predicates; IO/property suites are LSpec `TestSeq`s via TestKit | convention | |
| Deterministic checks deserve the same +/− control discipline as PropSpec | **to build** (`DetSpec`) | Hand-reinvented at the call sites today. |
| Error assertions go through structured diagnostics, not ad hoc substring matching | convention → structural | schema-lang's `SchemaDiag` (check → List Diag, wf = diags.isEmpty, did-you-mean + full valid space in every error) is the authority pattern. Extend the diag type; don't sprintf new error strings. |
| plausible instances for package types ship WITH their PropSpec + control | **to build** | Instance debt: Proto Expr/Rel/Plan (the expression grammar is unswept), schema-lang `Item`/`Ty`, Machine labels/states. Generated infrastructure (macros) should emit instances + PropSpecs. |

## 5. Codegen and the byte-tie

| Rule | Level | Notes |
|---|---|---|
| Artifacts are committed; `just gen-check` regenerates in memory and byte-diffs; drift fails CI | gate | 13 artifacts today. `--update` exists for deliberate changes only. |
| Registry audits: `pathsUnique` (one writer), `jobsCoverEmitters` (registered ⇒ byte-tied) | test-audit | Add the missing third: `run` outputs ⊆ declared `outputs` (guide 3.2). |
| Emission correctness: prove the round-trip where a parser exists; byte-tie the text where it doesn't | gate | WIT: wit-parser inversion fixtures (WitFixture — scalars fixture caught a real keyword collision). Delta trait: name-pinning test against the Lean class fields. substrait text: proved decode∘emit inversions. |
| Table-driven generation beats hand transcription | structural | `pipelineRust` currently hand-copies the PROVED `pipelineTrans` table as `.raw` strings — the table→Rust drift the design exists to prevent is still open (guide 1.5). Fold the table into arm text. |
| Codes/positions are derived, never hand-set | structural | `allocateCodes` + kernel-checked length lemma. Gap: host/guest ranges collide past 10 guest faults (guide 1.6). |
| Golden byte-ties compare against what production actually emits | test | Golden path must use `e.specSource` headers (guide 1.4); consider tying goldens to the committed src artifacts directly. |

## 6. Metaprogramming and reflection

The template's core trick: Lean declarations as the spec of record;
attributes reflect at elaboration into a `SimplePersistentEnvExtension`;
drivers replay via `importModules (loadExts := true)` +
`enableInitializersExecution` (requires `supportInterpreter = true` in the
lakefile).

| Rule | Level | Notes |
|---|---|---|
| Registry extension semantics are pure DATA tested purely (`RegistrySpec`); `mkRegistryExt` manufactures the extension | structural | schema-lang/Meta/Reflect.lean:42-47 reimplements `mkRegistryExt`'s spec inline — use the shared factory (guide 2.2). |
| The importModules driver preamble + writeFileCreatingDirs exist ONCE in codegen-core | **to build** | Copied between GenMain and Tests in schema-lang (guide 2.3). |
| Boilerplate families are generated, not written | **to build** | `declare_binop` (substrait Typed/Expr ×8+8), enum wire codecs, per-constructor inversion theorems (Decode.lean's 9× scalar clusters ×3 locations). |
| New backends clone the `leanir` re-run recipe (importModules → LCNF.main → getLocalImpureDecls → emit) | convention | Documented in wasm-backend/GenMain.lean. |

## 7. Notes discipline

Decisions live in `notes/`, one file per decision: context → options →
decision → rejected alternatives with failure evidence. Code comments point
here; when a note disagrees with a stale comment, the note wins (then fix
the comment). Verdicts are verified by build test before being recorded
(decision-wasip3-linking.md is the model).

## 8. The enforcement ladder and design rules

(Transferred from the flatland lineage's TOOLKIT.md/kimi notes — the
philosophy this template embodies, stated once.)

### The four-tier ladder

0. **Proved in Lean, erased** — manifests as the ABSENCE of defensive code
   downstream. If the spec proves it, nothing below checks it.
1. **Compile-time Rust** — types make bad states unrepresentable.
2. **Runtime checks** — only at trust boundaries (host↔guest, network,
   hand-written↔generated seams).
3. **Hand-written code** — only behind generated seams.

Pressure rules: wanting a mid-logic runtime check = promote the invariant
into the spec. Hand-written code fighting a type = the spec's domain model
is wrong; fix the spec, not the code.

### Design rules (the generalizations of the repo's known traps)

- **Bridge kit, in order** (new exec data structure checklist): (1)
  canonical form with proved semantics — pick the representation with
  lemma support (`List.mergeSort`, not `Array.qsort`); (2) `@[simp]`
  equations land in the SAME commit; (3) observer bridges
  (`getElem?`/`find?` characterizations); (4) membership/permutation
  facts; (5) THEN the laws, pointwise via `List.ext_getElem?`. Proving a
  bridge lemma about a structure that landed last week means the
  structure shipped without its kit.
- **Index ceiling**: three indices max at author-facing surfaces; a
  fourth becomes a predicate. Compute by reduction, prove by search.
- **Type-class search assembles proofs, never calculates values.**
- **Quotients quarantined to proof-land** — never in codegen-consumed
  data. HEq/John-Major needed between two indexed families = redesign
  signal.
- **Machines are SETS of transitions** (any enabled event may fire);
  **protocols are SEQUENCES** (order is the artifact). Session/indexed
  machinery serves sequences; plain `Machine` serves sets. Don't reach
  for Session types for unordered event sets.
- **Canon discipline**: a new subsystem names which known shape row it is
  (delta / stream / machine / fixpoint / partial-iso / codec) and
  inherits that row's laws, oracle coverage, and codegen path. Matching
  no row is a finding — the canon grows deliberately.
- **Proved counterexample → boundary lint**: a proved negative (e.g.
  dbsp Ordering's monotone-vs-D counterexample) justifies a boundary gate
  rejecting the unprovable shape at elaboration, the error CITING the
  counterexample. Hypothesis in theorem = field in item = code in host.
- **Elaboration traps** (from Dbsp.Circuit): interpretation functions
  over type-family-valued section variables take EXPLICIT binders
  (binder-info-mismatched eta-expansions fail defeq downstream); split
  flag-computation (plain recursive def) from soundness (induction
  theorem), wrap as a Subtype at the end; never ascribe section-variable
  types inside an induction arm.

### Discharge ladder (order of preference)

`rfl`/`decide` → `simp` with the def's own equation lemmas → `omega` /
`native_decide` (disclosed trust base) → `bv_decide` for fixed-width/
overflow contracts (verified LRAT — unlike SMT bridges) → explicit term.
`partial_fixpoint` exists for honestly-possibly-divergent loop
definitions before per-instance convergence is proved.

### Differential-testing doctrine

- The oracle only validates what reaches it — keep the observable surface
  generous in test builds (test-only flags may expose more state).
- Conformance compares operation SEQUENCES; "engine accepted what the
  spec rejects" is the most important bug class — generators should
  include a small invalid-mutation rate (DiffSpec's Corruption is the
  gate-level instance; generators need it too).
- Every historical divergence becomes a committed minimized case — the
  corpus grows from bugs.
- Floats compare bit-exact, never approximately.

## 9. What we deliberately do NOT do

- No verifier-framework deps (loom/veil/velvet/lean-machines) — pattern-
  match instead.
- No Aesop-heavy proof structure — automation discharges arithmetic
  (omega/decide/native_decide), not structure; proofs stay inspectable for
  the drift discipline.
- No do-notation rewrite of substrait's Decode internals — proofs consume
  raw equation lemmas (`parseType.eq_*`); `do` changes term shapes.
- substrait here is the TEXT surface only — ProtoGen/protobuf wire codec is
  deliberately excluded (lakefile comment) until binary interchange is
  needed; the stale lakefile/umbrella references to Vortex/ProtoGen get
  fixed (guide 0.x).
- Reservoir publishing is deferred until APIs stabilize (README).

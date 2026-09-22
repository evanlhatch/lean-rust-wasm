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
Rust hosts (guestlang-host, guestlang-rt) consume generated types
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
| Closed universes stay closed (no escape-hatch ctors); new ctors break every emitter until handled | structural (exhaustiveness) | `Ty` (20 ctors), `MetadataShape` (no `Raw`). This is deliberate — do not "fix" the parallel folds over `Ty`. |
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
| `native_decide` is grandfathered-only: new uses need a disclosed justification AND join the checked-set exile list | gate (`gates native-policy`) | lean4lean has no reduceBool, so a decl on the `_native.native_decide.` trust base is outside the independent kernel's checking (design-guest-verified.md §6.3). The 3 disclosed uses (edgepython's Parity module; schema-lang's Emit/Circuit ×2) are permanent checked-set exiles, named in `Gates.NativePolicy.grandfatheredNative`; a stale exile entry fails the gate too. The `_native.bv_decide.` sibling stays under the axiom allowlist's disclosure discipline (verified-LRAT certificate class). |
| A missing theorem is information; a stub is a lie | convention | |
| A green kernel sweep means exactly the checked surface, never more: the sweeps are honest about their blind spots (`example`s, structure-field defaults, anything outside `gatedPackages` — Gates/KernelCheck.lean header caveat (d)), and `gates axioms --write` refuses a non-empty diff (re-baseline = deliberate: `--write --accept-drift`) | gate (`gates kernel-check` + `gates axioms --write`) | PolyFun's axiom-sweep honesty pattern (polyfun-study.md item 2). |
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

Pressure rules (2026-09-18 extension — the correspondence preference):
whenever two presentations of the same data exist, prefer them in this
order: (a) a TRUE `Iso` (equal by construction — transport makes every
law free; the quotient-iso pattern turns normalizers into types:
`X/~ ≅ CanonicalX`); (b) a `PartialIso` into the canonical/checked
image (codecs, checkers: "checked" IS "in the image"); (c) a Decidable
check with a bridge; (d) a gate. A re-derived law where an iso exists
is a finding. wanting a mid-logic runtime check = promote the invariant
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

---

## 2026-09-15 additions (the cohesion wave)

Sources: notes/lean-cohesion-plan.md, notes/code-review-2026-09-15.md,
notes/runbook-2026-09-15.md. Enforcement levels as above.

| Rule | Level | Notes |
|---|---|---|
| Every agreement theorem is an instance of `Iso`/`PartialIso` (the kit) | convention → structural | The kit lives in a CORE-ONLY home (not Machines.Foundations — it needs zero mathlib). ~145 hand-rolled agreements predate this; new ones MUST be instances. The Iso/PartialIso ladder IS the correspondence vocabulary — `Denotes`/`ReprOp` were deleted as consumerless (2026-09-18): a one-way representation claim today is a comment or a `CheckedProp`; re-add the class only when a second consumer exists. |
| One copy per concept: did-you-mean, Async markers, EqAns/HasCol, cert-citation, edit distance | lint (cross-package DupDefBodies extension) | The known copies are enumerated in the review; new copies fail review. |
| Generated artifact = one writer + one SOURCE | gate (byte-tie) | The oracleSrc/Oracle.lean two-source drift is the canonical violation (W0.1). |
| Simp sets are invoked or stripped — tagged-but-unused is theater | lint (≥2 set members listed by hand ⇒ use the set) | `zset` is the found instance. `unusedSimpArgs` ON for library targets. |
| `deriving ToExpr` / Qq quotations over raw `Expr` surgery | convention → lint | Meta/Reflect's hand walks are the migration debt (W2.1/W2.2). |
| `fuel` only where the bound IS semantics; structural measures use `termination_by` | lint (fuel param beside a proved measure) | Sem.exec/cascade cap = semantic fuel; parseType/buildOne? = measures exist. |
| Elaboration errors are named (`register_error_explanation`), structured, enumerate the valid space | convention | The LLM contract. No bare `throwError` strings at authoring surfaces. |
| Automation ladder: generated proofs → grind → omega/decide/bv_decide → aesop (leaf goals, mathlib packages only, never in cert-cited theorems) | convention | Proofs are artifacts: cited by #check_cert, pinned by byte-ties. Search rots silently; construction doesn't. |
| mathlib: kernel packages core-only (kit, codegen-core, substrait, TestKit, LintKit); everything above may use it narrowly, never `import Mathlib` | gate (importGraph layering) | Qq/Batteries/aesop/ProofWidgets are in closure via mathlib — free above the kernel line. |
| Unused-but-planned modules are marked `seed` in notes/reuse-map.md, not deleted on sight | convention | ledger/Foundations.Dag are seeds for the event-sourcing/scheduler lanes. True dead weight (empty dirs, dead defs) still dies. |
| Module system (`module` keyword) for new/split modules; `meta` sections for elab internals | convention → lint | Adopt leaf-packages-first; mathlib at this rev is module-native. |

## 2026-09-15 additions, part 2 (the framework decisions)

| Rule | Level | Notes |
|---|---|---|
| Relations are a legal spec form WHEN the concept is relational (nondeterminism, don't-care order, inference-rule legibility); a relational spec MUST ship its executable checker + the bridge theorem | convention → structural | The two-projection pattern generalized (cedar: `InstanceOfType` ↔ `validateWellFormed`). Never relation-only. |
| GADTs at the authoring surface + semantics; plain IR with external WF only where a transformation PASS PIPELINE exists | convention | Indices are first-order data here (closed Ty) — the sweet spot. The bar for dropping indices is a real pass pipeline, not vibes. |
| Every checkable fact is an `Obligation` (label + assumptions + payload + provenance); the enforcement tier is a BACKEND ASSIGNMENT (kernel proof / decide / generated runtime check / oracle sweep) | structural (Wave 7) | Replaces: ad-hoc elab gates, hand-wired generated checks, the "armed but unfired" pattern. |
| A rule that has fired twice as a violation becomes structural or generated — convention is a staging area, not a home | convention | The framework-mindset clause. |
| mathlib: dev/tooling dep, never guest-compiled code. The guest fragment (what the wasm backend compiles) stays core-only | gate (GuestGate + importGraph) | Above the line, use mathlib narrowly: Finset/Fintype, NNRat/monus, ReflTransGen, Quiver/Paths, DFA/Language, linarith/ring/gcongr, aesop at leaf goals. Never `import Mathlib` umbrella in library code. |
| Feature admission test: a new feature names its kernel concept (Universe / Correspondence / Law class / Machine / Registry→Emitter / Surface / Obligation) and its canon row, or it's a finding, not an addition | review | Keeps the conceptual surface at seven. |
| Registry items carry provenance (declaring decl, doc, source range) | structural (W7.5) | Errors, docs, generated headers all read it. |
| Generators are monad-polymorphic (the Basalt `Gen` pattern); new generators are written ONCE against `Gen g`, not per-backend | convention → structural (W6.14) | Plausible + byte-tape (FuzzGen) interpretations minimum; SPMF proofs opt-in. |

| Every decidable property is a `CheckedProp` — relation (reasoning authority) + executable check + soundness proof (+ completeness when decidable; a documented gap when not) | structural (kit, W1.1) | The two-projection pattern at the predicate level. Bridges are TYPED, not commented — `checkAcyclic`'s deferred completeness would be a missing field, loud. |
| Confluence is the relational form of order-freedom: cascades/schedules whose interleavings agree are confluence claims; state them relationally, prove via the confluence toolkit, discharge the finite cases by decide | convention (W8.3) | `cascade_two_commute` is the 2-element shadow of "the tick is confluent". |

| Representation routing: index/GADT what elaboration must reject; inductive Prop family what proofs must invert; executable fn + CheckedProp what must run; canonical form what equality must decide (NEVER a quotient in computable land — quotients need the "no computable normal form + proof-land only" flip condition, documented); relation/setoid for agree-up-to (simulation/bisimilarity) | convention → lint | The six-row routing table; TOOLKIT 5.5 index ceiling stands; mathlib Multiset/Finsupp cover bag/zset proof-land needs |

| Emitters consume `CheckedUniverse` (the universe + its WF evidence bundled), never raw items + assumption | structural (W7.9/W3.5) | Defensive arms become unrepresentable; "may assume checked input" comments become types. Bundling stays at boundaries/constructors (5.4). |
| All text artifacts ride one pipeline: registry → typed doc → Std.Format → bytes; a format with a parse-back gets grammar-as-data (printer+parser+inversion from one table) | convention → structural (W7.10) | Raw-string emission is the drift surface; the oracle-manifest JSON trap is the evidence. |
| Registration computes; emission assembles | convention (W2.7) | Everything computable at attribute-time is computed there; drivers never re-derive. |

## 2026-09-15 lint battery (LANDED — the doctrine rows that are now gates)

All in LintKit/TextLints.lean (+ the Runner artifact gate), each with
positive AND negative controls in LintKit/Tests:

| Lint | Blocks |
|---|---|
| `linter.guestlang.noNewPartial` | new `partial def` (per-file legacy allowance; Tests/ exempt) |
| `linter.guestlang.noReprInEmit` | `repr` in Emit/ modules (Repr is not a wire format) |
| `linter.guestlang.noFormatInDebug` | re-rendering in Debug.lean (debug views call emitters) |
| `linter.guestlang.coreHasNoClaim` | uncited "core has no X" comments (multi-line docstring aware) |
| `linter.guestlang.staleNotesPath` | bare `notes/lean/` refs (a `flatland's notes/…` pointer is honest) |
| `linter.guestlang.nolintReason` | `@[nolint]` without the reason string |
| `linter.guestlang.artifactHeader` | declared generated output missing / headerless (a `just gates` row: `just artifact-headers`) |
| testImportDiscipline (extended) | driving LSpec directly in Tests/ (not just the import) |

First catches, all landed with the battery: 19 stale `notes/lean/`
references (now honest `flatland's notes/…` pointers), three "core has
no X" claims verified TRUE and now cited, dbsp's Tests driving
`LSpec.lspecIO` directly (routed through `TestKit.mainOfSuites`).

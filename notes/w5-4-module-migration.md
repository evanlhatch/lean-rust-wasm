# W5.4 module-system migration — phase 1 results + phase 2 recipe

Evidence base: phase 1 migrated `lean/dbsp` (all 21 modules incl. root) and
`lean/Machines` (11 of 14 modules) on Lean v4.33.0. Every claim below was
observed in a compiler error or a probe file, not inferred from docs.

## Hard constraints (observed, v4.33.0)

1. **A `module` file cannot import a non-`module` file at all.**
   Error: `cannot import non-\`module\` CodegenCore.Kit from \`module\``.
   Visibility kind (`import` vs `public import`) is irrelevant — the import
   itself is rejected. Consequence: migration is BOTTOM-UP over the whole
   dependency graph including our own packages; a package whose deps are
   non-module cannot be migrated at all.
2. **mathlib / batteries / cslib at v4.33.0 are already module-ized.**
   Their declarations carry public/private + exposure marks. Inside a
   `public section`, names from plain (private) imports are OUT OF SCOPE:
   `Unknown constant X` + the note "A public declaration X exists but is
   imported privately; consider adding `public import …`". In proof-heavy
   packages, signatures (`[AddCommGroup a]`, `Finsupp`) and `attribute`
   commands reference mathlib names pervasively → in practice EVERY import
   becomes `public import`. The runbook's "most stay plain" does not
   survive contact with a module-ized mathlib.
3. **Theorem kind is invisible at attribute-application time.**
   In a module, theorem bodies elaborate deferred; at
   `applicationTime := .afterCompilation` (and `.afterTypeChecking`) the
   decl is `.axiomInfo`, not `.thmInfo`. A `registerBuiltinAttribute` kind
   check (`ci.isTheorem`) therefore REJECTS every theorem in a module
   consumer (non-module consumers see `.thmInfo` — the bug only bites
   module files). Fix applied in `Dbsp.Certs`: the attribute registers the
   name; the theorem-kind check moved to `#check_cert` (the CI gate, run
   from a non-module Tests file where imported theorems report
   `.thmInfo` correctly).
4. **`show`/`rfl` defeq cannot cross into non-exposed mathlib bodies.**
   Observed: `ZSet.distinct 0 ≡ 0` fails with "The following definitions
   were not unfolded because their definition is not exposed:
   `Finsupp.onFinsetSupport`". Pre-module, the (non-module) elaborator
   ignored exposure and unfolded everything. Repair pattern: rewrite the
   `show` to match what EXPOSED reductions produce (our own defs are all
   exposed, so only mathlib-body unfolding is lost), and use the existing
   equational lemma (`ZSet.distinct_0`) via `rw` instead of defeq.
   One site needed this: `Dbsp.RelationalIncremental.distinct_incremental_ok`
   (zero branch). `simp`/`rw` with equation lemmas are unaffected —
   equation lemmas are ordinary public theorems.
5. **Private names cannot appear in public signatures.** A `private def`
   named in a public theorem's statement → `Unknown identifier` (name
   mangling). `Dbsp.Incremental.incrementalInv` had to be un-privatized
   (no consumers outside; the inversion theorems name it in their types).
6. **Non-module consumers are unaffected.** A legacy file importing a
   module sees exactly the old transitive behavior (proved by
   schema-lang, feature-flags — which runs the `machine!` command
   elaborator from module-ized `Machines.Dsl` — and both packages'
   unchanged Tests suites).

## The recipe (as executed; use for schema-lang, phase 2)

Per file, bottom-up along the import DAG:

```
module                                    -- first command after the header comment

public import Foo.Bar                     -- ALL imports public (constraint 2)
public import Mathlib.Something

@[expose] public section                  -- def/theorem-bearing files
…decls unchanged…
end -- @[expose] public section
```

- Tactic/elaborator files (`Tactics`, `Certs`, `Dsl`): `public meta
  section` instead. Holds `syntax`, `macro`, `macro_rules`,
  `register_simp_attr`, `initialize` (env extensions + builtin
  attributes), `elab`, `@[command_elab …]`. All worked first try.
- `private` decls inside a `public section` stay private — unless named
  in a public signature (constraint 5).
- Root aggregates (`Dbsp.lean`): `module` + `public import` of every
  internal module. A root CANNOT be a module while it imports a
  non-module file (constraint 1) — `Machines.lean` stays legacy for now.
- Tests and downstream stay untouched (constraint 6).

## Phase 1 migration table

### dbsp (21/21 modules migrated; build + `lake test` + `Tests/Axioms.lean` all green)

| file | shape | notes |
|---|---|---|
| Lint | module, 2 public imports | pilot; pure re-export module |
| Tactics | `public meta section` | `register_simp_attr zset`, `stream_cases` |
| Certs | `public meta section` | `@[cert]` kind check moved to `#check_cert` (constraint 3) |
| Stream, ZSet, Operators, Linear, Replicas, Relational, Incremental, ChangeSpec, Determinism, Effects, StreamElim, Recursive, NestedCycle, Ordering, Circuit, Staging, Subsystems | `@[expose] public section` | Incremental: `incrementalInv` un-privatized (constraint 5) |
| RelationalIncremental | `@[expose] public section` | one `show` repaired (constraint 4) |
| Dbsp (root) | module + all public imports | incl. the two Cslib imports |

### Machines (11/14; build + `lake test` + `Tests/Axioms.lean` all green)

| file | shape | notes |
|---|---|---|
| Tactics | `public meta section` | `guestlang_solver` ladder + `guard_omega`; extension rungs downstream still work (feature-flags) |
| Core | `@[expose] public section` | EventSpec/Machine/step?/run/tr |
| Compose, Session, Refine, Convergent, LinearMachine, Rewind, Sim, Trace | `@[expose] public section` | Convergent/LinearMachine/Rewind/Sim public-import the Dbsp modules |
| Dsl | `public meta section` | whole file is `machine!` elaborator infra |
| Sync | `@[expose] public section` | `machine!`-generated decls land public+exposed |
| **Foundations** | NOT migrated | imports non-module CodegenCore.Kit (constraint 1) |
| **Testing** | NOT migrated | imports non-module TestKit |
| **Machines (root)** | NOT migrated | a module root cannot import Foundations/Testing |

## Phase 2 prerequisites (before schema-lang migrates)

schema-lang's import surface includes CodegenCore (Registry/Emit/…),
TestKit (→ LSpec), LintKit, QLang, Substrait, etc. Constraint 1 means
EVERY dependency must be module-ized first. Order:

1. **codegen-core** — `Kit.lean` has zero imports (trivial pilot);
   AttrKit/Registry/Emit import `Lean` (module-ized core) so they should
   follow the Certs/Dsl meta pattern. Watch: codegen-core is the
   byte-tie universe owner — the spec of record is generated text, so
   Lean-side module changes don't touch artifacts, but run
   `just lean-build && just lean-axioms && just gates` after.
2. **LSpec status check** — only partially module-ized upstream
   (`LSpec/SlimCheck/Control/*` are modules; the `LSpec` root aggregate
   may not be). If TestKit's LSpec surface isn't module-ized, TestKit
   blocks: either carry a small local patch/upgrade or migrate TestKit's
   Harness to avoid the non-module parts. This is the biggest unknown.
3. **TestKit, LintKit** (depend on 1–2), then **schema-lang** bottom-up:
   Flatland/Value first (it imports Dbsp.Lint's bundle — already a
   module), Emit/* last (they're `Lean`-heavy meta files →
   `public meta section`).
4. Then **Machines.Foundations / Testing / root** finish (unblocked by 1–2).

## Discipline summary (defs that NEEDED expose)

Effectively every def/abbrev/instance/structure in both packages — the
packages are def-heavy and proofs rfl/unfold over operator defs
constantly (`delay`, `D`, `I`, `lifting`, `step?`, `run`, Kit aliases).
Phase 1 therefore exposed everything; opacity TIGHTENING (which decls
may drop `@[expose]`, cedar C4-style private representations) is
deferred to W6.13's `@[expose]` audit. The one defeq that even full
exposure could NOT save was mathlib-body unfolding (constraint 4) —
the durable rule: **proofs must reduce through OUR exposed defs and
mathlib LEMMAS, never through mathlib DEF bodies.**

---

# Phase 2 addendum (codegen-core, TestKit, LintKit, schema-lang, Machines leftovers)

Evidence base: phase 2 migrated LintKit (9 lib modules + root), TestKit (6 +
root), codegen-core (13 + root), schema-lang (46 modules incl. root and Demo),
Machines.Foundations/Testing/root (Machines now 14/14). Builds + tests +
`Tests/Axioms.lean` green in all five packages; schema-lang byte-tie
content-identical (see below). Every claim observed in a compiler error on
v4.33.0.

## Order correction (constraint 1 wins over the work-order sequence)

schema-lang's `OrderMachine`/`Pipeline` import `Machines.Testing`, so the
Machines leftovers had to migrate BEFORE schema-lang, not after. Executed
order: LintKit → TestKit → codegen-core → Machines.Foundations + Testing +
root → schema-lang. (codegen-core's `AttrKit` imports `LintKit.DeclCheck` and
`RoundTrip` imports `TestKit`, so codegen-core could not go first either —
only its zero-import `Kit.lean` pilot did.)

## New constraints (phase 1's list extends)

7. **Module mode enforces a REAL meta phase distinction; legacy ignores it.**
   `Lean.Compiler.LCNF.Visibility.checkMeta` runs only for module files.
   Errors and repairs, all observed:
   - meta def referencing a same-module non-meta def → "`X` not marked
     `meta`" — mark the helper `meta` (cascade within the file), or
     `set_option compiler.relaxedMetaCheck true` when the meta def must
     reference a same-module non-meta FAMILY that non-meta code also uses
     (used once: `SchemaLang.Item` for the `declare_enum_wire` products).
   - meta def referencing a non-meta IMPORTED decl → "not accessible here;
     consider adding `public meta import M`" — additive import, keep the
     plain `public import` too.
   - non-meta def referencing a meta decl → "may not access declaration
     marked as `meta`" then "failed to compile … noncomputable" — the
     referencing def must go meta (or the whole file to
     `public meta section`).
   - `@[command_elab]` / `@[app_unexpander]` decls must be `meta`;
     `app_unexpander` decls must additionally be PUBLIC (`private`
     unexpanders are rejected — `SchemaLang.Validate` un-privatized seven).
   - Modifier order is `meta partial def` (`partial meta def` is a parse
     error).
   - LSpec/Plausible mark `checkPlausibleIO`, `PrintableProp` instances etc.
     meta; anything embedding them (PropSpec assembly, generated test
     suites) is meta-contaminated. `declare_enum_wire`'s template now emits
     `meta def wireSuite/wireControl/wirePropSpec` (generated-code templates
     are part of the visibility surface).
8. **Attr-registering `initialize` must live in a `meta` section.** Plain
   (non-meta) `initialize` blocks do not run at import in module mode
   (import-time execution is interpreter-only) — the attribute is then
   "Unknown attribute" in importing modules. `LintKit.Basic`'s
   `@[nolint]` registration failed cross-module until the file went
   `public meta section`; phase 1's `Dbsp.Certs` was already meta.
9. **Constraint 3 generalizes to IMPORTED theorems.** In a module consumer,
   `env.find?` on an imported theorem is not `isTheorem` during elaboration:
   `SchemaLang.Emit.Circuit`'s `#check_cert Dbsp.incrementalize_ok` failed
   with "not a theorem". Repair: the pin moved to the legacy
   `Tests/Main.lean` (drift = test-build error; comment updated). Any
   elaborator that kind-checks constants is module-unsafe, imported or not.
10. **`native_decide` in a module needs `public meta import` of the modules
    owning the referenced instances/defs** (`Mathlib.Algebra.Group.Int.Defs`,
    `Dbsp.Circuit` for `SchemaLang.Emit.Circuit`).
11. **Server-level extension data needs `import all`.** Module-mode oleans
    export `moduleDocExt` at `.server`/`.private` level only
    (`exported := #[]`), so `Lean.getModuleDoc?` over a plain import returns
    nothing in batch processes. `SchemaLang.ModuleDocs` imports its six
    manifest modules with `import all` (syntax: `public? meta? import all M`).
12. **Exe drivers touching meta env extensions stay legacy.**
    `GenMain`/`CheckMain`/`BreakingMain` call `meta` registry constants
    (`schemaItemExt`, `registeredInvariants`) from compiled `main` — illegal
    in module mode; `SchemaMain` imports them, so it stays legacy too.
    Legacy consumers are unaffected by meta bits (the `guestlang-lint` exe
    over the all-meta LintKit engine builds and runs green).
13. **Exposure propagates along rfl chains.** `Emit/Registry`'s
    `jobsCoverEmitters_true := rfl` folds EVERY emitter module, so
    `Vortex/Emit`, `Vortex/ExtDType`, `Snapshot` needed `@[expose]` after
    all, and their private helpers (`parseTy`, `Open`, `State`,
    `bytesVecRust`, `serializeBody`, …) hit constraint 5 and were
    un-privatized. Rule of thumb: if any public theorem proves `rfl` over a
    cross-module fold, the whole fold's modules are expose-forced.

## Tooling trap (mechanical migration)

Header comments containing lines that START with `import`/`module` (col 0,
inside `/- -/` blocks) fooled the batch transform — `SchemaLang.Validate`,
`SchemaLang.Meta/Reflect` (mid-comment `module` insertion),
`SchemaLang.ExprLang`, `SchemaLang.Vortex/Emit` (skipped entirely).
Zero-import files got `module` but no section marker → every decl private
(`Vortex/DType` → downstream "Unknown identifier"). Verify per-file with
`grep -c '^module$'` and a build before moving on.

## Files left legacy (with blocker)

| file | blocker |
|---|---|
| `SchemaLang/Bridge.lean` | imports `Substrait.Typed.Expr`; substrait is 1/29 module-ized (constraint 1). In-scope once substrait migrates. |
| `GenMain/CheckMain/BreakingMain/SchemaMain.lean` | compiled `main` references meta env-extension constants (constraint 12). |
| `LintKit/LintMain.lean`, `LintKit/TestFixtures*`, all `Tests/*` | legacy by design (constraint 6); fixtures are `importModules` replay targets. |

## Phase 2 migration table

### LintKit (10/10 lib modules; build + LintKitTests + guestlang-lint + Axioms green)
Basic, DeclCheck, AxiomAllowlist, DupDefBodies, PackageNamespace,
RecursiveSimpEqns, GuestBan, TextLints, Runner — all `public meta section`
(linter engine; legacy exe/tests unaffected), root = module + public imports.
TextLints keeps `private def justified` (no expose → private legal).

### TestKit (7/7; build + `lake test` + Axioms green)
Harness, Golden, PropSpec, DetSpec, DiffSpec, GateKit — `@[expose] public
section`; root module + public imports + kept the `export LSpec (…)`.

### codegen-core (14/14; build + `lake test` + Axioms green)
Kit (pilot), DidYouMean, Validation, Emit/Core, Emit/Rust, Emit/Certified,
DataRegistry, CodedRegistry, Enumerable, Registry — `@[expose] public
section` (Registry: `meta def deriveCtorKindsImpl` + `meta def
ctorShortName`). AttrKit expose-public. GuestGate, RoundTrip — `public meta
section` (+ meta imports). Root = module + public imports.

### Machines (14/14 now; build + `lake test` + Axioms green)
Foundations — `@[expose] public section`. Testing — plain `public section`
(keeps `private def deadlockCheck`). Root — module + public imports.

### schema-lang (46/47 lib modules + Demo; build + `lake test` + Axioms green; Bridge legacy)
Default `@[expose] public section`; `public meta section`: Meta/Reflect
(+ a trailing `@[expose] public section` for the `Async.Future/Stream`
markers — Demo's non-meta code unfolds them), Meta/Derive, Meta/Gen, Debug,
ModuleDocs head (exposed tail for `internalsPage`/emitter). Notable repairs:
Validate's elab layer meta-marked (7 unexpanders un-privatized); Item got
`public meta import TestKit.PropSpec` + `compiler.relaxedMetaCheck`;
Emit/Circuit's `#check_cert` moved to Tests/Main (constraint 9) + meta
imports (constraint 10); ModuleDocs `import all` (constraint 11);
Vortex/Snapshot expose + un-privatization (constraint 13); `Vortex/DType`
zero-import section fix.

## Byte-tie evidence

`lake exe schema gen` after the migration: every artifact's CONTENT hash
identical to the committed one (the header's embedded `content hash` field
unchanged, e.g. `13343525594910719474` for delta_generated.rs); stripped
diff (forge's `strip_header` semantics) empty for all 33 artifacts. Headers
differ only in timestamp + `spec <commit>` field — the exempt metadata the
byte-tie strips by design. NOTE: the on-disk headers now name the
uncommitted working copy (`57c7b3e+`); after the phase-2 commit lands, rerun
`just gen` so the committed artifacts' headers name their own commit.

## Downstream chain

dbsp, faults, feature-flags, wasm-backend, qlang, proofkit, std, ledger,
edgepython — all build green. **substrait fails, NOT from this migration**:
`Substrait/Decode/Plan.lean` (string-lemma proofs: `simp made no progress`
etc.) — the file's import closure is substrait-internal only, and the
working copy carries uncommitted substrait edits (Decode/*, Emit/Text,
Grammar, Tests/Main) from other in-flight work. Verified independent: no
import path from any migrated package into substrait's library.

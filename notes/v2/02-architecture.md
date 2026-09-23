# 02 — Architecture (the target state)

## 1. The three semantic kernels

All behavior is a fold over exactly three closed semantic cores:

| Kernel | Closed codes | Total denotation | Home |
|---|---|---|---|
| **Ty** | `Ty` | `El : Ty → Type` | schema-core |
| **Wat** | `Wat.Instr` + `Op` | `Sem` (stack-typed GADT, target) | wasm-core |
| **Ckt** | `Ckt` | `denote : Ckt → Operator` | dbsp |

A new surface = pick a kernel + an interpretation instance + a correspondence +
an emitter row. Never a new world.

## 1a. The roots (20)

Three orthogonal semantics: Universe (what is), Change (what changes,
reversibly; incl. DeltaSystem), TraceModel (what behaves). Two carriers:
Statement (provability), Correspondence (crossing). Everything builds as
INSTANCES of the roots: Machines = a generator whose semantics is TraceModel;
dbsp = the group instance of Change + stream theory; event sourcing,
migrations, refinement, model-checking, provenance = instances/compositions.
Provability inherits: an instance cites the root theorems (20 §4).

## 2. The cone rule

- C0 core primitives (codegen-core, TextKit, TestKit, LintKit envelope) — zero deps, everything imports.
- C1 domain cores (schema-core, wasm-core) — core-only (no mathlib); public/static worlds (substrait, future QL) consume C1.
- C2 theory (Machines/Dbsp, mathlib). C3 app (emitters, meta, lanes, Vortex, per-product).
- Enforcement: import-ban table as data; each module's cone in its header. C0/C1 never imports C2.

## 3. The primitives (four kinds + statement + one generative machine)

1. **Registry** — append + replay + snapshot + member (`declare_registry_member`).
2. **Interpretation** — one vocabulary per universe, readings as instances (`ExprLang`, `ShapeLang`, `WireLang`). Reads once, interprets many.
3. **Correspondence** — every crossing a declared `Iso`/`PartialIso`/`Denotes+ReprOp` with the law in the type.
4. **Emitter** — fold + law + header + outputs(nodup in type) + byte-tie + self-audit; `runCertified` when lawful.
5. **Statement** (one checked-fact shape, mounts) + **Obligation** (facts with tier+evidence, evidence closed).
6. **family!** — the generative engine (tables + name patterns + proof/test templates).
7. **TraceModel** (19) — THE fundamental model: events + independence + causal
   order (a poset/DAG). Machines, circuits, cascades, stage schedules,
   provenance trails, dependency universes denote INTO it; verification
   (trace sets, POR, vector clocks, fairness, refinement, causal cones) is
   the theory of the model, inherited by every denotation.

## 3a. The inference law (infer, don't generate)

Verification objects are THEOREMS and DEFINITIONAL VIEWS of what already
exists — never freshly generated artifacts. The smell test: a verification
object that needs NEW data (a table, registry, or emitted file) instead of
being computable from the declaration + theory is a design error. The only
sanctioned generation: product surface (emitters: WIT/Rust/goldens) and
genuinely new embeddings (the portable wasm verifier reuses the one
checker). Everything else — independence, posets, trace sets, clocks, POR
batteries, causal trails — is proof-over-declaration (19 §6, R11).

## 4. The One Universe (concrete)

```lean
structure Universe where
  items      : List Item          -- the Ty-level spec (records/variants/funcs/resources)
  invariants : List InvariantItem
  updates    : List Update2Item    -- v2 only
  keys       : List KeyDecl
  witnesses  : List WitnessSpec
  migrations : List Migration
  features   : List FeatureRow     -- the oracle/observability vocabulary
deriving Repr, Inhabited
```

- ONE committed snapshot text covers all lanes → one breaking diff.
- All goldens/witnesses/tests are folds of `Universe`; each lane is a field + a
  snapshot case + its emitter rows.
- New lane = one field + one member registration + one derived reader.

## 5. Target module tree (per cone — create/move modules to these homes)

```
codegen-core/CodegenCore/
  Kit.lean          -- Iso, PartialIso, Denotes+ReprOp (correspondence)
  Statement.lean    -- CheckedStatement + mounts (gate/lint/test/obligation/duel)
  Obligation.lean   -- Tier, Evidence (closed), Obligation, discharge contract, others
  Registry.lean     -- mkRegistryExt, allocateCodes
  MemberKit.lean    -- declare_registry_member
  GenKit.lean       -- freshNameCheck, did-you-mean ctx, @[derived] stamp
  AttrKit.lean      -- register_check_attribute, mountAsGate
  ModelCheck.lean   -- finite enum + transition + decidable property → cert or trace
  Errors.lean       -- Diag envelope + didYouMean engine + E-code allocation
  Validation.lean   -- accumulating applicative
  Emit/Core.lean, Emit/Rust.lean, Emit/Certified.lean, Emit/Registry.lean

TextKit/TextKit/
  Grammar.lean      -- the node types + table + unambiguous field (see 03)
  Lex.lean          -- token rows + scanner (Substring positions)
  Parse.lean        -- combinators, ParseOutcome, ParseError (host)
  Guest.lean        -- the guest-thin adapter (bytes, ids only)
  Inversion.lean    -- declare_inversion (per-ctor ladders + parse∘emit)
  Dsl.lean          -- dsl! (elaborator + unexpander + printer generation)
  Diag.lean         -- the diagnostic envelope (shared with CodegenCore.Errors)
  FormatLaws.lean

TestKit/TestKit/
  Spec.lean         -- ONE Spec (positives + negatives + vacuity in type)
  Verdict.lean      -- differential verdict (expected/observed/category/payloadDiffAt)
  Golden.lean       -- stripped byte-tie + golden check
  Audit.lean        -- the emitter self-audit rule set
  Shrink.lean       -- minimal-counterexample strategy (12 §5)

schema-core/                       (new package, core-only, mathlib-free)
  Ty.lean, Value.lean, Field.lean, HasCol.lean, RowVals.lean, ColPath.lean,
  VExpr.lean, ExprLang.lean, Lens.lean, Codec.lean, CodecValue.lean,
  DefaultVal.lean, Bridge.lean     (Ty → Substrait SType)

wasm-core/ (new package / lean_lib, core-only)
  Wat.lean, Op.lean (SemOp table), Sem.lean, Layout.lean, Audit.lean

dbsp/, Machines/                   -- unchanged homes (C2 theory)

schema-lang/ (C3)                  -- keeps only the app layers
  Universe.lean                    -- the One Universe value + snapshot/breaking
  Invariants.lean, Updates.lean, Keys.lean, Witnesses.lean, Migrations.lean
  Meta/                            -- command handlers (register/derive per lane)
  Emit/*                           -- the emitters (target folds)
  Vortex/*
per-product: faults/, gates/, oracle (wasm-backend leaves), forge, edgepython, qlang
```

The future QL is a C1 consumer: schema-core types + ExprLang expressions +
Bridge→SType + Ckt semantics + substrait wire.

## 6. Correctness distribution

Boundaries = types (unrepresentable/instances/defaulted fields); between =
generated/decided; relational content only = hand theorems, once, cited.

## 7. Key signatures (detail lives in 03/12)

```lean
-- Statement (05 §1): the ONE checked-fact shape
structure CheckedStatement (α : Type) where
  P        : α → Prop
  check    : α → Bool
  sound    : ∀ a, check a = true → P a
  complete : Statement.Completeness P check   -- .missing | .proved
-- mounts: gates/lints/tests/obligations created from one statement

-- Emitter outputs carry uniqueness IN THE TYPE
structure Emitter (Spec : Type) where
  outputs : List String
  outputs_nodup : outputs.Nodup := by decide
  law : Option (Spec → Prop) := none
  run : Spec → List GeneratedFile     -- TOTAL (07 §1)
```

See 03 for Grammar/ParseError/ParseOutcome; 12 for Effect/Liveness/ModelCheck/
Causal-trail.

Note: this file is the TARGET STATE. Migrations happen phase-by-phase (11), each
gated; the module tree above is where every phase ends, not where it starts.

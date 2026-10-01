# Design — the FLATLAND rewrite on the mandate tree

**Status: design.** The re-architecture of `/home/evan/flatland` (v2 rebuild,
pre-implementation) around the mandate tree, Lean-central. The owner's
directives govern: (1) best practices + Lean more central; (2) simplify and
streamline where possible; (3) rethink what is unlocked by the current
approach; (4) ESPECIALLY — the Lean qlang is used rather than DataFusion as
the mandatory compiler.

Doctrine slots this note names: 01 §1–§5 (the three roots, the Change
ladder, the carrier, the spine, the relational engine), 02 §1–§10 (the data
plane: valid worlds, weights, keys, the optimizer as proof engine, the
violation relations, materialized queries), 03 §3/§7/§8 (Lean defines what
Rust demonstrates; the trichotomy; validity at the boundary; incremental
violation relations), 04 (the obligation ladder, certificates, observers),
05 (emitters, the deriving protocol), 07/09 (recipes, gates, byte-tie),
12 (construction patterns), 15 #7–#9 (the env-log, deriving, machine!-
entourage patterns), 16 §1–§6 (the two idioms, the six-word vocabulary, the
evidence entourage, the game-engine activation), wave-30 E1–E7/F2/F5, and
flatland's own `notes/lean/SPEC-core.md` + `REBUILD-architecture.md` +
`REBUILD-fork-leverage.md` (the ancestors — mined, never migrated in place).

Evidence basis: flatland's code read (verified this session) —
`flatlandc` 15.7k raw LOC (~11.2k src + tests), `flatland-core` 42k raw
(23.8k audited engine core per fork-leverage's disposition audit), plus the
sibling findings: the DataFusion plan-walk, the closed ~20-template set
mirrored 4–5× (`classify_expr.rs` / `FusedTemplate` / dispatch / `fused.rs`
/ `kernel_spec.rs` — the "mirrors" comments are in the files), the
`col OP literal` hard error (`extract.rs:254,452–478`).

---

## 0. The verdict in one paragraph

flatland's compiler exists because flatland's authoring surface is SQL +
comment annotations — a foreign syntax that needs parsing, planning
(DataFusion), annotation extraction, and classification into kernels. Every
one of those stages is machinery the mandate tree does not need: the authoring
surface is `table!`/`qlang!` (Lean-native, elaborated, reified), the typed Q
IS the plan, the optimizer's rewrites are checked not trusted, and the kernel
set is one generated table instead of five hand-synced mirrors. flatlandc —
11k+ LOC whose full-time job is bridging SQL-comment-land to a closed
template enum — dissolves into the query lane it was imitating. The runtime's
defensive perimeter (health checks, poison flags, per-kernel rollback,
flow-group atomicity) shrinks to boundary checks, because the interior is
carried by proofs that flatland does not have and the mandate tree already
landed.

---

## 1. The compiler's dissolution — the pipeline

The pipeline replaces `SQL dir → annotation extraction → DataFusion planning
→ classify → one vortex spec file` with five stages, each an existing
mandate-tree discipline:

```
Stage 0  AUTHOR    table! / qlang! / rule declarations   (16 §2; E1)
Stage 1  ELAB      reified items in the registry         (01 §5; 15 #7)
Stage 2  TYPE      qlang! → the typed Q                  (02 §2; F2)
Stage 3  OPTIMIZE  checked rewrites over the typed Q     (02 §6; F5)
Stage 4  SELECT    kernel selection = one generated table (05; 12 §2)
Stage 5  EMIT      Rust kernels + the spec wire          (01 §5; 05 §2; 09 byte-tie)
```

### Stage 0 — authoring (what dies: SQL + @annotations)

The five authoring concepts survive from SPEC-core — Schema / Query / Update
/ Invariant / Tick — but spelled in the six-word vocabulary (`table`, `key`,
`ref`, `rule`, `state`, `event`), riding the `table!` clause macro
(design-authoring-surface.md; the machine! precedent, 15 #9):

```lean sketch
table Unit v2 where
  key id
  hp : UInt32 @range(0, 10_000)     -- a dtype FACT, not an annotation
  mana : UInt32 @range(0, 10_000)
  forbid NonNegativeHp := hp >= 0
  rule Regen every 3 := update u where u.hp < 10_000 | u.hp += 1
  query Wounded := Unit where hp < 10_000
```

The annotation extractions die one by one, each into a named slot:

| flatland mechanism | Dies into |
|---|---|
| `@primary_key` SQL comments | `key` clause → `KeyDecl` rows (Keys.lean; 02 §3 — keys are determinacy theorems, driving API shape) |
| `@range` SQL comments | the refinement rides the extension dtype (SPEC-core §1); a `ShapeFacts` input to encoding selection |
| `@rule` SQL files | `rule` clauses → registry `UpdateItem`s — reads/writes DERIVED from the body, never declared |
| `@retention` | materialized-query policies (02 §10) + the vortex retention laws |
| gates / rates / flow groups / observers | SPEC-core §6's dissolution table — verbatim; guard = part of the body, rate = reads `$tick`, trigger = `D(filter p)`, flow group = overlay-segment rewind |

### Stage 1 — elaboration (the reified core)

Items register through the ONE reflection path into the registry (01 §5 —
the accumulated event log; 15 #7). The compile-to rule (16 §2) holds: every
surface word names which machinery it compiles to, or it does not exist.
A schema the wire can't carry fails at elaboration (SPEC-core §1) — the
projection to vortex dtypes / the generated host types is total and checked
(the ptype-table discipline; the lean mirror byte-tie, 09).

### Stage 2 — the typed Q (what dies: DataFusion, the WHERE restriction)

`qlang!` lowers to the schema-indexed typed Rel (query/Query/TypedBridge.lean;
02 §2's fragment) — the SAME term is the executable query, the constraint
input, the maintenance input, and the classification input. DataFusion is
not in the pipeline at all: there is no SQL to plan, no plan node zoo to
walk, no external planner to trust. This is the owner's directive made
concrete: **the query lane IS the compiler.**

**The WHERE restriction dies honestly.** flatland rejects any predicate
outside `col OP literal` at compile time (`extract.rs:452` — a hard error).
The rewrite replaces the hard error with the fragment discipline (02 §2's
honest boundary): the typed Q's predicate is classified into

- **the kernel-eligible fragment** — pointwise comparisons over literals and
  columns → the closed kernel floor;
- **the interpreted fragment** — anything else the evaluator accepts →
  runs on the Lean-evaluated / guest path with its cost named;
- **the refused fragment** — what the wire can't carry → the QL00xx
  E-code with the did-you-mean (the QL0002 standard), at ELABORATION, at
  the declaration site — not a Rust compile error, not a parse rejection.

Nothing is silently slow or silently wrong: the fragment is a property of
the TERM, checked once, carried on the wire as the recipe's class.

### Stage 3 — the checked optimizer

The optimizer is a proof engine (02 §6): untrusted search proposes the
rewrite sequence; the kernel checks each rewrite against the semiring's
equational theory (02 §4 — `h (evaluate Q input) = evaluate Q (h input)`;
F5's foundation). Rows: selection fusion, projection pushdown, join
elimination via keys (02 §3 — determinacy theorems make the join
disappear under the right semantics), and F2's landed join reading
(`join'` + `joinCond` + the completeness mirror). The optimizer emits
`optimized Q + proof` — the certificate pattern (04 §3). flatlandc's
`optimizer/` (an untyped per-plan pass over DataFusion nodes) becomes rows
in the checked rewriter's table.

### Stage 4 — kernel selection (what dies: the 4–5 mirrors)

flatland's killer maintenance bug: the closed template set (~20 shapes:
AddConst/Min/Max/Clamp/FkLookup/CaseWhen/GroupedAggregate/VectorAdd/…) is
hand-synced across `classify_expr.rs` (classification), `FusedTemplate`
(the type), dispatch, `fused.rs` (bodies), `kernel_spec.rs` (the wire) —
the file comments admit the drift. The rewrite: **the template set is ONE
table in the Lean core** (the declare_binop pattern, TOOLKIT §6; the
description layer's deriving protocol, 05 §3), and the five consumers are
GENERATED projections of it:

| Consumer | Generated from the table |
|---|---|
| classification | the guard column (a decidable match over the typed Q's shape — `decide` territory) |
| kernel type | the row type (the recipe / KernelRecipe) |
| the Lean oracle `eval` | the denotation column (the oracle evaluates the SAME rows the engine runs — REBUILD-lean's wire-makes-the-oracle-honest law) |
| the Rust kernel body | the emitter (Stage 5) |
| the duel vectors | the row's sample instances (C6 — the op table → duel rows) |

A new rule shape = a new row + its law, never a 4-file mirror edit. The
linearity classification (linear/bilinear/nonlinear — lean-v3 §4.1) is
derived per row; the old_values capture policy derives from IT (never
hand-set); the `CertifiedFixpoint` witness attaches where the read/write
graph's SCC needs one. Row-shape certification (`write ⊆ read ⊆ in-bounds`,
SPEC-core §7.4's H2) rides the recipe as a generated check.

### Stage 5 — the emitters

The emitter is an interpretation (01 §5): the typed recipe → the grammar of
the Rust target. Emission targets the fork's verbs — `RawParts` views,
`affine` (encoded-domain FoR ref-bump / dict values-map / constant rewrite),
`diff`/`neq_indices`/`scatter`/`group_indices`/`merge_in_place` (the
fork-leverage disposition wholesale: the per-ptype hand bodies of
`fused_kernel.rs` — 2,882 LOC, f64-cast, 13 alloc sites — become generated
bodies over native-lane fork verbs). Artifacts are byte-tied, one writer
per path, the artifact-header gate enforces it (09). The spec wire (the
vortex spec file) is the same emitter's second face.

**The compiler's honest residue:** an `exe` driver + the emitter templates —
the estimate is ~1.5–2k LOC of genuinely new code, all of it in the
mandate tree's existing lanes (query + schemacore Emit + vortex), zero of
it a parallel machinery.

---

## 2. The runtime's re-architecture

flatland's tick today: poll deltas → rate-nudge → coalesce (BTreeMap,
determinism) → cascade (fixpoint with per-kernel rollback + flow-group
atomicity + max-passes budget) → lifecycle → journal. The rewrite maps each
phase to landed machinery and shrinks the defensive perimeter:

| flatland mechanism | Status in the rewrite | Doctrine slot |
|---|---|---|
| the tick (settle → cascade → resolve → commit) | SURVIVES as the machine's step; the four-phase construction is SPEC-core §7 verbatim — it was already right | machines; 16 §6 |
| the cascade = fixpoint | a MACHINE instance; convergence is the ZSet elision discipline — seminaive ≡ naive with the convergence witness, fuel-bounded `fixFuel` + decidable `converged` (the classical choice evaporates) | zset; 02 §9; the tree's landed machines |
| per-kernel rollback + flow-group atomicity | REPLACED. The overlay's (row, S0, new) triples ARE the undo log; rollback = write S0 back; flow groups = overlay-segment rewind — no backup machinery, no poison flags | 01 §2 (the Change ladder); 03 §7 |
| the defensive perimeter (health checks, poison flags) | SHRINKS to the boundary. Validity belongs at the transaction boundary (03 §7): check after the whole atomic batch; the interior is carried by the proofs — a kernel whose row-shape is certified needs no runtime guard | 02 §1 (`ValidDatabase`); 03 §3 |
| max-passes budget | the tripwire: certified stages keep the cap as a fault-tripwire (hitting it is an engine bug, not semantics); uncertified never runs | SPEC-core §7.5; 04's monitor tier |
| coalescing (BTreeMap for determinism) | the zset canonical ordering — already the exec twin of the theory zset, merge/revert PROVED | zset; 01 §2 |
| determinism spine | external inputs + seed ⇒ chain hash; RNG = total `draw_u32` per-update stream hashes; the test IS the duel (candidate vs baseline, same seeds, table equality per tick) | 16 §5.3 (reflexivity-as-determinism); the duel lane |
| journal | the delta log + snapshots — PROVED crash recovery (the torn-tail recovery theorem; the fusion bridges: journal = D∘run, replay = I∘journal) | machines/Crash; A5; 03 §7 (the trichotomy: journal causal, delta net, event recorded) |
| observability (`observe`) | the GENERATED fast-observe face: E-codes map onto `#[code]` verbatim; one registry, two faces; the observer-transparency theorem (instrumented refines plain) | faults lane; C1 |
| config | the config face — a config IS a schema record; the override fold IS the update lane; sources are TextKit grammars | 08 #34; C4 |
| game logic in wasm | the guests as landed: edgepython for the game's scripting; the capability valves (the closed effect lattice) are what the sandbox IS | wasmcore; D1/D3 |
| schedule | GENERATED DATA — the stratified stage walk + per-SCC fixpoint on the wire (REBUILD-architecture T1.1); the schedule-equivalence theorem (both schedules fix the same strict operator ⇒ `fix_unique`) is the proof to land FIRST, its hypotheses explicit | 02 §6; SPEC-core §7.4 |

**What the runtime keeps that the mandate tree does not supply:** the
Column {base, overlay} write funnel, the cursor cache (ptr, epoch), and the
per-tick fault policy — ~3–4k LOC of engine glue, all of it the ReprOp home
the Lean oracle needs a seam against (fork-leverage's "rules" section holds
verbatim).

---

## 3. The encodings — mapping + the absorb discipline

| flatland `Encoding` | Mandate tree | Note |
|---|---|---|
| Primitive | identity / BitPacked(width) | the fallback row |
| Constant | Constant | `cardBound == some 1` guard (Encoding.lean) |
| FoR | FoR(base) | the `foRGuard` |
| Dict | Dict | `lowCardMax`, FK/enum/low-card |
| BitPacked | BitPacked(width) | small int range |
| Patched | the overlay (engine state) + upstream `Patched` as the compaction target | the addendum's two verifications owed |
| Sparse | Sparse | kept |
| — | RunEnd, Sequence, ALP | mandate-tree UPGRADES flatland lacks (its hot set had none) |

Selection is the pure function from `ShapeFacts` (Encoding.lean's `select` —
already landed, the flatland policy "compiler predicts, never searches"
adopted as the design note design-vortex-encodings.md prescribes), with the
`applicable` predicate + totality proof + the coverage obligation.

**The absorb discipline.** flatland's `dispatch/absorb.rs` (1,334 LOC:
ABSORB_TABLE probing per write — encoding × trigger × uniform) dies into
the mandate tree's absorb arms: `absorbConst` / `absorbFor` / `absorbDict`
/ `absorbAOp?` (vortex/Vortex/Compute.lean) — a Lean FUNCTION with laws, not
a Rust table probe. The compiler emits the resulting policy byte on the wire
(T1.2); the runtime reads it; the `absorb_for_ref` overflow bug class dies
because the fork `affine` checks (the fork-leverage rule). The 4-D absorb
table becomes the generated policy — the wire, not the runtime search.

**Compute-on-compressed vs the hand decoders.** The cursor collapses to a
thin `RawParts` wrapper (the fork-leverage disposition: `cursor.rs` 1,446 →
≤300 LOC; the 11 canonicalize/to_vec sites die). Where compute-on-compressed
is sound (the FoR ref-bump, the dict values-map, the constant scalar — the
sound cells the 0L research established), the kernel operates in the encoded
domain and the decode never happens; where it isn't, the `RawParts` typed
view is the honest materialization. Every such swap is a ReprOp square:
`abs(opR r) = opA (abs r)` — proved once per shape, differential-tested at
the boundary (03 §5).

---

## 4. What is UNLOCKED (the rethink)

1. **The proved cascade.** Convergence is a theorem (seminaive ≡ naive, the
   witness `(R i)^[n+1] 0 = (R i)^[n] 0`), not a max-passes hope. flatland
   cannot state this; the tree proved it.
2. **A new rule shape costs one row.** flatland: classify_expr + FusedTemplate
   + dispatch + fused.rs + kernel_spec.rs, hand-synced, drift-prone (the
   comments admit the bugs). The rewrite: a query fragment + the optimizer's
   rows + one table entry; the four consumers derive, the byte-tie gate
   catches any residue.
3. **The WHERE restriction's death.** `col OP literal` or compile error →
   the typed Q's fragment classification: eligible / interpreted / refused
   with an E-code at the declaration site. New predicate shapes are ROWS,
   not compiler surgery.
4. **Observability for free.** Every schema operation emits its fast-observe
   face from the registry (C1); the span-coverage gate enforces it; the
   observer-transparency theorem replaces "instrumentation can't break
   prod" as a hope.
5. **Save versioning = the migration lane.** `v1→v2 + v2→v3 = v1→v3` (group
   addition over the diff zset); upcasters derived; the refusals at
   elaboration; the LOCAL preservation equation + one induction for replay
   preservation (08 #19; 03 §7 — upcasters work on deltas).
6. **Determinism as the duel.** The candidate-vs-baseline duel on identical
   seeds IS the desync test — and the three-way duel extends it to wasmi
   (D1) when the portable verifier lands.
7. **Wasm guests for game logic.** edgepython runs the game's scripting
   inside the capability lattice — the sandbox is the effect rows, not an
   honor system. A component that can't import a clock can't desync.
8. **Benches as duel rows.** The 10K/200K workloads are duel pairs
   (candidate vs flatland baseline, same inputs, threshold verdict) — the
   acceptance criterion is a gate, not a slide deck (C2).
9. **Netcode's delta-is-the-wire = the journal's discipline.** The same
   signed-bag delta is what the journal folds, what the wire carries, and
   what replica reconciliation subtracts — one algebra, D/I absorbing all
   four (journal/checkpoint/replay/netcode), the inverse pair PROVED.
10. **The oracle.** One property covers the whole lowering stack: compiled
    execution ≡ authored semantics, table equality per tick, the model
    evaluating the SAME recipe rows the engine runs. flatland needs ~N hand
    suites for what this buys in one sweep + control.

---

## 5. The simplification ledger

Verified counts (raw `wc -l` over `crates/`, excluding target dirs; the
audited-engine figure from REBUILD-fork-leverage's disposition audit):

| flatland crate | Raw LOC | Fate in the rewrite |
|---|---|---|
| flatlandc | 15.7k (~11.2k src) | DISSOLVED — ~2k of emitter residue in the tree's lanes; the rest is the SQL/DataFusion bridge that has no consumer |
| flatland-core | 42k raw / 23.8k audited engine | REWRITTEN to ~5–7k: cursor ≤300, absorb ≤150, fused bodies → generated, snapshot/undo → overlay rewind, encodings → the vortex lane, delta/zset → mandate-delta, journal → the delta log |
| flatland-journal | 4.8k | the delta log + snapshots (PROVED recovery replaces the hand format) |
| flatland-substrait + flatland-query | 3.3k | the query lane (qlang! → typed Q → eval — already landed) |
| flatland-derive | 1.8k | the deriving protocol (landed) |
| flatland-hex | 0.5k | tensor rows over the vortex layer (see risks) |
| flatland-net | 2k | the journal's discipline + the connector rows |
| renderer + gfx + ui + ui-kit | 32k | ORTHOGONAL — see §7 |

**The honest estimate:** flatland's engine + compiler ≈ 35k audited LOC of
correctness-bearing machinery → the rewrite is ~8–10k LOC of engine glue +
guest logic ON TOP of the mandate tree, with the tree supplying (already
landed, already gated): the query lane, the vortex layer, machines, zset,
the delta log, faults, config, the wasm guests, the gates, the duel/bench
disciplines. The dissolved layers, named: the SQL frontend, the DataFusion
dependency, the annotation extraction, the closed-template classification
mirrors (×4–5), the absorb-table probe, the per-encoding cursor paths, the
per-kernel rollback + flow-group backup machinery, the hand journal codec,
the hand determinism tests, the hand config parsing.

---

## 6. The migration's shape

**Parallel-run discipline: the rewrite lives alongside flatland; flatland is
the baseline the duel beats.** No layer swaps until its duel pair is green.

| Phase | Content | Acceptance |
|---|---|---|
| M0 — the oracle first | The Lean model's evaluator vs flatland v1 journals (Replay.lean shape); the shared trace format | differential green on flatland's own replay corpus; the model validated before any new code |
| M1 — the schedule-equivalence proof | stratified walker ≡ queue cascade, hypotheses H1–H5 explicit (SPEC-core §7.4) | the theorem lands or names the design constraint — BEFORE the stage walker is built |
| M2 — the authoring surface | `table!` with key/forbid/rule/query clauses (E1) + the encoding selection wired (design-vortex-encodings) | a 10K-entity schema elaborates; every annotation of the flatland fixture dir has a clause spelling |
| M3 — the compiler pipeline | Stages 2–5: typed Q → checked rewrites → kernel table → emitters | the duel vectors generated per kernel row; the byte-tie gate green; a new template costs one row (the acceptance DEMO) |
| M4 — the runtime slice | Column{base,overlay} + cursor-on-RawParts + the four-phase tick as the machine + the delta log | the 10K-entity tick end-to-end (E4's dogfood); crash-recovery duel vs the proved model |
| M5 — the parallel run | mandate tick vs flatland tick on the same workloads; the 10K/200K benches as duel pairs | parity-or-better verdicts; table equality per tick across the corpus |
| M6 — the perimeter shrink | delete the defensive layers flatland needed because it couldn't prove: poison flags, per-kernel backups, flow-group atomicity, hand snapshot machinery | the dogfood runs with the boundary-only checks; the fault lane catches what the proofs don't carry |
| M7 — the guests + faces | edgepython game logic, the config face, the fast-observe face, netcode on the journal discipline | the quickstart walks the loop (E7) |

Each phase = one vertical slice per the execution protocol (v3 README);
the 07 recipe entry + the 08 spec line FIRST; the audit loop at the phase's
end.

---

## 7. The honest risks (what the mandate tree does NOT yet cover)

1. **The renderer / UI.** flatland's 32k LOC of renderer/gfx/ui/ui-kit are
   orthogonal to the data plane and NOT rewritten — they consume the tick's
   outputs through a seam the rewrite must define (the materialized-query
   face, 02 §10). Until a renderer consumes the generated host, "the game
   runs" is unproven. The projection face is designed (16 §6) but not
   exercised at frame cadence.
2. **The tensors' compute depth.** flatland-hex's grid/hex tensors run on
   the fork's `vortex_tensor` fns; the mandate tree's vortex lane has
   fixed-shape vectors + the compute-on-compressed arms but no
   tensor-kernel depth (contractions, neighborhood sweeps). The hex slice
   is small (0.5k) but the compute it needs may force fork verb donations
   not yet queued.
3. **The fork's SVE verbs.** The research verdict stands: the fork's SVE is
   NET-NEW on both sides (cursor.rs's arm is dead code — wrong cfg +
   wrong intrinsics). Every "parity-or-better" duel on aarch64 that leans
   on SIMD tiers is a donation first, a duel second. The NEON ceiling for
   8/16-bit gather caps narrow-integer loops (u32 keys stay the convention).
4. **The schedule-equivalence proof is OWED** (M1) — if the hypotheses fail,
   the stage walker's shape changes and the tick re-architecture re-plans.
   This is why M1 precedes M4.
5. **Float determinism.** Game code wants floats; the tree's honest answer
   is the semantic-profiles lane (`Float Deterministic` fixed-point vs
   `Float Fast` with the forfeited laws NAMED) — designed (E2), not landed.
   The f64/2^53 hazard that the fork's f64-cast kernels shipped with is the
   standing counterexample.
6. **DataFusion's residual breadth.** SQL features flatland's surface
   silently inherited (full expression breadth, planner-side rewrites)
   become the interpreted fragment or named refusals. The first real game
   schema will exercise this; expect QL00xx rows to grow.
7. **The interpreter-gap at scale.** The Lean oracle evaluates the recipe
   rows; its speed is elaboration-speed, not tick-speed. "Playtest in the
   model" (REBUILD-lean Part 13) holds for mechanics, not frame budgets —
   frame budgets stay the cost lane's bench discipline.
8. **flatland upstream movement.** The fork rebase risk (206 commits, the
   stats/ hazard) and flatland's own v2 build may land while the rewrite
   runs. The parallel-run duel discipline absorbs drift, but the baseline
   pin (a flatland commit hash per duel row) must be recorded per row.

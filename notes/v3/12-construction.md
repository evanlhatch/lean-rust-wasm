# 12 — The construction handbook (mechanical patterns for building)

**STATUS: current-tree** — the file paths below are the CURRENT tree's
(the mining source). The new tree's homes come from 14 + the scaffold;
the PATTERNS are durable, the paths are not.

How to actually build each kind of thing, with the exact shapes to
follow. An agent executes from this file + the doctrine (00–10) with no
conversation. The patterns are load-bearing: deviating without a written
reason is a review failure (10's checklist).

## 0. The universal recipe (read before anything below)

Every new thing: (1) name its root + carrier grade + spine reading +
ladder rung + gate row (01's five questions); (2) write its 07 recipe
entry + its 08 spec line; (3) land the vertical slice (declare → derive
→ artifact → byte-tie → duel); (4) run the gates (`just gates` — or
`--package X` shards while iterating); (5) diagnostics land in the same
change (the Diag shape + the E-code row + the curated rendering).

The build discipline (post-monolith): build from the repo root
(`lake build <Lib>`); test via the per-library exe
(`(cd lean/<lib> && lake --dir ../.. exe <Lib>Tests)` — the cwd carries
the fixture paths); the gates exe runs as
`(cd lean/gates && lake --dir ../.. exe gates <subcmd>)`; the Lean
toolchain is pinned (leanprover/lean4:v4.33.0 — elan provides it);
Rust runs under `devenv shell --profile wasm` with the CC export
(`export CC=$HOME/lean-rust-wasm/.devenv/profiles/wasm/profile/bin/cc`).

## 1. A new schema item (record / variant / function)

```lean sketch
@[schema]               -- registers the item in the universe's extension
structure Order where   -- a record: fields are the schema
  id : UInt64
  customerId : UInt64
  total : Int64
deriving WireCodec      -- the codec + its law, generated (thin wrappers)

@[schema_fn]            -- a function: its signature registers;
def getOrder ...        -- the impl lives in the impl module (GuestlangStd
                        -- for guest fns) — the guest-marking attrs
                        -- (@[guest]/@[guest_std]) gate guest-compilation
```

Rules: field types from the closed `Ty` (a new ctor touches every closed
fold — the compiler drives it); a key field rides `schema_keys`
(02 §3's determinacy); the record gets its row bridge (the Iso to its
RowVals) + its codec + its generator via the deriving protocol — never
hand-derived pieces of the same shape.

## 2. A new lane (invariant/update/witness/…)

The lane skeleton (follow an existing one — Keys.lean or
TableInvariant.lean are the references):

1. The item type + the env extension (`mkRegistryExt`-shaped — the
   append-only log; replay = the materialization).
2. The attribute/command mount (`register_check_attribute` for the
   decl-check shape; a `schema_*` command for the grammar shape — the
   clause kit + didYouMeanSuffix + freshNameCheck from GenKit).
3. The WF/legality: the inductive relation + the decidable checker +
   the bridge theorem (sound; completeness via the loud two-constructor
   choice) — the Statement instance; the mounts (gate/lint/test/
   obligation).
4. The obligation view: `obligation : Item → Obligation` + the tier
   computation + the discharge via the kit backends
   (`decideEvidence`/`decideDischarge` — never a hand-rolled trio).
5. The emitter rows (folds over the lane's data; the byte-tie).
6. The test section: a fixture + the positive pins + the mandatory
   negative controls (the PropSpec `control` field is structural — a
   suite without its control doesn't construct).

## 3. A new emitter

```lean sketch
def myEmitter : Emitter MySpec where
  name := "myEmitter"
  outputs := ["src/my_generated.rs"]        -- nodup in the type
  law := some myLaw                          -- or a header note why not
  run spec := …                              -- PURE + TOTAL: the fold
```

Rules: outputs disjoint across ALL emitters (global ownership — the
gates check it); the driver writes via `runEmitters` (never hand IO);
the artifact's header is the standard 2-line GENERATED block (the
content hash is the tie); the self-audit's rule set applies; the law
cites existing theorems where they exist (the vortex/circuit precedent:
`vortexLaw` cites `checked_field_*`). If the law needs the checked
universe, the emitter consumes `CheckedUniverse` (the defensive arms
die by construction).

## 4. A new codec / wire format

- The payload type's codec: `deriving WireCodec` where the structure
  fits (atoms + products + sums + options + lists) — the law is an
  instance field. Hand-write only what the handler refuses (it refuses
  LOUDLY with the unsupported fragment named).
- A text format: a TextKit grammar value (05 §1) + `declare_inversion`
  — never a hand parser/printer pair.
- The round-trip: a RoundTripSpec (the suite + the mandatory negative
  control assembled once) — never a hand-assembled property test.
- The guest-compilable half: the guest-thin adapter (bytes + Nat-free
  ids) with the boundary conversion (the witness lane is the model).

## 5. A new machine / lifecycle

```lean
machine! myMachine where
  states: [new, active, done]      -- the entourage generates: the state
  …                                -- enum + the table + the tie theorem
                                   -- + DecidablePred + the conformance
                                   -- battery, all from the clause data
```

An entity lifecycle (a state column on a record + transitions as keyed
updates): `schema_entity_machine` (the preset — it composes the record
+ the machine + the updates + the obligations). Hand-built machines
carry a written reason (the OrderMachine precedent: the preset rejects
some honest machines — the header says why).

Rules: guards/legality discharge at the tightest tier; the generated
entourage's names are the convention (`<m>States`, `<m>Trans`,
`<m>TableStep?_eq_step?`); a new clause rides the clause kit (never a
hand-rolled clause parser); the unknown-clause error enumerates the
legal clauses + did-you-means.

## 6. A new DSL (the authoring surface)

Third-or-later DSLs MUST ride `dsl!` (05 §1): the grammar spec with
labels + payload correspondences generates the category + elaborator +
unexpanders + printer. The curated instance-gate failure is part of the
surface (04 §3's shape in 05). Before writing ANY surface: check whether
the surface is a grammar (TextKit) or a clause command (the GenKit
clause kit) or a Lean attribute (register_check_attribute) — the three
existing shapes cover the space.

## 7. A new gate / check

A gate is a row in the gates exe's registry (Gates/Packages + the
report-gate combinator in Gates/Common): config + analyse + render +
the baseline discipline (write-or-diff with the loud re-baseline — a
content-changing re-baseline is a deliberate act). The gate's output is
a Verdict (ctors, never strings) + the exit code. Mounts available:
gate (CI), lint (guestlang-lint), test (TestingKit), obligation row,
duel (the oracle), monitor (runtime) — one Statement, many mounts.

## 8. A new Rust host capability

- The error surface: never hand-write error types — declare faults in
  the Lean registry (`@[fault]`/`@[host_fault]`); the fast-observe
  `error!` blocks generate; the codes allocate from the persisted
  E-code registry (stable — never position-derived).
- The observability surface: spans derive from the world (the
  observability emitter); generated host code without span coverage
  fails the self-audit.
- The runtime: wasmtime in guestlang-host; the skew check at startup;
  the witness verification via `verify-witness`; errors flow as
  fast-observe Faults (the causal trees) — never bare panics on real
  error paths (documented invariants keep their panics with comments).
- Tests ride the shared harness (tests/common/mod.rs) + the bolero
  fuzz layer for parsers/decoders (never-panic floors + the fixture
  differentials).

## 9. The disciplines that apply to EVERYTHING above

- The byte-tie is law: never hand-edit a generated file; regen is a
  deliberate commit-visible act; the header's volatile lines are exempt,
  the content hash is not.
- One writer per artifact path; the outputs' nodup is in the type.
- Zero sorry/axiom; a missing theorem is information, a stub is a lie;
  the axiom gate's baselines re-sync with the `--write` discipline (a
  content-changing re-baseline is deliberate).
- Negative controls are mandatory and structural (the PropSpec control
  field); a gate without teeth gets a sabotage row.
- The docs-check gate: notes' Lean fences name real decls or tag
  themselves as sketches.
- jj discipline: one work order per commit; describe once known;
  `jj undo`/`jj new`, never git checkout/reset/stash; bookmark before
  risky operations.

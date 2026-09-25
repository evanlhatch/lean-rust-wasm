# The Authoring Surface — optimizing the 100th schema

Owner's directive: "the best use case — a project where types and
schemas need to be defined REPEATEDLY; this authoring surface is what I
want to improve the most." This note designs that surface against the
code AS IT STANDS (mandate branch), with a friction census (file:line
evidence), the surface decision, the evolution workflow, the dogfood
product, and the landing sequence.

Doctrine slots this note names (per the diff rule): 01 §5 (the registry
as the accumulated event log; the emitter reads it), 02 §1–3 (the
relational schema — valid worlds, constraints as shared authority, keys
as determinacy theorems), 03 §7 (the trichotomy; upcasters work on
DELTAS), 05 §3–4 (the ONE reflection path; curated failures), 07 R1/R4
(target/DSL recipes), 12 §1–2 (the authoring face; the lane recipe),
15 #7/#8/#9 (the env-extension log, the deriving protocol, the
machine!-entourage pattern), 16 §1–3 (the two-idiom frontend, the
compile-to rule, the evidence entourage).

Read-evidence basis: `schemacore/SchemaCore/{Item,Register,DeriveMeta,
Slice,KeysSlice,Keys,Migrate,Diff,Goldens}.lean`, `scaffold/Scaffold/
{Spec,Generate}.lean`, `machines/Machines/Dsl.lean`, `query/Query/
QLang.lean`, `faults/Faults/{Item,Registry}.lean`, `LedgerApp/
{App,Reg}.lean`, `justfile`, `notes/studies/verified-ledger-study.md`,
`notes/v3/16-surface.md`. The prompt's `notes/rfc-business*` files DO
NOT EXIST in the tree (verified by find) — the domain thinking is taken
from `verified-ledger-study.md` alone; if the rfc files live elsewhere,
this note's §6 should be re-checked against them.

---

## 1. The use case, precisely

**Who.** A backend team evolving an event-sourced product's data model
— the verified-ledger shape (deposit/withdraw/transfer over a replayed
journal, invariants framed per op, a differential harness against the
implementation). Not a protocol author (one schema, hand-polished
forever) and not a data-product team (schemas as Snowflake-flavored
commentary). The user who matters writes v7 of a table on a Thursday
and needs v6's journal to replay against it, the TS client to regen,
the conservation invariant to still hold, and the gates to stay green
before lunch.

**The repeated act.** NOT "adding a schema" (that happens once per
project). The repeated act is **EVOLVING one**: add a field, retype a
field with a remedy, promote a field to key, add a constraint, add a
named query, add an event. The 1st schema teaches the vocabulary; the
100th schema is where the surface's tax is measured. Every step that
costs the same on schema #1 and schema #100 is a step the surface
failed to amortize; every step that GROWS with the schema count
(registrations, string keys, pin fixtures) is the enemy.

**What the 100th schema needs from the surface:**

1. ONE authoring location per entity (today: see §2 — six).
2. ZERO per-entity ceremony that does not state a fact about the entity
   (registrations, replay modules, string cross-references).
3. Evolution as a first-class declaration, not a diff-and-pray.
4. Every failure at the declaration site, in the ONE Diag envelope,
   with the did-you-mean (the QL0002 standard, Query/QLang.lean:20).
5. The entourage (types, codecs, faults, spans, queries, tests) arrives
   without being requested — and every row of it is tied.

---

## 2. The friction census — one entity, today

Measured over the live tree. To add ONE entity `T` (say `Order`) and
evolve it once, the author touches:

| # | Step | Evidence | Hand-written? |
|---|---|---|---|
| 1 | Author the `@[schema]` structure | `schemacore/SchemaCore/Slice.lean:39,57` — plain structure; shapes ambiguous in plain Lean (`Slice.lean:17`: `List K` reifies to `.list`, the `set` ctor has NO authoring spelling) | yes |
| 2 | Request capabilities per record | `deriving WireCodec` / `deriving row_bridge` per clause (`SchemaCore/DeriveMeta.lean:60–76`; lazy derivation, D12 — nothing derives unless named) | yes |
| 3 | Declare the key in a DIFFERENT module, referencing the record BY STRING | `SchemaCore/KeysSlice.lean:41–46`: `@[key] def exampleKey : KeyDecl := { record := "Example", fields := exampleCheckFields, key := "label" … }` — a separate file (the initializers rule), a string record name, a fields ref to a check-lane fixture | yes |
| 4 | Regenerate + commit the tied artifacts | `just gen` (`justfile:101`, `lake exe schema`) → `gen/schema-slice.ts`, `gen/schema-slice.wit`, `crates/schema-generated/src/lib.rs`; the goldens teeth (`SchemaCore/Goldens.lean:12,445`) fail the build on drift | mechanical (regen) but COMMIT-vision |
| 5 | Update the test pins + write the negative controls by hand | `SchemaTests/RustEmit.lean:31–103` — pinned fixtures over the LIVE lane, the keys tooth, the derivation-agreement pin, the sabotage controls — each re-plumbed per schema | yes |
| 6 | Author fault rows in a SEPARATE lane, name-keyed | `faults/Faults/Registry.lean:32–35` (`@[fault]` def rows of `FaultItem`); the schema↔fault connection is by hand; codes allocated from the persisted registry by name (`Faults/Item.lean:12–16`) | yes |
| 7 | Author queries separately, re-naming the schema's fields | `query/Query/QLang.lean:1–40` — `qlang!{ from <schema> then … }` re-resolves columns by name against the item's field list; no named query is generated with the schema | yes |
| 8 | App consumption by STRING ref | `LedgerApp/App.lean:32`: `ledgerAppItemConsumes : List String := ["Order"]` — the schema is a string in the consumer | yes |
| 9 | Run the gates | `just gates` (`justfile:97`) — axioms report, gen-check, snapshot-check, code-registry, artifact-headers; a missed step is a CI failure, not an edit-time error | mechanical |
| 10 | Evolve v1→v2 | `SchemaCore/Migrate.lean:1–70` — the diff (`Diff.fieldDiffsOf`) + the remedy half (`Diff.lean:202` `FieldMigration`, `:243` `widenBounded`) are hand-registered per retyped field; the upcaster derives, the refusal derives, but the REMEDIES and their soundness obligations are hand rows in yet another location | partially |

**The census finding:** the tree's DISCIPLINE is excellent and entirely
GENERATED-side — one reflection path, one description layer, the
byte-tie teeth, the derived upcaster with its composition law. The
AUTHORING side is what has not converged: **~6 hand locations per
entity + 2 mechanical passes**, at least three of which reference the
entity by STRING (`record := "Example"`, `["Order"]`, fault name
keys). Nothing here is a correctness problem; every item is a
repetition tax. The verified-ledger study's bar — "~100 author lines
reproducing their 1k" — is unreachable at 6 locations × per-entity
ceremony: the ceremony, not the model, is the 1k.

---

## 3. The ideal loop

**The ONE authoring act:** a versioned table declaration. Everything
else is derived and tied. Concretely, the author writes (see §5 for
the full sketch):

```lean sketch
table Account v2 where
  key id
  name : String
  balance : Int64
  forbid NegativeBalance := balance < 0
  query Overdrawn := Account where balance < 0
```

and NOTHING ELSE. From that one declaration, before the next
keystroke:

- the structure exists as a plain Lean record (the macro DESUGARS —
  §4), registered by the SAME `@[schema]` mount (`Register.lean:94`);
- the key rows are emitted as `KeyDecl`s into the keys lane (killing
  step 3's separate module + string ref);
- `deriving WireCodec, row_bridge` is INJECTED by default (killing
  step 2 — the derivation stays lazy, the default is the lazy set the
  100th schema always wants; an explicit `deriving` clause overrides);
- `just gen`'s outputs regen (step 4 unchanged — already the right
  shape: mechanical, commit-visible, gate-enforced);
- the test pins + negative controls SCAFFOLD themselves from the
  schema's own shape (step 5 — the emitter already computes the
  tamper vectors; `Emit/Rust.lean:983–1060` — the pins should be
  EMITTED, not re-plumbed per schema);
- the schema's fault family (decode-refusal per field, keyed by name)
  registers itself into the faults lane (step 6);
- the named queries exist as elaborated `qlang!` terms pinned to the
  schema's field list (step 7);
- the version number `v2` diffs against the registered `v1` (the
  registry IS the event log, 15 #7), derives the upcaster plan
  (`Migrate.FieldPlan`), refuses loudly where the plan can't, and
  accepts inline `remedy:` clauses for the retypes (step 10).

**The invariant that makes this safe:** the macro adds NO new
reflection path. It elaborates to the same plain declarations + the
same attribute mounts; `Describe.reflectItemViaDescr` remains the ONE
route (`Register.lean:71–77`, the D19 convergence); the goldens teeth
stay glued to the live registration. The macro is sugar over the same
registers — a parallel path would be a design failure (the
no-parallel-tables rule).

---

## 4. The surface's shape — which idiom, which form

Three candidates, against the doctrine:

**Data files (a JSON/YAML-ish spec consumed by a driver).** Rejected.
The legacy tree is the evidence of where this goes: `legacy/lean/
schema-lang/` grew a parallel meta-universe to compensate. Data files
lose elaboration-time obligations (the fields-nodup refusals would
become runtime refusals), split the authoring act from the proof
obligations, and need their own parser — the textkit grammar would
earn its keep only if a non-Lean author were the user, and the user
here writes Lean every day.

**The attribute face, extended (field attributes on plain
structures).** The honest TODAY-plus-marges. It keeps 12 §1's
"plain Lean declarations" doctrine and needs no new parser. But it
cannot carry the repeated act's annotations in ONE place: keys are
already forced into a second module + string ref (`KeysSlice.lean:
41–46`); constraints (02 §1's `forbid` — the shared authority),
defaults (the migration lane's `fill` needs a type default), caps, and
named queries have NO field-level home at all; and the shape
ambiguities are real (`Slice.lean:17` — plain Lean cannot spell `set`,
variant items are the named gap). Attributes scale as ATTRIBUTES STACK
PER CAPABILITY — exactly the per-capability ceremony the 100th schema
drowns in.

**A `table`-idiom clause macro (the machine! pattern, the 16-surface
vocabulary).** Chosen. The precedent is proven END-TO-END in-tree:
`machines/Machines/Dsl.lean:1–60` — one declaration generates the
entourage (state enum, Label, spec, table, the table↔step tie,
decidable instance, battery registration), the clause kit is a closed
world with the did-you-mean refusals, and the generated surface IS the
law-carrying surface. 16-surface §1/§2 ALREADY prescribe the
vocabulary (`table Orders { id : u64 key, … }` + the compile-to rule)
— this note is that prescription applied to the schema lane, with the
macro consuming the SAME Descr + Kit.Lane substrate the attribute face
uses today.

**Why the macro fits REPEATED authoring specifically:** a repeated act
needs (a) one location, (b) annotation density (key/ref/default/
forbid/query are PER-FIELD facts no plain Lean type carries), (c)
evolution as syntax (`v2` is a clause, not a convention). The
attribute face wins on none of the three; the macro wins on all
three while desugaring to the attribute face — so the doctrine's
plain-declaration face (12 §1) survives as the macro's EXPANSION, and
the snapshot idiom's six words (16 §2) become the authoring
vocabulary exactly where they are exercised.

**The stream idiom rides free:** the event clause of a table is the
journal lane's face (the fusion bridges are proved — 16 §1); the
delta/upcaster face is the migration lane's. The macro presents BOTH
idioms as clauses of the ONE declaration; the conjugacy underneath is
already a theorem, not this surface's problem.

---

## 5. The concrete design

### 5.1 The grammar (the clause kit — Machines.Dsl's discipline verbatim)

```lean sketch
table Account v2 where
  key id                              -- primary key (determinacy, 02 §3)
  ref customer : Customer             -- a foreign ref (the keys lane's FK rung)
  name     : String
  balance  : Int64
  tags     : Set String               -- the closed universe's spellings,
  status   : variant Active | Closed  -- incl. the two named gaps (Slice.lean:17,
                                      -- the variant-item note)
  forbid NegativeBalance := balance < 0      -- 02 §1: the shared authority
  default tags := .empty
  event Deposited (amount : UInt64)   -- the stream idiom's clause
  query  Overdrawn := Account where balance < 0
  deriving -row_bridge                -- OPT-OUT; WireCodec+row_bridge default on
```

Clause list (closed world, unknown clause → the legal enumeration +
`TextKit.suggestSuffix` — the Dsl.lean:60–70 refusal shape):
`key`, `ref`, `forbid`, `default`, `event`, `query`, `remedy:`,
`deriving`. Colon-suffixed atoms where a term could follow (the
token-pollution lesson, Dsl.lean:53–56). `v<N>` is mandatory from the
second declaration of a name — the first declaration IS v1.

### 5.2 What one declaration expands to (the entourage, per 16 §3)

| Surface word | Compiles to (16 §2's table, instantiated) |
|---|---|
| `table Account v2` | the plain structure + `@[schema]` (the SAME mount, `Register.lean:94`) + the registry's version row |
| `key` / `ref` | `KeyDecl` rows emitted into the keys lane (kills the separate module + string ref); refs drive the key-backed API shape (02 §3: `OrderId → Option Order`) |
| (the structure itself) | `deriving WireCodec, row_bridge` injected — the entourage computed per capability: `DeriveMeta.lean:79–110` — the codec's LCG sweep + mechanical controls + `@[schemaCodec]` registrations, the row bridge's zero-emission where the type carries it |
| `forbid` | the ℤ-weighted violation relation's row (∅ ⟺ valid) + the obligation row (15 #4) + the diagnostic face (the violating rows ARE the payload — 02 §1) |
| `default` | the migration `fill` step's inhabited witness (Migrate.lean's refusal `added field whose type has no default` becomes a DECLARATION-TIME fact) |
| `event` | the Label ctor + EventSpec (the `machine!` entourage's event clause, Dsl.lean:31–38) + the journal lane's delta variant |
| `query` | the named `qlang!{ from Account then … }` term, elaborated ONCE at the declaration (columns resolve by name immediately — QL0002/QL0003 teeth at the authoring site) |
| `remedy:` | the `FieldMigration` row + its soundness obligation, INLINE at the retyped field (`Diff.lean:202,243`'s shape, mounted where the diff can find it) |
| `v2` (the version diff) | `Diff.fieldDiffsOf` v1→v2 → the derived `FieldPlan` + `upcastDelta` + the local law's mount (`Migrate.lean`'s ONE induction, cited) + `MigrationSeed.deriveSeed` (the operator's acceptance stays the WITNESS — the gate still refuses an unwitnessed replay) |
| (every declaration) | the test scaffold: the emitter's tamper/duel vectors rendered AS the pinned fixtures + the mandatory negative controls (15 #5 — the control is in the STRUCTURE, a scaffold without it doesn't construct; `Scaffold/Spec.lean:31–35`'s refusal template precedent) |
| (every declaration) | the fault family: one `@[fault]` row per decode/refusal path (payload typed by the closed `Ty` — `Faults/Item.lean:31`), name-keyed `<table>-<field>-<path>`, codes allocated from the persisted registry by stable name |

Per-schema artifact outputs (regen, not authoring): `gen/*.ts`,
`gen/*.wit`, `crates/schema-generated/src/lib.rs` (the Rust/TS types +
codecs + the migration face, `Emit/Rust.lean:794–943`), the WAT/wasm
lanes' consumption, the goldens (byte-tied, `Goldens.lean`).

### 5.3 What does NOT change

- The ONE reflection path (`Describe.reflectItemViaDescr`) — the macro
  feeds it, never bypasses it (D19, `Register.lean:100–113`).
- The byte-tie: `just gen` stays the writer side; the goldens teeth
  stay the live link; the artifact headers stay the tie.
- The gates: unchanged rows; the surface FEEDS them better (a scaffold
  with structural negative controls makes the suites gate-clean by
  construction).
- The attribute face: survives for the trivial record; the macro is
  strictly richer sugar over the same registers.

---

## 6. The evolution workflow (the repeated act, end to end)

Adding `limit : UInt64` with default 0 to `Account`, as v3:

1. The author edits the declaration: `table Account v3 where …`,
   adds `limit : UInt64`, `default limit := 0`. One location.
2. At elaboration: the diff (v2→v3) computes ONE field addition; the
   plan derives (`fill` at the end, from the default clause); the
   local migration law mounts as a field (a migration without the law
   is unconstructible — `Migrate.lean`'s carrier grade); the seed
   derives, awaiting the operator's acceptance witness.
3. The refusal cases fire AT THE DECLARATION, in the ONE envelope:
   removed field (no value-map target), retyped without a matching
   `remedy:`, reordered/mid-inserted (until the stable-id lane, D13),
   key touched (a migrated key is a different entity set). Today these
   are `Migrate.deriveFieldPlan`'s runtime refusals; the surface moves
   the DETECTION to elaboration without changing the derivation — the
   diff runs against the replayed v2 from the registry (15 #7: the
   registry is the accumulated event log; the versions ARE its rows).
4. `just gen`: the Rust face emits the upcaster + the migration
   bindings (`Emit/Rust.lean:794–943`); the TS client regens; the
   goldens re-tie.
5. `just gates`: axioms/gen-check/snapshot-check green because the
   scaffolded tests carried their controls; the composition law means
   v1→v3 is v1→v2;v2→v3 BY CITATION (`compMigrations`) — no new proof
   per evolution.
6. The journal replays: old rows upcast through the derived plan; the
   witness gate still demands the operator's acceptance (the loud
   refusal for the unwitnessed — `replayMigrated?`).

The author's total hand-written delta for the evolution: the field
line, the default line, the version bump. Everything else is derived,
tied, or refuses loudly at the declaration.

---

## 7. The friction kill-list

| Today's step (§2's census row) | Mechanism that kills it | Zero steps after |
|---|---|---|
| #2 per-record `deriving` clauses | WireCodec + row_bridge ON by default; explicit `deriving` clause only to opt out (lazy derivation D12 preserved — the default IS the named set) | yes |
| #3 keys in a second module, string record ref | the `key`/`ref` clauses emit the `KeyDecl` rows at the declaration; the record ref is the declaration's own name (hygienic — `mkIdentFrom`, Dsl.lean's rule) | yes |
| #5 hand-plumbed test pins + controls | the scaffold emits the pins (the vectors are already computed — `Emit/Rust.lean:983–1060`) + the structural negative controls (Scaffold.Spec's refusal-template precedent) | yes (pins become generated artifacts, byte-tied like every artifact) |
| #6 separate fault rows, name-keyed by hand | the fault family derives per declaration (name-keyed by the table+field names; codes allocated by stable name — the `Faults.Alloc` discipline unchanged) | yes |
| #7 separate query authoring | the `query` clause elaborates the named `qlang!` term at the declaration | yes |
| #8 string consumption refs | `consumes` takes the table's registry name from the mount (the naming fn's key), not a string literal; a miss is the closed-world Diag | yes |
| #10 hand-registered remedies in a third location | `remedy:` inline at the field; the diff finds them by the plan's own walk | yes |
| #9 the gates dance | unchanged as GATES (they are the teeth); killed as STEPS: the scaffold's structural controls + the declaration-time refusals remove the edit-CI-fail-edit loop | mostly |
| #1/#4 (the declaration + the regen) | NOT killed — they are the authoring act and the tie, respectively. The regen stays mechanical and commit-visible | no (correctly) |

---

## 8. The dogfood product

**Proposal: `ledger` — the verified-ledger study grown into the real
small product.** The study already names the success criterion
("~100 author lines reproducing their 1k") and the shape (schema items
+ updates + one machine, the Rust side and the oracle manifest
GENERATED). The owner would actually run it: an event-sourced personal
ledger — accounts, transfers, budgets — with a TS client over WASM,
the journal replayed on open, the conservation invariant enforced.

The dogfood plan exercises the 100th-schema regime deliberately, by
scheduling ≥5 EVOLUTIONS as the product grows real features:

- **v1** accounts + deposits/withdrawals (the verified-ledger core;
  the conservation `forbid` from day one).
- **v2** transfers (a new event + a new ref; the frame conditions are
  the locality family, cited — the study's 146 proof lines collapse to
  `set_neutral` citations).
- **v3** money as a profile (`Money USD Cents` — 16 §4.5's semantic-
  profiles lane; a `balance` retype WITH the inline remedy — the
  honest float tension resolved, not avoided).
- **v4** budgets (a `forbid` over a materialized query — the
  constraint-is-a-query reading, 02 §2).
- **v5** the TS client's named queries (the `query` clauses the
  frontend actually consumes).

Each evolution is the surface's acceptance test: one location, zero
ceremony steps, the upcaster derived, the gates green, the journal
replaying. If v5 costs more than v2 (measured in hand-touched
locations, not LOC), the surface failed and the census re-runs.

The leftover rule: the dogfood is the surface's first CONTENT consumer
— the macro, the entourage emitters, and the evolution face land with
`ledger`'s rows, never as empty libraries ahead of them.

---

## 9. The landing sequence

Each wave is a vertical slice (declare → derive → artifact → byte-tie
→ duel), names its doctrine slot, and lands its tests + negative
controls. No wave adds a parallel path to `Describe.reflectItemViaDescr`.

1. **W1 — the clause kit + the desugar.** `table`/`key`/`ref` clauses
   expanding to the structure + `@[schema]` + emitted `KeyDecl` rows;
   the closed-world refusals (Dsl.lean's kit verbatim); the
   fields-nodup + key-WF teeth at the declaration. Gate row:
   SchemaTests' surface suite + the axiom report.
2. **W2 — the defaulting entourage.** WireCodec + row_bridge default
   on, explicit opt-out; the evidence entourage computed per
   capability (DeriveMeta.lean's emissions, unchanged — now
   requested by the default).
3. **W3 — versioned tables + the evolution face.** `v<N>` registry
   rows; the diff → plan → upcaster pipeline wired to the declaration
   (inline `remedy:`; the refusal cases at elaboration); the
   composition law cited. Gate row: SchemaTests' Migrate suite grows
   the declaration-time teeth.
4. **W4 — the fault family derivation.** Per-table `@[fault]` rows
   from the refusal paths; name-keyed, `Faults.Alloc`-allocated;
   FaultsTests grows the negative controls (a duplicated derived name
   refuses loudly).
5. **W5 — the query bridge + the test scaffold.** `query` clauses →
   named `qlang!` terms; the pins + controls emitted as tied
   artifacts (the scaffold generator's test capability, now fed by the
   schema lane — Scaffold.Spec's `schemacore` exclusion is REVISITED
   here deliberately: the scaffold does not generate the schema; the
   schema's declaration generates its own tests).
6. **W6 — the dogfood.** `ledger` v1–v3 live; the census re-measured
   (§8's success metric); the friction kill-list audited row by row.
7. **W7 — the doc + the recipe.** 12 §1's authoring face rewritten
   around the macro; 15-patterns gains the entry (#9's generalization:
   the table-entourage pattern); 16 §2's compile-to table gains its
   landed-instance column.

**Honest gaps carried (not hidden):** variant ITEMS (the item model is
records-only today — Slice.lean's note; W1's `variant` clause waits
for it or lands with it); the `set` spelling (needs the wrapper-typed
face — named there); mid-list inserts/reorders (the stable-id lane,
D13, is the named follow-up; until it lands the surface REFUSES — the
refusal is the honest size).

---

## 10. The five questions (the surface itself)

- **Root**: META — the surface stage over the description layer (the
  QLang.lean precedent's third layer, applied to the schema lane).
- **Carrier grade**: none of its own — the expansion IS the existing
  core's types (`Item`, `KeyDecl`, `FieldPlan`, the fault rows).
- **Spine reading**: the surface stage — syntax → clause resolution →
  the SAME reflection route → the registry append; the entourage rides
  the existing emitter spine.
- **Ladder rung**: the macro's own obligations (key uniqueness across
  clauses, query column resolution) are `decidableNow` at the
  declaration — kernel decides, never a sweep.
- **Gate row**: SchemaTests' surface suite (the desugar pins + the
  curated refusals + the negative controls) + the code-registry gate
  (the new E-code family) + the axiom report.

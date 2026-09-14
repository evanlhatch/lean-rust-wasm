# Flatland lean-notes → guestlang: the alignment roadmap

Source: `~/flatland/notes/lean/` — SPEC-core.md (keystone), TOOLKIT.md
(constitution), GAPS-to-spec.md (gap list), lean-v3.md (decisions). This
doc maps each idea onto OUR system (guestlang: schema-lang + codegen-core +
faults + dbsp + Machines + wasm-backend + substrait) and orders the build.

## The one-paragraph read

Flatland's endgame is a five-concept authoring core — **Schema / Query /
Update / Invariant / Tick** — where every concept is registry DATA
(elaborated through the four-addresses axis: data / type-level / Prop /
instance), every artifact (types, gates, wire, docs, tests) is GENERATED
from that data, correctness flows through instance search + bundled proofs
+ a computed enforcement ladder, and ONE oracle property ("the compiled
system's observable result = the authored semantics") covers the whole
stack. Our system already has the Schema leg, the emitters, the wire
round-trips, the machines, the delta theory, and the embryonic oracle.
We are missing: Update, Tick, the Invariant ladder, and the oracle's
teeth. Everything below is buildable with machinery we already ship.

## What we already have (mapped to the notes)

| Flatland idea | Where it lives | Notes |
|---|---|---|
| Schema as reified registry data (SPEC §1) | `@[schema]` + `schemaItemExt` + `Ty` | DONE — and now with elab-time derivation (`Meta.Derive`), reserved-word gate |
| Closed GADT + open registry (TOOLKIT 5.2) | `Substrait.Typed` (Rel/Expr/HasCol/Args) | exists; connected to schema via `Bridge.toSType?` |
| Emitters: AST→skeleton→tokens, byte-tie (D6/D7) | `CodegenCore.Emit` + `just gen-check` | DONE — now with DERIVED forge-jobs (`jobsCoverEmitters_true` is rfl) |
| Machines + guard-proof threading + conformance battery | `Machines` + `Pipeline` + `OrderMachine` | DONE; first DOMAIN machine emitted to Rust + host-replayed |
| Delta theory = the incrementalization LICENSE (SPEC §0 law 1) | `Dbsp` (fix_unique, incrementalize_ok, seminaive_equiv) | exists, unconnected to authoring |
| Errors enumerate the valid space (TOOLKIT 11.1) | `SchemaDiag` + did-you-mean | partially — not yet golden-tested with `#guard_msgs` |
| Wire round-trips proved once (GAPS A5) | `Codec` + NEW `CodecValue` (decode∘encode = id over the CodecClosed Value universe) + substrait expr decode | just landed |
| Oracle: model evals, engine replays (SPEC §11) | `Oracle.lean` + the wasm differential duel | embryonic — being randomized now |

## The gaps, in flatland's own order of attack

### 1. Invariant as a registry item with a COMPUTED tier (SPEC §5)

The item: `InvariantItem` = name + predicate + tier, where the tier is
COMPUTED from expressibility, not declared:
- **proved-erased**: the predicate is discharged as a THEOREM over the impl
  module (`getUser_spec : ... = ...`) — the axiom gate already enforces
  these are real; the content is the absence of defensive code downstream.
- **compile-time-type**: the VExpr/VCase families (we have these —
  instance-gated, elaboration-checked).
- **boundary-check**: EMITTED validators — the Rust `validate()` +
  fault codes from the SAME predicate item (this is the delegation in
  flight: field checks as schema data).
- **oracle-covered**: the predicate joins the differential manifest.

Today our VExpr layer is rung 3 only, hand-attached. The build: an
`@[invariant]` attribute registering the item, the tier computed by a
decidable fold over expressibility flags, emitters consuming it per tier.

### 2. Update + Tick (SPEC §3, §7) — the missing concepts

STATUS (2026-09-14): CORE LANDED — `SchemaLang/Update.lean`:
- `UpdateItem fs f` — the update demoted to v1: guard is part of the body
  (a `VExpr .bool`), the write is ONE column assignment whose value
  expression is a `VExpr` of the column's OWN type (the GADT index — a
  u64 expr cannot write a string column), and the write PATH rides as
  data (resolved by the registration command's HasCol search).
- **Reads derived, never declared**: `VExpr.reads` folds both
  expressions for their `.col` refs; `reads`/`writes`/`selfReading` are
  pure folds of the reified term. `selfReading` IS the derived
  linearity classification (the old-values capture policy's input —
  the flatland "linearity is COMPUTED" move).
- **Batch semantics** (SPEC law 1): `applyRow` reads the ORIGINAL row
  only (guard and value); `apply` = map — order-freedom is structural.
- **The two-channel duality pinned at row level**: `ColPath
  .set_commute_same` (later-wins — overwrite channels are not group
  elements) and `ColPath.set_commute_disjoint` (different names ⇒
  either order; kernel-checked by induction over the field list).
- **The tick machine**: settle → cascade → resolve → commit (+ reset),
  non-vacuous invariant (excluded `stale` state, OrderMachine's
  pattern), rank-acyclicity + committed-is-terminal theorems,
  `tickTableStep?_eq_step?` for emission through the generic fold.

IN FLIGHT: the `schema_update` command + emitter + tests (delegated).
The emitter consumes the SAME VExpr→Rust lowering as the invariants —
one expression language, two consumers (checks + updates), the canon's
row discipline.

An `@[update]` def: named, total, order-free `World → DeltaBundle`; reads/
writes DERIVED from the body (checked, not declared); guard = part of the
body (`fun w => if c then delta else ∅`); rate = reads `$tick`; no effects
(the `@[guest]` gate already bans IO/clock/thunks — our GuestGate IS
SPEC §3's "what an update may not do", already enforced).

The tick = `commit (resolve (cascade (settle ...)))` — and every phase has
a home in our tree: settle = `Dbsp.ChangeSpec` apply; cascade-to-fixpoint =
`Dbsp.Recursive`/`Staging` (fuel-bounded, decidable convergence — the
bridge theorem is GAPS A2's `fix_unique` play); resolve = the declared
deterministic function (monus-shaped); commit = two artifacts (causal
stream + state diff) from ONE triple stream — our event-sourcing rule
("deltas at the boundary, inversion in the log") is the same law.

The keystone license is ALREADY PROVED in our tree: `incrementalize_ok` +
`seminaive_equiv` — "the simple semantics and the fast execution are the
same function". Nothing new to prove for the claim; the work is the
authoring surface + the derived read/write graph (Dag — TOOLKIT 2.6,
`acyclic := by decide`) + the emitted Rust stage walker.

### 3. The oracle's teeth (SPEC §11, GAPS E-track)

- **Scenario/trace as a spec item**: `Scenario := {schema, init, seed,
  inputs}` with GENERATED both-direction codecs (our `CodecValue` +
  `PartialIso` shape — decode∘encode proved once, fuzzed in the engine).
- **Table equality** (sorted compare) as the conformance relation, not
  hash equality; the observable surface generous in test builds.
- **Every divergence → a minimized trace in the corpus** — the suite grows
  from bugs; bolero at ingress boundaries (we have the fuzz lane).
- **Versioning**: journal header carries the rule-set hash; deliberate
  changes go through the MIGRATION table — our `SchemaLang.Migration` +
  `just breaking` gate is EXACTLY this design, already landed. (The
  registered-migration + `remedied` verdict = flatland's "event-sourcing
  upcasting" distinguished from "engine bug".)
- Randomized oracle manifests (in flight in wasm-backend) are step one.

### 4. Proof-flow mechanisms we should adopt (TOOLKIT Part 4)

- **autoParam discharge ladder** (4 + Part 7): bundled obligations with
  `decide → omega → bv_decide → linarith → grind` defaults — e.g. a
  schema invariant's obligation discharges silently, failing ONLY with a
  domain-voiced error naming the flow and the law.
- **Deriving handlers emit artifact + proof** (4.3): our emitters already
  emit `#[cfg(test)]` tests; extend to emit property tests + negative
  controls from the same spec item (the delta emitter is the precedent).
- **`run_cmd` build-time assertions** (Part 7): registry consistency that
  fails the build from inside the file — our Derive module is this pattern;
  push more consistency checks into it (shift-left).
- **`bv_decide`** for overflow/alignment contracts on the emitted Rust
  (u64 wrapping semantics — our backend's binop lane is the consumer).
- **`@[implemented_by`]**: model stupid-clear, prove slow = fast, run fast —
  the oracle's eval can stay legible while the sweep goes native_decide.
- **Translated instance-failure layer** (4.1): "no `Linear` instance for
  `discountFlow`: its body calls `ifDistinct`, which is nonlinear" — when
  we get Determinism/Linearity classes over schema fns (FuncSem.determinism
  is ARMED but unfired — THIS is its firing site: a pure-context consumer
  that instance-searches update composition legality).

### 5. The canon discipline (TOOLKIT Part 3)

Every new subsystem names its row: our OrderMachine = the `machine!` preset
row (Rust typestate projection pending — the emitted enum+step IS the
typestate seed); CodecValue = the PartialIso row; the randomized oracle =
the E-track row; Migration = the versioning row. If something matches no
row, that is a finding — document, don't force.

## Build order (ours, not flatland's — we start further along)

| Phase | Items | Why |
|---|---|---|
| now | invariants-as-items (tier computed) + deterministic `Determinism` firing site | completes the Invariant concept with our existing VExpr as rung 3 |
| next | `@[update]` + derived read/write Dag + tick construction over the demo domain | the missing concept; dbsp license already proved; GuestGate already enforces the effect ban |
| then | scenario/trace spec item + table-equality conformance + corpus-from-divergences | the oracle goes from "smoke" to "teeth"; reuses Migration as the versioning story |
| then | Rust typestate emission from machines (machine! preset row) + session choreography on the wire | Machines becomes load-bearing for real services |
| continuous | autoParam defaults, deriving-with-proof, run_cmd shift-left, error goldens | the ambient-benefits requirement: benefits baked in, invisible, free |

## Explicit anti-goals (from the notes, restated)

No final-tagless in anything codegen touches; no proof terms in hot data;
no fourth GADT index (three is the ceiling — move it to a predicate); no
string-interpolation emitters (our Rust AST discipline); no runtime
machinery that isn't derived or generated; a proof obligation we can't
discharge is a FINDING, never a silently weakened statement.

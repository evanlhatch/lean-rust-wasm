# 03 — The Lean↔Rust discipline (bidirectional without dual authority)

Lean owns precise meaning and reusable laws; Rust owns implementation.
Changes originate on either side; neither side silently changes the
agreement.

## 1. One owner per fact

| Fact | Authority |
|---|---|
| domain identity, relationships, invariants, observable behavior | the model, checked by Lean |
| storage layout, algorithms, concurrency implementation | Rust |
| Rust public types, codecs, contract adapters | generated from the checked model |
| implementation satisfies model | explicit evidence connecting both (the levels, §3) |

Bidirectional editing ≠ dual authority. A Rust-side edit is a PROPOSED
model change: Lean validates compatibility + obligations → the accepted
revision regenerates the Rust interface. Generated Rust is never a
second specification.

Stable entity/field IDs are required infrastructure: renaming
`customer_id` must not read as delete+add. Names are presentation;
identities persist.

Never roundtrip arbitrary source. Rust admits layouts/lifetimes/traits/
macros/unsafe without schema meaning; Lean admits propositions Rust can't
express. Roundtrip the shared MEANING; preserve the language-specific
remainder.

## 2. The bidirectional transformation (the complement lens)

```
project : Model → Surface
update  : OldModel → EditedSurface → Either Conflict NewModel
```

The OldModel retains what the surface can't express — refinement
predicates, proofs, stable identities, migration history, semantic
units, hidden constraints. That retained information is the COMPLEMENT.

Laws (over the supported edit fragment):

- updating with the unchanged projection preserves the model;
- projecting an accepted update yields the normalized edited surface;
- unrelated model information survives the update.

**Unsupported edits produce a structured conflict, never silently
discard meaning.** Example: a Rust-side `Money<USD> → u64` edit
conflicts: removes the currency guarantee; the options are preserve the
semantic type / introduce an explicit representation adapter / weaken
the model and discharge the affected obligations.

Never lens handwritten implementation bodies — only generated interfaces.

## 3. Lean defines what Rust must demonstrate

The big risk is not stale types — it's a stale BEHAVIORAL abstraction
(Rust compiles against generated types while doing something the model
never intended). Every important operation has its relation:

```
Allowed(before, request, after, response, observableEffects)
```

The evidence levels — never masquerade one as another:

| Evidence | The actual guarantee |
|---|---|
| generated signature/type checks | the interface agrees |
| differential/property tests | tested executions agree |
| runtime checked transition | the accepted execution satisfies the checked relation |
| verified implementation/refinement | all executions covered by the theorem satisfy it |

**The practical default: Rust proposes, the checker validates, the
commit applies.** Rust computes `request + snapshot → proposed delta +
response (+ optional witness)`; the checker validates `snapshot +
request + proposal → accept/refuse`; the commit applies the accepted
delta against the SAME snapshot/version. Lean supplies the spec + the
checker's soundness theorem; Rust keeps algorithmic freedom. This is one
discipline with our artifact-time lane (the guestVerified witness
checker): candidate + independent validation, in both directions.

The honest limits: the compiled checker needs its own trust story (04);
the checker must see the relevant state+effects; the commit must prevent
snapshot races (transactional snapshot + commit validation / CAS /
recheck / PROVEN commutativity permitting intervening change — the
delta laws pay here); external effects never occur before authorization;
local transition checks establish no liveness.

## 4. Escape paths are explicit and expensive

A raw store handle in ordinary business code makes generated contracts
optional documentation. The shape:

```
handwritten Rust:   read snapshot; compute proposal
generated boundary: validate proposal; authorize commit; produce events
```

The generated API makes the correct route the EASIEST route (ownership,
module visibility, capability handles, transactional APIs). A legitimate
escape = an external primitive with a declared contract, declared
effects, an implementation identity, and its evidence/assumptions — an
explicit trust boundary, reviewed. Rust visibility is not a security
boundary against arbitrary unsafe code; process/component isolation
where appropriate.

## 5. Evidence binds to exact implementation dependencies

A theorem name or a previously-green test is not enough. Evidence
identifies: the model revision, the operation identity, the contract,
the representation/ABI, the relevant implementation dependencies, the
checker/toolchain assumptions, the verification method. A change to any
invalidates the appropriate evidence.

**Hashes establish identity, not correctness.** Correctness comes from
proof/checking; identity prevents old evidence applying to new
implementations. The "why may this operation commit?" command answers
with the evidence chain: the generated interface matches the model, the
proposal checker covers constraints A/B/C, the store adapter assumes
transactional commit, the differential tests cover the supported
representations, no universal proof of the handwritten algorithm is
claimed. Lean's role stays visible and honest.

## 6. Rust-first authoring, one checked model

Two authoring modes share the checked model: Lean authoring → the model;
Rust-facing authoring (attributes/macros over the supported fragment:
keys, references, semantic units, named operations, contract references,
views, migration intent) → a model PROPOSAL checked by Lean. Extracting
a description from Rust does not prove the description matches the
implementation — the connection is preserved through generated
interfaces, compile-time assertions where meaningful, boundary checks,
and stronger verification where available. Never two semantic
authorities; never full-Rust verification hidden behind a macro.

## 7. The change interface (the data plane's operational half)

The committed delta is the common change interface for tabular state:

```
Table = finite bag of typed rows
Delta = finite signed bag of typed rows     -- replacement = −old +new
```

One delta representation feeds: constraint maintenance, materialized
views, subscriptions, audit projections, cache/index maintenance,
synchronization, reconciliation, what-if execution. Mutations produce
deltas; consumers interpret the same deltas.

**The trichotomy that must not collapse:** a COMMAND is requested intent
(can fail, can no-op); a DELTA is an accepted state change (a NET
change — it erases intermediate history); an EVENT is a recorded
occurrence (with intent + causality). The journal stays causal; the
Z-set is a projection of it (net-zero ≠ nothing happened; signed
addition commutes but is not idempotent — replay/delivery needs event
identity or dedup).

**Validity belongs at the transaction boundary:** signed deltas may
temporarily represent negative counts or remove-referenced rows inside
a batch; check validity after the WHOLE atomic batch, unless a contract
explicitly requires intermediate validity.

## 8. Constraints as incrementally-maintained violation relations

The strongest single composition in this file. Define violation queries:

```
MissingReferences(db) · DuplicateKeys(db) · NegativeBalances(db) ·
InvalidLifecycleTransitions(history)
```

maintained INCREMENTALLY (the Ckt lane — the certified circuit emitter).
The state invariant: `Valid db ↔ Violations db = ∅`. A proposed delta
updates the violation relation; empty permits commit. The foundation
proves the incremental result equals full recomputation — ONCE, at the
circuit theory (`incrementalize_ok`).

Constraint specification, runtime enforcement, error explanation, and
incremental maintenance become one composition, with change-proportional
work. A constraint outside the efficient incremental fragment gets the
fallback checker or an explicit proof obligation — named, never silent.

## 9. The derivative discipline

For a pure query Q: `ΔQ = Q(B + ΔB) − Q(B)` — the derivative computes
the change without full recomputation, and "what changed" becomes
first-class (which customers became eligible, which constraints became
violated, which artifacts changed, which subscriptions need notifying).
Nonlinear operations stay explicit: the join's delta carries the cross
term (`Δ(A⋈B) = ΔA⋈B + A⋈ΔB + ΔA⋈ΔB`); distinct/thresholds/top-k/
aggregates carry their maintained state. Never infer linearity from
Z-set shapes.

## The first slice (the proof this doctrine works)

Keyed tables with a foreign key; a handwritten Rust command proposes a
delta; the incremental violation query checks the proposal; the
transactional adapter commits; the derived view updates; a view edit
maps backward through the checked lens. One slice demonstrates
bidirectionality, relational correctness, the delta machinery, and
Rust-first ergonomics — with zero duplicate implementations.

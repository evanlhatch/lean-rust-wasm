# Design — `guestVerified`: the fifth obligation tier (guest-checked witnesses)

Status: design contract. Canon rows named inline; the one NEW row this
doc proposes lands in `notes/canon.md` Part 4 with the W9 work (rule:
the canon grows deliberately, in that file). Executor's prerequisite
reading: this file + the primer in `notes/runbook-2026-09-15.md`
Part A. Every symbol cited below was grepped against the tree at the
paths given; a citation that no longer resolves is a finding, not a
license to improvise.

## 0. Context and the canon-row claim

Today's guests are Lean-derived wasm with NO verification capability:
the host's committed artifacts (byte-tied generated Rust/WIT, the
`invariants_generated.rs` check fns) are trusted because the host's
gates ran. The guest replays what it is handed. The fifth tier changes
WHO checks: the host ships a **witness** — a serialized, checkable
certificate — with the data, and the GUEST re-checks it in the sandbox
before acting. Trust moves from "the host's CI ran" to "this artifact
carries its own proof, verified at the point of use."

Kernel concepts touched: **Obligation** (the tier is a backend
assignment — this adds a backend), **Correspondence** (the checker is
a `CheckedProp`; the witness codec is a `PartialIso`), **Universe**
(the mini proof language is a closed code set with a total
denotation).

The proposed canon row (Part 4, lands with W9.1–W9.5):

| The mechanism | IS | Notes |
|---|---|---|
| a guest-checked fact | = | a witness (serialized certificate: claim + proof + fuel) + a fuel-bounded guest checker + the soundness bridge — proof-carrying data at the boundary | W9.1–W9.5; the checker is a `CheckedProp` with `complete? := .missing` (fuel) |

Existing rows inherited, not re-derived: the codec row (canon Part 4,
"a codec = a PartialIso"), the CheckedProp row ("a decidable check"),
the event-sourcing row (Part 1: migration = the delta transformer),
the Obligation row (doctrine 2026-09-15: "Every checkable fact is an
`Obligation` … the enforcement tier is a BACKEND ASSIGNMENT").

Substrate state (all verified in-tree):

- `CodegenCore/Kit.lean`: `Obligation.Tier` (4 ctors:
  `provedAtElab`/`decidableNow`/`generatedCheck`/`oracleSwept`),
  `Obligation.Evidence` (4 ctors), `Obligation.Evidence.tier`,
  `structure Obligation (α : Type)` (label/tier/payload/provenance),
  `CheckedProp` (P/check/sound + `Completeness.missing|.proved`),
  `PartialIso` (decode/encode/decode_encode), `Denotes`.
- `SchemaLang/Obligation.lean`: `SchemaObligation` (abbrev over
  `InvariantItem`), `Tier.toObligationTier`, `InvariantItem.obligation`,
  `SchemaObligation.discharge`, `discharge_isSome_of_computed`. The
  review-2026-09-16 verdict on this lane: tested-only; W9.3 is a
  paired consumer order, not new framework (the delete-or-graduate
  rule is honored by W9.5 being in this plan).
- `SchemaLang/Validate.lean`: `VExpr` (col/lit/gt/eq/and/strlen/not),
  `evalV` (boxed SPEC reading), `evalRaw`/`evalU`/`evalB`/`validates`
  (`@[guest_std]` — the COMPILED reading), `RowVals`, `ColPath.get`,
  `guardCastApply`.
- `SchemaLang/Wf.lean`: `WellFormed` (reasoning authority) +
  `universeCheck_sound`/`_complete` bridge, `CheckedUniverse` — the
  relation+checker+bridge template this design copies at the proof
  level.
- `SchemaLang/Codec.lean`: `encVarNat`, `encEnum`/`decEnum?`,
  `encBytes`/`decBytes?`, `encList`/`decList?`,
  `encEnvelope`/`decEnvelope?` (version + fingerprint + payload) with
  the append-form round-trip theorems.
- `CodegenCore/RoundTrip.lean`: `RoundTripSpec` (iso + sabotage +
  goldens + mandatory negative control), `runIO`.
- The guest boundary (`LintKit.GuestBan` + `CodegenCore.GuestGate`):
  `@[guest]` = fixed-width scalars only (no Nat/String/IO/Task/Thunk);
  `@[guest_std]` adds match-only Nat (zero/succ patterns — fuel
  decrement is legal) and String. The wasm backend compiles exactly
  the `guestMarkExt` registry's decls. The WIT marshaling rule (W6.2):
  ONLY scalars + byte arrays cross.
- lean4lean is NOT in the tree (no lakefile require, no justfile row;
  `/tmp/lean4lean` absent at design time). The adoption directive
  ("fully embrace it, speed is irrelevant") is the ordering authority;
  §5's gates-row claim is therefore a W9 order (W9.0), not an existing
  gate. Established facts used (per the project brief): pure Lean
  data structures, no IO/ST; truncated reduction (N-step cap =
  provable termination — the same discipline as our `Sem.exec` fuel);
  the VExpr/TrExpr metatheory with a `vexpr(…)` macro; NO reduceBool
  support; `Environment.addDecl'` as the drop-in checker entry.

---

## 1. The witness format — what crosses host→guest

**Boundary discipline (unchanged):** only scalars + byte arrays cross
(W6.2). A witness is therefore ONE byte array plus scalar metadata,
serialized host-side, decoded guest-side. No structure-field reads
off-Lean; no new marshaling.

**The witness as data** (new module `SchemaLang/Witness.lean`, W9.1):

```
structure Witness where
  label : String        -- the obligation's label (Obligation.label)
  claim : WProp         -- the claim, mini-language proposition (§2)
  proof : WProof        -- the proof term, mini-language (§2)
  fuel : Nat            -- the checker's step cap (semantics, §7.3)
```

`WProp`/`WProof` are ordinary closed inductives (core-compatible
data: Strings, UInt64s, lists, the VExpr fragments they embed). The
GADT discipline holds at the CLAIM level: `WProp` embeds VExpr-shaped
expressions as DATA (a first-order mirror — see §2.1), so a witness is
serializable; the indexed `VExpr` stays at authoring/semantics
(doctrine: GADTs at the authoring surface, plain IR + external WF
where a pipeline exists — the wire IS the pipeline edge).

**Byte-level encoding** (the codec row, instantiated — no new
machinery):

```
encWitness w =
  Codec.encEnvelope witnessVersion witnessFingerprint (
    Codec.encBytes w.label.toUTF8
    ++ encWProp w.claim
    ++ encWProof w.proof
    ++ Codec.encVarNat w.fuel)
```

- `witnessVersion`/`witnessFingerprint`: a `Nat` pair derived from the
  schema fingerprint pair of the record the claim ranges over (the
  Snapshot/enum-wire rule: reordering ctors of `WProp`/`WProof` is
  wire-breaking; `just breaking` is the gate).
- `encWProp`/`encWProof`: one tag byte per ctor in declaration order
  via `Codec.encEnum`/`Codec.decEnum?` (the EnumWire discipline),
  children via the append-form combinators. The round-trip laws are
  per-ctor `decEnum_encEnum_append` + `encList` composition, assembled
  ONCE as `decode_encode_append` over the mutual pair.
- The assembled codec is a `Kit.PartialIso (List UInt8) Witness`
  (W1.2's kit instance — this is also RoundTripSpec's first production
  consumer; the review's F3 graduate-not-delete verdict).
- The suite: `RoundTripSpec` with `goldenDir` set (golden byte-tie
  over fixed witness samples) + the default byte-sabotage control. A
  witness decoder that accepts corrupted bytes fails its own control.

**On the wire**: the witness rides the existing envelope slot as a
`bytes` field beside the payload it certifies (WIT: `bytes` is a
legal boundary type today). The guest receives `(payload-bytes,
witness-bytes)`; §4 gives the consumer flow.

---

## 2. The mini proof language + the guest checker

Design stance: we do NOT port lean4lean-whole into the guest. We build
OUR OWN kernel for OUR OWN mini language, following lean4lean's
architecture: pure data structures, truncated reduction (the step cap
IS provable termination), structural checking, no IO/ST. The calculus
covers what obligation payloads actually need: VExpr-level equations/
relations over guest values.

### 2.1 The claim language (`WProp`) — a first-order mirror of VExpr

The guest cannot consume the GADT (`VExpr s .bool` is indexed; the
wire carries bytes). The mirror is a plain inductive + a WF predicate
+ a denote, the doctrine's representation-routing row (executable fn +
CheckedProp for what must run; inductive Prop family for what proofs
invert):

```
inductive WU64 where           -- the .u64 fragment, as data
  | lit (v : UInt64)
  | col (name : String)        -- resolved against the record's fields at decode
  | strlenCol (name : String)  -- the only .string shape (VExpr's rule)

inductive WProp where
  | valid (e : WBoolExpr)                    -- validates e row = true
  | eqU (a b : WU64)                         -- raw u64 equality
  | chain (steps : List WStep) (inv : WBoolExpr)
      -- per-event invariant preservation over a log fold (§4)
```

(`WBoolExpr` mirrors VExpr's `.bool` ctors: col/gt/eq/and/not over
`WU64` — one-for-one with `VExpr` so the mirror's denote is
`evalV`/`validates` through the field resolution. Field resolution is
the existing machinery: decode builds the `ColPath` against the
record's `List Field` — a misspelled field in a witness is a DECODE
failure, `none`, loud.)

### 2.2 Judgment forms

One judgment: `checkWitness fuel claim proof = true`, with the proof
grammar matched to the claim grammar:

```
inductive WProof where
  | byEval (expected : UInt64)        -- eqU: both sides reduce to it
  | byValidEval                       -- valid: the fold evaluates to 1
  | steps (perStep : List WProof)     -- chain: one proof per log event
                                      -- (init holds; each step preserves)
```

Rules (structural, each one line of checker + one soundness lemma):

1. **evalEq**: `eqU a b` accepts `byEval v` when fuel-bounded raw
   evaluation of both sides yields `v`. Soundness: the raw evaluation
   is of TOTAL functions (`evalRaw` is total; fuel is instrumentation
   over a total semantics — lean4lean's truncated-reduction
   discipline), so "returns v within N steps" → "evaluates to v".
2. **evalValid**: `valid e` accepts `byValidEval` when the row supplied
   WITH the claim (the data being certified) makes the raw fold yield
   1 — i.e. `validates e row = true`, computed guest-side by the
   ALREADY-COMPILED `evalB`/`validates` lane (the witness checker
   reuses the guest-marked evaluator; it does not re-implement it).
3. **chain**: `chain steps inv` accepts `steps ps` when `ps.length =
   steps.length`, the invariant holds of the initial state, and each
   `ps[i]` certifies preservation across `steps[i]` — the fold
   induction, checked stepwise (the guest walks the log it already
   has; the witness carries no log copy, only per-step proofs —
   §7.2's size rule).

### 2.3 The checker as a guestlang function

```
@[guest_std]
def checkWitness : (fuel : Nat) → WProp → WProof → RowValsP → Bool
```

(`RowValsP` = the decoded row, an existential wrapper over
`RowVals fs` at the record's decoded field list — the
`InvariantItem.checkOn` existential pattern; decode builds it, the
`guardCastApply` kit casts it. Proposed here, defined in W9.1.)

- **Fuel-bounded, total by construction**: structural recursion on the
  proof term with a match-only-Nat fuel decrement (zero/succ patterns
  — legal at `.std`; Nat ARITHMETIC stays banned). `outOfFuel` is a
  verdict (`false`), never a trap — the `Sem.exec` precedent. The
  doctrine's fuel rule is satisfied: the cap IS the semantics (§7.3),
  not an unproved measure.
- **Guest-compilable**: the checker's closure must pass
  `@[guest_std]` (W9.6 proves it by compiling it — the manifest fold
  picks it up via the guest-mark registry, no hand-list). Data it
  touches: `WProp`/`WProof` (ctor dispatch), UInt64 ops, String
  comparisons at decode time only (std-legal), the compiled
  `validates`/`evalB`/`ColPath.get` lane (already `@[guest_std]`).

### 2.4 The soundness statement

The reasoning authority is an inductive Prop family (the Wf.lean
template):

```
inductive WHolds : WProp → RowValsP → Prop   -- the claim's meaning,
                                             -- stated against Denotes/evalV
```

and the bridge is a `CheckedProp` (the canon row — gaps LOUD):

```
def witnessChecked : CheckedProp (WProp × RowValsP) where
  P := fun (c, r) => WHolds c r
  check := fun (c, r) => ∃ fuel … -- checkWitness at the SHIPPED fuel
  sound := checkWitness_sound     -- checker accepts → the denotation holds
  complete? := .missing           -- LOUD: fuel exhaustion rejects true claims
```

`checkWitness_sound` per rule: evalEq/evalValid reduce to
`evalRawI_vexpr`-style reading ties (already proved:
`evalRawI_vexpr : evalRawI … = evalB`, `validatesI_vexpr`) plus the
fuel-sufficiency lemma (§7.4). The chain rule's soundness is induction
over the log fold — `replay_snoc`'s shape. Completeness is
DELIBERATELY `.missing` (a two-constructor `Completeness`, no default):
fuel can reject valid claims; that is the documented one-directional
gate, not a bug.

---

## 3. The tier wiring — exact deltas

**`CodegenCore/Kit.lean`** (core-only — no schema-shaped data crosses):

```
inductive Obligation.Tier where
  | provedAtElab | decidableNow | generatedCheck | oracleSwept
  | guestVerified                       -- NEW

Tier.render: | .guestVerified => "guest-verified"          -- NEW arm

inductive Obligation.Evidence where
  | citedProof (thm : Lean.Name)
  | decided (result : Bool)
  | generatedCheck (artifact fn : String)
  | oracleRow (ref : String)
  | guestWitness (artifact ref : String)  -- NEW: artifact = the byte-tied
                                          -- witness file; ref = the
                                          -- obligation label inside it

Evidence.tier: | .guestWitness _ _ => .guestVerified       -- NEW arm
```

The closed-enum discipline applies: adding the ctor breaks every
exhaustive match until handled — let the compiler drive.

**`SchemaLang`** (the invariant lane + the migration lane):

- `Invariant.Tier` gains `| guestVerified`;
  `Tier.toObligationTier .guestVerified := .guestVerified`;
  `Tier.render` gains its arm. `tierOf` is UNCHANGED — `guestVerified`
  is never computed from citation presence; it is assigned when
  registration carries a witness declaration (a computed assignment,
  from the row's own witness spec, same discipline as `tierOf`).
- `InvariantItem` gains `witnessRef : Option WitnessRef := none`
  (additive, defaulted — existing constructions and the byte-tie are
  untouched; the W7.1 additive-view discipline). `WitnessRef` =
  `(artifact : String) × (label : String)` — data only.
- `SchemaObligation.discharge` gains:

```
| .guestVerified =>
    o.payload.witnessRef.map fun wr => .guestWitness wr.artifact wr.label
```

  `none` stays the LOUD gap: a `guestVerified` tier with no registered
  witness is the armed-but-unfired pattern as data, exactly as
  `provedAtElab` without a citation is today.
- **`discharge_isSome_of_computed` gains a clause.** Current
  hypothesis: `o.tier = (tierOf o.payload.proofName).toObligationTier`.
  Since `tierOf` never yields `guestVerified`, today's theorem is
  unaffected by the new match arm — but the STATEMENT no longer
  covers all computed tiers. New statement:

```
theorem SchemaObligation.discharge_isSome_of_computed (o : SchemaObligation)
    (h : o.tier = (tierOf o.payload.proofName).toObligationTier
       ∨ (o.tier = .guestVerified ∧ o.payload.witnessRef.isSome = true)) :
    o.discharge.isSome = true
```

  (The disjunct's right side is the witness-backed computed tier; the
  proof's existing case split gains one arm, `Option.map` + the
  `isSome` hypothesis.)

**Host-side vs guest-side discharge** (the tier's two halves):

- Host (at emission, W9.4): the witness is GENERATED from the
  obligation payload AND SELF-CHECKED — the host runs the same
  `checkWitness` (interpreted, not compiled) on the artifact before
  writing it; a failed self-check fails the build. The emitted
  artifact enters the byte-tie manifest (one writer: the witness
  emitter).
- Guest (at consumption, W9.5/W9.6): re-checks via the COMPILED
  `checkWitness`. The two runs are the same Lean function through two
  backends; the oracle duel rows (guest verdict ≡ Lean verdict) pin
  agreement end-to-end (the existing differential discipline).

---

## 4. The first consumer — W5.1's migration path, end to end

Context: `@[event_sourced]` (W5.1, wave 16 in flight) derives per
record: the `Delta ρ κ` variant, the journal codec
(`encJournal`/`decJournal?` + `decJournal_encJournal_append`), the
replay fold (`replay`, `replay_snoc`), the RewindableMachine
(`esMachine`). `Migration.lean` carries the remedy half:
`FieldMigration` (typed total value map), `Migration.remedies`,
`verdictOf` (`remedied` → exit 2: apply the migration, re-baseline).
The named gap this tier closes (EventSourced.lean's deliberate
exclusion): "wire-level upcasting … the attribute ships the identity
upcaster hook."

**The obligation**: for record `R`, migration `m`, invariant `inv`:
*replaying the old log through `m` preserves `inv`.* Registered as an
`Obligation` with `tier := .guestVerified`, payload = the migration
row (a `MigrationItem`: the `Migration` + the invariant ref + the
record's field list), tier computed from the presence of the witness
spec at registration.

**End-to-end flow**:

1. **Host, at emission** (W9.4): the migration is applied to the
   committed log segment (the journal the artifact covers). Per event,
   the host computes the step certificate (old row satisfies `inv` →
   migrated row satisfies `inv` — an evalValid/checkable step over the
   closed fragment; a step outside the calculus → §7.1 refusal). The
   witness assembles: `claim := .chain steps invMirror`,
   `proof := .steps perStepProofs`, `fuel :=` consumed × headroom
   (§7.3). Host self-checks (`checkWitness` interpreted), then emits
   `witnesses/<record>-v<from>-v<to>.wtn` (bytes, byte-tied) + the
   envelope (version/fingerprint = the OLD and NEW schema
   fingerprints — `decEnvelope?` rejects a version mismatch guest-side
   before any checking).
2. **The wire**: the migrated journal segment + the witness travel as
   `(bytes, bytes)`.
3. **Guest, at consumption** (W9.5/W9.6): decode envelope (version
   check) → decode journal (`decJournal?`) → decode witness →
   `checkWitness fuel claim proof decodedState`. ALL of this is the
   compiled lane.
4. **On acceptance**: the guest applies the migrated events
   (`replay`), the invariant now guest-certified per step.
5. **On rejection** (bad bytes, wrong version, check failure, fuel
   exhaustion — ONE refusal path): the events are NOT applied; the
   guest returns a typed fault command (the W8.6 effect row: commands
   as data out) naming the refusal reason; the host quarantines the
   segment and the migration artifact is marked failed. Rejection is
   loud, total, and never downgraded (§7.1).

**Negative control (mandatory, the PropSpec discipline)**: a sabotaged
witness (corrupted step proof; wrong expected literal) MUST be
rejected by the compiled checker in the oracle duel; a suite whose
sabotage passes fails the gate. This is the tier's sabotage row, the
same shape as the wasm differential gate's flipped-instruction row.

---

## 5. What lean4lean contributes — host-side (the embrace, full list)

The owner directive: fully embrace lean4lean; speed is irrelevant.
What it buys, itemized:

| Contribution | What it is | Lands |
|---|---|---|
| **The independent olean sweep** | Re-check every declaration in the committed oleans with the lean4lean kernel (`Environment.addDecl'` drop-in): a SECOND, independent kernel's verdict on the build artifacts, replacing single-kernel trust. Ordered by the adoption directive; observed NOT yet in `just gates` (no lean4lean require in any lakefile) — W9.0 lands it as a gates row (`just gates` gains `lean4lean-sweep`) | W9.0 |
| **Cone-tracing for proof budgets** | The dependency cone of a cited theorem (the `checkCitation?`/`#check_cert` lane) computed over lean4lean's pure environment data — sizes what a citation pulls in, feeds witness fuel budgeting and the axiom audit's blast-radius reports | W9.0 follow-on |
| **The VExpr/TrExpr pattern as the semantic-preservation substrate** | lean4lean's metatheory pattern (a verified expression level + its translation, `vexpr(…)`-macro authoring) is the template for stating the wasm backend's translation correctness (emit preserves `Sem`) as a Lean-side theorem, itself checked by lean4lean — the oracle→theorem promotion. `Sem.lean`'s header already names the target ("the full correctness theorem … the NEXT Talos step"); W6.9's fuel-insensitive statements are the statement-shape precedent | W9.8 (research-grade, later — see §6.4) |
| **The honest limit: reduceBool exclusion** | lean4lean cannot re-check `native_decide` proofs (no reduceBool). Decls proved by `native_decide` keep the C++ compiler in their trust base forever. Hence §6.3's policy gate: the lean4lean-checked set must be `_native`-free | W9.7 |

**Divergence discipline** (the lean4lean `divergences.md` pattern,
adopted): if the lean4lean sweep and the C++ toolchain disagree on a
declaration, the DISAGREEMENT is the fact — never silently resolved.

- **Which wins**: for BUILDING, the C++ toolchain remains the
  authority (elaboration needs it — §6.1's hard floor). For GATES, a
  lean4lean rejection BLOCKS: `lean4lean-sweep` fails, the merge
  stops. Neither verdict is discarded.
- **How investigated**: minimize the rejected declaration to a
  committed repro; record it in `notes/divergences.md` (new ledger,
  created by W9.0's first run) with the verdict (our bug / lean4lean
  gap / toolchain behavior), following the doctrine's differential
  rule: "every historical divergence becomes a committed minimized
  case."
- The same discipline applies to the mini checker (§2): a host/guest
  verdict split on the same witness is a divergence — minimized,
  committed, ledgered; the guest verdict never silently overridden.

---

## 6. The C++-reduction map

Owner directive: reduce use of the C++ stuff as much as possible;
refactor around lean4lean where helpful.

### 6.1 The honest inventory

| C++ component | Role today | Status under the directive |
|---|---|---|
| **Kernel** | Checks every proof term at build — the sole correctness authority for proofs | **Absorbed as authority**: lean4lean re-checks the oleans independently (W9.0); for decls in the checked set, the lean4lean verdict becomes the cited authority. The C++ kernel still runs (it is inside the build) but is no longer trusted ALONE |
| **Elaborator / frontend** | Elaborates all spec modules; every attribute/macro (`@[schema]`, `machine!`, `declare_enum_wire`) runs it | **CANNOT be absorbed — the hard floor.** No Lean-written frontend exists; lean4lean is a kernel, not an elaborator. Stated plainly: elaboration is permanently C++-toolchain-hosted. The directive's floor |
| **Compiler + runtime (LCNF→C)** | Builds oleans, runs metaprograms, runs the test drivers | **Already bypassed for shipped artifacts**: guests are compiled by OUR wasm emitter (lean/wasm-backend), hosts are Rust (steel-host, guestlang-rt, forge). The C++ compiler's role is the DEV loop only — development-speed relevance, zero artifact relevance |
| **reduceBool (`native_decide` trust base)** | Compiles+runs proof-irrelevant evaluation inside proofs | **Cannot be absorbed** (lean4lean: no reduceBool). Quarantined by policy — §6.3 |

### 6.2 The target invariant (doctrine addition)

> **C++ is build-time scaffolding — never a correctness authority,
> never in a shipped artifact.**

Proposed as a `notes/lean-doctrine.md` row (gate level, enforced by
W9.0's sweep + W9.7's policy gate). Corollaries already true: no
shipped artifact contains C++-compiled code (guests: our WAT; hosts:
Rust); the olean sweep removes single-kernel trust; §6.3 removes
`_native` trust from the checked set.

### 6.3 The native_decide policy (new doctrine rule + gate design)

**Rule**: declarations in the lean4lean-checked set must not depend on
the `_native` trust base (`_native.native_decide.*`,
`_native.bv_decide.*` axiom families) — a decl lean4lean cannot
re-check cannot join the checked set.

**Gate design**: the axiom gate ALREADY computes per-declaration trust
bases — `just lean-axioms` delegates to the `guestlang-lint` exe's
`LintKit.AxiomAllowlist` env-linter (allowlist: propext,
Classical.choice, Quot.sound + the disclosed `_native.*` bases).
W9.7 adds a second mode to the same linter: a registered
checked-set (packages/roots opting into lean4lean sweeping) for which
ANY `_native.*` axiom is a finding. One linter, two allowlists; the
existing disable-flag machinery in the `lean-axioms` recipe is the
wiring pattern.

**Grandfathering** (the 3 disclosed existing uses, kept WITH their
disclosures):
- `lean/edgepython/EdgePython/Parity.lean` (the interpreter parity
  fixtures — disclosed in `edgepython/Tests/Axioms.lean`),
- `lean/schema-lang/SchemaLang/Emit/Circuit.lean` ×2 (allowlisted in
  the AxiomAllowlist).

These stay outside the checked set until re-proved; their disclosure
rows are the record. NEW uses require a disclosed justification at the
use site + a `Tests/Axioms.lean` row, and are categorically barred
from checked-set packages (the lint enforces).

### 6.4 The semantic-preservation work order (W9.8)

The item that makes the C++ toolchain's BEHAVIOR irrelevant to
artifact correctness: state the wasm backend's correctness against a
Lean-side semantics and check the proof with lean4lean. Concretely:
the `Sem.Instr` ↔ `Wat.Instr` translation + "emitted AST's exec ≡ the
LCNF source's semantics" (Sem.lean's named next step), developed in
the VExpr/TrExpr metatheory pattern (verified expression level +
translation, authored through a `vexpr(…)`-style macro), swept by
W9.0's gate. Once landed, artifact correctness rests on: our emitter
+ a proof + lean4lean — the C++ compiler only built the proof script's
oleans, and even that is double-checked. What remains C++: the
elaborator (§6.1, floor) and dev-loop speed. **Honest sizing**:
research-grade, LATER — the Talos lane's own ledger calls this the
hard open piece; W9.8 is scoped as a statement + substrate order, not
a theorem-delivery order, and its jj description carries the design
before merge (the `[senior]` protocol).

---

## 7. Risks — the honest ones

### 7.1 Expressiveness vs obligation needs
The calculus (§2) covers: u64 comparisons/strlen/boolean folds over a
record's fields (the whole registered-invariant fragment), raw-u64
equalities, per-event fold chains. A payload that outgrows it — the
VCase family, update payloads, table-level aggregations — gets NO
witness: registration fails at elaboration with a named error
enumerating the checkable shapes (the SchemaDiag discipline), and
`discharge` on a hand-set tier returns `none` (loud). **The tier
REFUSES; it never silently degrades** to `generatedCheck` or
`oracleSwept` — a downgrade is a new registration with a new tier, a
diff a reviewer sees.

### 7.2 Witness size on the wire
Chain witnesses grow linearly with the log segment: per-event proofs,
each a small constant (a tag + an expected literal). Rules keeping it
honest: claims reference events by journal OFFSET, never by copy (the
guest already holds the log); the envelope fingerprint pins the
segment; v1 ships per-SEGMENT witnesses (one claim per migration
batch), not per-event envelopes. If a segment's witness blows a
committed size budget, that's a design finding (split the segment),
not a retry.

### 7.3 Fuel-cap semantics on the guest
A timeout IS a rejection — an availability cost, never a soundness
cost. Policy: (a) fuel is part of the committed artifact — host sizes
it at emission as `consumed × 4` measured by the self-check run, so
host and guest agree BY CONSTRUCTION (no environment-dependent
budgets); (b) the guest never retries with more fuel — a legitimately
expensive witness is a claim-shape finding; (c) rejection surfaces as
the typed fault (§4 step 5) so availability impact is observable, not
silent. The availability/soundness asymmetry is deliberate: a refused
migration is recoverable operator work; an accepted bad migration is
corruption.

### 7.4 The soundness proof's real difficulty
Easy half: fuel-sufficiency for the TOTAL evaluators — `evalRaw` is
total, so "bounded run returns v" → "evaluates to v" is instrumentation
reasoning (the W6.9 mono/unique machinery is the in-tree precedent).
**The hardest lemma**: the chain rule's step composition — per-event
preservation must compose over the fold (a `replay_snoc`-shaped
induction) WHERE the rows are guest-decoded: the bridge must transport
`WHolds` across the codec — decode-then-denote equals denote-of-the-
host's-row (a `PartialIso`-law-through-`Denotes.abs` composition, the
kit's `ReprOp` square at the codec edge). Budget the proof there; if
it resists, the fallback is narrowing chain claims to records whose
row codec is byte-trivial (flat scalars — the `unbox*` fragment
EventSourced already isolates), stated as a calculus restriction, not
a hand-wave.

---

## 8. Work orders — W9.x (each self-contained; gates per order)

Dispatch protocol per `runbook-2026-09-15.md` Part B. Dependency
order: W9.0 ∥ (W9.1 → W9.2 → W9.3 → W9.4 → W9.5); W9.6 after W9.2,
feeds W9.5; W9.7 ∥; W9.8 last, gated on W9.0.

### W9.0 lean4lean vendored + the olean sweep `[std]`
Context: §5 row 1, §6.1. lean4lean is not yet a dependency (verified:
no lakefile require; the adoption directive orders this). Recipe:
`require` lean4lean at a rev matching the v4.33.0 olean format (VERIFY
the format match before depending — the cslib tag-check precedent);
a driver exe replays each package's environment and re-checks every
declaration via `Environment.addDecl'`; justfile gains
`lean4lean-sweep`; `gates` gains the row. Divergences: §5's ledger
discipline; create `notes/divergences.md` on first entry.
Verify: BUILD; `just gates` green incl. the new row.
Done-when: every package's oleans re-check; a planted bad olean fails
the sweep (negative control).

### W9.1 The witness data + codec `[std]`
Context: §1, §2.1. New module `lean/schema-lang/SchemaLang/Witness.lean`:
`WU64`/`WBoolExpr`/`WProp`/`WProof`/`Witness`, the append-form codec
(`encWitness`/`decWitness?`) over `SchemaLang.Codec` combinators, the
`Kit.PartialIso (List UInt8) Witness` instance, the `RoundTripSpec`
suite (goldens + default sabotage control), field-name resolution at
decode (misspelled field = `none`).
Verify: BUILD schema-lang; tests green incl. control; BYTE-TIE.
Done-when: decode∘encode law proved per ctor; a corrupted witness byte
is caught by the suite's control.

### W9.2 The mini checker + soundness `[senior]`
Context: §2.2–2.4, §7.4. `checkWitness` (fuel-bounded, match-only-Nat
decrement, structural on the proof), `WHolds` (the Prop family),
`checkWitness_sound`, the `CheckedProp` instance with
`complete? := .missing`. Per-rule soundness lemmas ride the existing
reading ties (`evalRawI_vexpr`, `validatesI_vexpr`). The chain lemma
(§7.4) is the budget; the flat-scalar restriction is the documented
fallback, stated in the module header if taken.
Verify: BUILD schema-lang; axiom gate (zero sorry; the theorem is the
deliverable — a missing chain lemma is REPORTED, never stubbed).
Done-when: `checkWitness_sound` lands (possibly with the documented
fragment restriction); the CheckedProp instance constructs.

### W9.3 The fifth tier `[std]`
Context: §3 (exact deltas specified there — this order is mechanical
against that section). Kit: the two ctors + render/tier arms.
Schema-lang: `Tier.guestVerified`, `toObligationTier` arm,
`InvariantItem.witnessRef` (defaulted), the `discharge` arm,
`discharge_isSome_of_computed` re-stated with the disjunct.
Verify: BUILD codegen-core + schema-lang; BYTE-TIE (no registered row
uses the tier yet → emitted bytes unchanged); axiom gate.
Done-when: exhaustive matches updated everywhere the compiler flags;
the extended theorem proves.

### W9.4 Host-side witness generation + self-check `[std]`
Context: §3 (host half), §4 step 1. The witness emitter: from a
`guestVerified` registration, generate the witness, self-check with
interpreted `checkWitness` (failure = build failure), emit the
byte-tied artifact (one writer, declared outputs, the emitter spine);
the obligation's `Evidence.guestWitness` names the artifact.
Verify: BUILD; `just gen-check` (the new artifact enters the byte-tie);
a doctored generator (skips the self-check) is caught by a test
(negative control).
Done-when: emission of a bad witness fails the build, not the guest.

### W9.5 Guest-side check + the W5.1 migration consumer `[senior]`
Context: §4 (the full flow — this order implements exactly it).
Depends: W9.4, W9.6, and W5.1 phases (wave 16, in flight — sequence
after). The apply-gate (`checkWitness` before `replay`), the refusal
fault variant, the ledger dogfood end-to-end, the oracle duel row with
the sabotaged-witness negative control.
Verify: GATES (full); the duel's sabotage row fails when it should.
Done-when: a migrated ledger segment replays in the guest ONLY with a
valid witness; a corrupted witness is refused with the typed fault.

### W9.6 The guest checker compiles `[std]`
Context: §2.3. `checkWitness` + `decWitness?` marked `@[guest_std]`,
compiled by the wasm backend (the guest-mark manifest fold picks them
up — no hand-list); oracle rows pin guest verdict ≡ Lean verdict.
Recipe note: if the checker's closure trips a backend `unsupported`
throw, that is a BACKEND finding (report; do not shrink the calculus
to fit the backend — fix the backend or restrict per §7.4, loudly).
Verify: BUILD wasm-backend; the duel rows green; GATES.
Done-when: the checker runs under wasmtime AND wasmi agreeing with the
interpreted run.

### W9.7 The native_decide policy gate `[flash]`
Context: §6.3. `LintKit.AxiomAllowlist` gains the checked-set mode
(second allowlist; `_native.*` = finding for registered roots); the
3 grandfathered uses recorded as outside-the-set; `just lean-axioms`
recipe unchanged (the linter table does the work).
Verify: `just gates`; a planted `native_decide` in a checked-set
package fails (negative control via the LintKit TestFixtures pattern).
Done-when: the grandfathered three are the only `_native` deps
tree-wide and the gate proves it.

### W9.8 Semantic preservation substrate `[senior]` — research-grade, LATER
Context: §6.4. The `Sem.Instr ↔ Wat.Instr` translation + the
correctness STATEMENT in the VExpr/TrExpr pattern, checked by W9.0's
sweep. Scoped as statement + substrate; theorem delivery is its own
later wave. Design in the jj description; review BEFORE merge.
Verify: BUILD wasm-backend; the sweep checks the new proofs.
Done-when: the statement is kernel-checked (by both kernels) and the
substrate modules carry the impossibility/preservation lemmas that
land; honest partiality recorded in `WasmBackend/Correct.lean`'s
ledger.

---

## 9. Decisions the owner must confirm

1. **Witness artifacts are regenerated + byte-tied, never
   hand-committed.** Recommendation: YES — one writer (the witness
   emitter), the byte-tie is the drift gate, same as all 13 existing
   artifacts. The alternative (committed blobs) creates a second-class
   artifact outside `gen-check`.
2. **Fuel exhaustion = refusal, no retry, no host fallback.**
   Recommendation: YES (§7.3) — soundness over availability; the
   emission-time `consumed × 4` sizing with the fuel pinned in the
   artifact makes exhaustion a design finding, not an operational
   event.
3. **Grandfather the 3 disclosed `native_decide` uses as permanent
   checked-set exiles.** Recommendation: YES (§6.3) — re-proving
   Parity's fixtures without `native_decide` is real work for zero
   artifact-correctness gain (edgepython emits no shipped artifact);
   the gate's job is preventing NEW uses.
4. **v1 calculus scope: VExpr `.bool` invariants + the migration chain
   rule ONLY.** Recommendation: YES — VCase/update-payload/table-level
   claims are new calculus RULES, each landing with its own soundness
   proof or not at all; a broader v1 buys witness-size risk (§7.2)
   against no waiting consumer.
5. **The divergence ledger (`notes/divergences.md`) is created at
   W9.0's first run, empty if no divergences.** Recommendation: YES —
   an empty ledger with the policy stated is the honest "we looked"
   record; lean4lean's own `divergences.md` is the format model.

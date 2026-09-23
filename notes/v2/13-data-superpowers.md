# 13 — The data superpowers: reversible, event-sourced, delta-algebraic management

The theory is PROVED: journal = D, state = I (`derivative_integral`), rewind =
subtraction (`ChangeInversion`), replay = addition (`Replicas.applyDeltas_sum`),
convergence = the group law, distinct/union/difference = Z-set ops. This doc
makes those PROVED laws the operating system of data management — migrations,
reconciliation, inspection, and portable verification — with concrete
capabilities an agent can build first-slice.

## 0. The data algebra, as the frame

```
state t   = I (journal) t            -- world = integral of its log
diff t1 t2 = state t1 - state t2     -- Z-set subtraction: WHAT changed
rewind K  = revert the last K deltas -- subtraction, again
apply Δ   = the group action         -- patch = +
migrate v1log = apply the upcaster per event, then replay
```

Every capability below is an INSTANCE of this algebra; the theorems already
landed (EventSourced, RewindableMachine, Replicas, DeltaSystem, Ckt) are
cited, never re-proved.

## 1. Migrations synthesized from the diff, proved by construction (the product core)

**Purpose.** The breaking gate computes the diff; derive the upcaster for the
common cases, and discharge the replay-preservation obligation (the W9.5
checkpoint shape) as a tier obligation. Hand-written upcasters become
generated + sound-by-construction.

```lean
-- the diff (exists: Diff/Migration) yields the remedy candidates:
inductive Change where
  | addField    (record : String) (field : Field) (default : Value def)
  | renameField (record : String) (from to : String)
  | widenField  (record : String) (field : String) (from to : Ty)  -- u32→u64 etc.
  | typeShape   (record : String) (field : String) (from to : Ty)  -- list-len etc.

def remedyOf  (c : Change) : Migration        -- the candidate remedy row
def upcastOf  (c : Change) : Event → Event    -- the generated per-event function
  -- addField   : insert/update payloads gain the default (boxed at the wire type)
  -- renameField: payload field read/written under the new name
  -- widenField : payload field value widened (the u64/… wrappers, NOT raw casts)

-- the preservation obligation (W9.5 shape, PER migration):
structure MigrationProof (m : Migration) where
  -- replaying the MIGRATED log preserves the claim, over the derived ctx
  replay_preserves : ∀ log init W (wf : well-formed witness for W),
    WHolds W.claim <migrated-base> <migrated-segment>   -- cited, decide-backed
```

Rules:

- Every remedy row is a `Change` row; the upcaster is a GENERATED fold of the
  change (no hand mirrors). A change without a `remedyOf`/`upcastOf` is a
  breaking-gate finding.
- The preservation obligation is a TIER row (proved-at-elab where decideable,
  else generated-witness, else guestVerified — 12 §3/§1). It is discharged at
  the registration, not after.
- What-if (below) is the dry-run: `replayMigrated?` over the REAL journal,
  refused loudly on a failing witness (EventSourced — existing).

**Kit home:** schema-core (Change/remedyOf/upcastOf) + the witness lane
(obligations) + the breaking gate (the diff's consumer).

**Acceptance:** rename a field in the demo → the upcaster exists, the
preservation obligation discharges, the migration replays the committed v1
segment byte-stable; a migration that would fail preservation is refused by
`replayMigrated?` before the gate is green.

**Guard:** remedy derivation is CLOSED per change kind (the enum above is
closed); exotic changes (type-shape surgery) are hand remedies WITH the same
obligation — generated-by-default, hand-with-proof when closed cases don't fit.

## 2. The what-if inspector (the data tool)

**Purpose.** Every state is reconstructable; the machine (RewindableMachine,
wasm-delta's log, the oracle's replay) landed. The tool: `rewind <journal>
<point>` + `replay-forward-with-a-modified-event` — what-if over REAL journals.
And the diff readout is algebraic: `state t1 - state t2` as a Z-set difference,
presented as data ("these rows appeared / disappeared / changed"), not a string
diff.

```lean
structure Inspector where
  log    : List Δ
  base   : State

def rewindTo (h : Inspector) (point : Nat) : State          -- drops point.. replay base+prefix
def whatIf (h : Inspector) (point : Nat) (ev : Δ) : State   -- replay to point, apply ev, continue
def diffBetween (h : Inspector) (t1 t2 : Nat) : ZSet Δ-ish  -- state t1 - state t2 (algebraic)

-- the readout rules:
--   appeared  = (diff).support where multiplicity > 0
--   vanished  = (diff).support where multiplicity < 0
--   changed   = the rows whose multiplicity/values moved
```

**Kit home:** a `Data` tool module in schema-core or the app package (assembly
over EventSourced/RewindableMachine/Replicas — cites their theorems).

**Acceptance:** a committed journal replays/rewinds/forks deterministically;
`diffBetween` on a known mutation reports exactly the touched rows; what-if
over a tampered event is REFUSED by the rewind/replay obligations or shows the
tamper as the (algebraic) delta.

**Guard:** what-if is data-plane only (no writes); safety = the existing
inversion laws (cited).

## 3. Portable proof-carrying artifacts (the product capstone, the "don't trust me" pack)

**Purpose.** Package data + certificate + a small wasm verifier module that
ANY consumer can embed and run: "here's the migration, here's the proof, here's
the verifier — don't trust me." The pieces exist (witness format, the mini
W9.x checker, the wasm compilation). The work: packaging + a SECOND consumer
proving portability.

```lean
structure ProofCarryingArtifact where
  payload   : ByteArray            -- the data (e.g. the migrated segment)
  witness   : Witness              -- label + claim + proof + fuel (existing codec)
  verifier  : wasmModule           -- the compiled checker (guest-checked)
  declared_hash : UInt64           -- payload hash the witness certifies
-- consumption contract:
--   verifier(payload, witness) → accept | refuse{code}
--   (code = the E-code; refusal is loud, never silent)
```

Rules:

- The verifier is the SAME guest-compiled checker (the witness lane) — one
  semantics, N embeds.
- Portability proof: a SECOND consumer embeds it (a Rust host via wasmtime AND
  the in-product guest path) and both accept/refuse identically (the
  conformance engine, 08 §4, is the check).
- The artifact's byte-tie is a golden; the payload hash is in the witness.

**Kit home:** the witness lane (packaging + the second consumer); wasm-core
(the verifier module); TestKit (the conformance rows).

**Acceptance:** two independent embedders (the product guest + a standalone
Rust host) verify one artifact identically; a tampered payload/claim/proof
refuses with the same E-code in both.

**Guard:** the verifier's own effect row (12 §1) is `[read witness-bytes]` only
— the verifier touches nothing else; that is part of the artifact's contract.

## 4. CEGAR-flavored gate failures (minimal failing sub-universe)

**Purpose.** A QC affirming gate currently says "drift." Upgrade: every
WF/obligation failure returns the MINIMAL failing witness — the smallest
sub-universe that still fails ("this record's third field collides") — by
delta-debugging the failing spec (shrink until pass, report the boundary).

```lean
def minimalFailing (check : Universe → Bool) (bad : Universe) : Universe
  -- shrink-search over the sub-universe lattice (+ the Shrink strategy, 12 §4)
  -- returns the minimal bad input; the diff (badMinusMinimal) names the culprit
structure GateFinding where
  code     : String        -- the E-code
  message  : String        -- the curated render
  minimal  : Universe      -- the smallest failing witness
  culprit  : List (Lane × Row)   -- derived from (bad - minimal)
```

Rules:

- Applies to every decideable gate over a spec (universe WF, keys legality,
  range checks, obligation discharge). Bound by the budget (never a full
  exponential sweep); on budget cutoff: report the best-found + the bound.
- The culprit render satisfies 04 §2 (valid space + did-you-mean where closed).
- Composses with the model-checking counterexample traces (12 §3): a minimal
  failing universe for gates, a minimal failing TRACE for machines/grammars.

**Kit home:** `CodegenCore.Errors` (GateFinding in the Diag envelope) + the
shrinking strategy (TestKit).

**Acceptance:** a universe with a colliding third field reports exactly that
("record `X`, field `c` collides with field `a`") and the minimal failing
sub-universe reproduces the failure alone.

## 5. Reconciliation and audit as deltas (z. the group law repays)

**Purpose.** Two replicas/states reconcile by subtraction and the audit trail
IS the journal. The machinery exists (Replicas, RewindableMachine, the
differential duels); the superpower is the UX layer:

- `reconcile (local known) (remote journal)` → convergence certificate +
  the diff (which events were missing) — `batch_order_irrelevant` cited.
- Audit = any point's state + the journal prefix, provably reconstructable
  (journal_complete cited) — the "what was the table at t?" query is an
  integral read, not a store.

**Kit home:** the Data tool module (§2) + the conformance engine.

**Acceptance:** a divergent replica detects exactly the missing deltas and
converges by application (the certificate cites the group law); an audit query
reconstructs a past state byte-stable.

## 6. Incremental derived views (the Ckt edge, made data-plane)

**Purpose.** Migrated/aggregated views stay incrementally consistent: changes
flow as deltas, `incrementalize_ok` cited in the emitted layer (the Rel→Ckt
lowering + Rust emission, 08/11 Phase 7). The data plane's read model is
maintained, not recomputed.

**Kit home:** dbsp (Ckt) + schema-lang Emit; the consumption is the app
layer's.

**Guard:** incrementalize certifications are cited per emitted view; a view
without its citation is a review finding.

## Priority

Per the product direction: **(1) migrations synthesized + proved** is the
"crush it" core (composes Diff/Migration/Witness — the direct product value);
**(3) portable proof-carrying artifacts** is the capstone (and the closest to a
genuinely novel capability — package it second); **(2) what-if** and **(4)
CEGAR failures** are the highlight+DX layer (assembly + polish, land with the
observability phase); **(5)/(6)** ride existing proofs (UX + emission edges).

Additions to 11-sequencing:

- **Phase 9 — The data plane**: migrations synthesized from diff + per-migration preservation obligations (13 §1), the what-if inspector (13 §2), reconciliation + audit-as-integral (13 §5), incremental views (13 §6). Acceptance: rename/widen on the demo yields a generated upcaster + a discharged obligation + a what-if dry-run; CEGAR gate failures land earlier with the diagnostics phase (04/10), fold `minimalFailing` into Phase 2's diagnostics work.
- **Phase 10 — The portable verifier**: packaging (13 §3) + a second consumer + conformance rows. Acceptance: two independent embedders verify identically; tamper → same E-code, both sides.

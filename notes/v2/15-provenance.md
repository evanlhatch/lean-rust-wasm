# 15 — Provenance for generated things (the generation ergonomics layer)

This toolkit WILL generate a lot of artifact: every spec row feeds emitters,
fixtures, witnesses, duels, docs, dtypes. Provenance is BUILT IN so the
artifact map is a first-class, queryable, ergonomic surface — "what made
this?", "what would change this?", "regenerate just this".

## 1. The artifact ledger (the one registry of generated things)

```lean
structure ArtifactTrait where
  path        : String                -- repo-root-relative (declared output)
  emitter     : String                -- the emitter plugin name
  specSource  : String                -- the spec module (header today)
  specRows    : List (Lane × String)  -- the EXACT spec rows it folds (the demand set!)
  hash        : UInt64                -- content hash (already in the header)
  obligations : List ObligationRef    -- the obligations it attests (tier + evidence)
  golden      : Option String         -- the golden baseline path (if byte-tied)
  coveredBy   : List (String × String) -- duel rows that exercised it (fn × row id)
  generatedAt : String                -- the GenMeta time (cosmetic, header only)

structure ArtifactLedger where
  artifacts : List ArtifactTrait
  nodup     : artifacts.map path .Nodup := by decide    -- one-writer IN THE TYPE
```

- The ledger is a DATA file the driver writes (one writer: the emitter
  spine's write path append the row); the gates, the inspector, forge, and the
  causal trail (12 §6) READ it — never resent it.
- `specRows` is computed by the emitter fold itself (which registry items each
  artifact's `run` consulted — the demand set), so it cannot drift from what
  the fold actually read.

## 2. The two query directions (the ergonomics payoff)

- **backward: artifact → spec rows** — "which registry rows made `User.lean`-ish
  artifact X?" → the inspector/causal trail starts from the ledger entry.
- **forward: spec row → artifacts** — "change `User`; what artifacts will move?"
  → the provenance-fed impact set (12 §5 + 14 §1): the `--affected` filter is
  a ledger query, not a heuristic.

Both are folds over the ledger — total, deterministic, and the SAME table the
byte-tie and self-audit consume.

## 3. Header ↔ ledger agreement

The 2-line GENERATED header already carries tool/source/hash. The ledger row
must agree with the header (hash, specSource, path); a disagreement is a
self-audit finding (07 §6). The header is cosmetic; the ledger is the truth.

## 4. Regeneration ergonomics

- `just gen <artifact-pattern>` regenerates exactly the matching emitters; the
  pattern matches the ledger (paths, emitters, spec rows), never bespoke flags.
- Regen obeys the one-writer audit: an artifact whose declared owner conflicts
  is unconstructible (outputs nodup in the type, 05 §4).
- After regen, the byte-tie (07 §2) is trivially green for untouched artifacts
  and REQUIRED for touched ones — the ledger is the change set.

## 5. The "organized, usable, productive" layout rules

1. Declared outputs only: every generated path is an `Emitter.outputs` row; no
   path magic outside the emitters.
2. One directory per package's artifacts (already the `src/generated.rs`,
   `wit/…` convention) — keep it; the ledger documents it, never the prose.
3. File naming derives from registry names through the ONE mangler
   (kebab/pascal/snake) — no hand spellings.
4. Regeneration is idempotent and deterministic — same ledger, same bytes.
5. A generated file WITHOUT a ledger row is a review failure (Phase 11 rule).

## 6. Provenance for the whole chain (the causal trail's spine)

Ledger rows + obligation evidence + duel coverage + gate verdicts form the
full chain: spec row → emitter fold → ledger row → byte-tie → obligations →
duel coverage. The causal trail (12 §6) is this chain read backward; the
inspector (13 §2) runs on it; the E-code registry (04 §4) keys it. Provenance
is not a sidebar — it is the answer to "why does this artifact exist and what
attested it."

## 7. Acceptance

- Every artifact in the tree has a ledger row whose `specRows` equals the
  rows its emitter actually read (drift test: rename a field → the affected
  artifact rows change, others don't).
- `--affected` after a one-line spec change returns exactly the ledgel-defined
  set; `just gen <pattern>` regenerates precisely that; the self-audit
  verifies header↔ledger agreement including the one-writer property.
- The inspector's "what changed between two specs" is an algebraic diff and
  the artifact map updates accordingly (14 §2 × 13 §2).

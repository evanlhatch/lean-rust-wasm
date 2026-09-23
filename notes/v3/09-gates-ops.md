# 09 — Gates, byte-tie, provenance, the dev loop

## 1. Totality of the emission layer

Every emitter/generator/printer is total (structural recursion or an
explicit size measure). Totality makes the golden equality a theorem and
`parse∘emit` provable. The only permitted `partial`: genuine semantic
recursion the totality engine can't see, each with a written reason,
ratcheting down only.

## 2. The byte-tie

The committed generated artifacts are the spec of record. The tie binds
CONTENT (the header's timestamp/sha are exempt metadata; the embedded
content hash + body bytes are the tie). The stripped compare runs
in-process in the gates exe; hand-edits are detected; drift fails CI;
regen is a deliberate commit-visible act.

With total emitters the committed golden is a REPRESENTATION of a
theorem (`emitter … = committed-bytes` is provable); the gate upgrades
from regen-and-diff toward "the equality holds."

## 3. The gates as one machine

The pipeline is a machine: states = the checks; transitions = the gate
runs; the invariant = emissions green. One driver over the gate registry
(the report-gate combinator); the obligations are the gate's data — a
registered obligation with no discharge, or evidence resolving to
nothing, fails the gate. The current composition: lean-build, gen-check
(the stripped byte-tie + hand-edit detection), artifact-headers,
wit-check, lean-axioms (sharded, baselined report), native-policy,
kernel-check (the lean4lean sweep), manifest-check, coverage, docs-check,
check-schema, breaking, wasm-diff-check, budget-check, splice-smoke,
rt-conformance, lean-lint — each a row, each with teeth.

## 4. Provenance (the artifact ledger)

Every generated thing has a ledger row: path, emitter, the EXACT spec
rows it folds (the demand set — computed by the emitter fold itself, so
it cannot drift from what the fold read), the content hash, the
obligations it attests, the golden baseline, the duel rows that
exercised it. The two query directions: artifact → its spec rows
(backward: "what made this?"), spec row → its artifacts (forward: "what
moves if I change this?" — the impact filter).

**The demand-set correction (a review catch — do not regress):**
recording previously-read rows is INSUFFICIENT for exact incremental
rebuilds — a query also depends on absence, enumeration, the emitter's
own code, imports, configuration; adding a new row can move an artifact
whose old demand set never named it. The tracked query interface records
negative/collection dependencies; conservative invalidation is PROVEN
(the affected set never under-reports); exactness is promised only where
established.

The ledger is one data file with one writer (the emit spine's write
path); gates/inspector/forge read it, never re-derive it. Header ↔
ledger disagreement is a self-audit finding. A generated file without a
ledger row is a review failure.

## 5. The artifact self-audit

Every emitted artifact scans against the AuditRule list (no TODO/FIXME/
unwrap/dbg!/unsafe in generated output; the observability-inheritance
row: generated host code without span coverage fails). Runs over every
emitter, every package, the forge manifests.

## 6. Impact-aware gating

The full run is the release gate. The dev loop runs the affected set:
the change set (the VCS diff) → affected modules (the import-closure
walk) → affected artifacts (the ledger's forward query) → only their
gates. The affected-set correctness is the invariant: conservative, never
under-reports. The pipeline-as-circuit reading (14's incrementalize
discipline) is the theory.

## 7. Elaboration-time regression watch

Type-driven gating shifts work into elaboration; the gates exe logs
per-module elaboration time and flags DELTAS against the committed
baseline (absolute budgets are noise; regressions are signal). Every
deriving handler terminates in linear work over the record's fields; a
handler needing a fixpoint or search is a review failure. The
degradation rule (01's ladder): a gate that blows the budget drops a
rung with a note in the module header.

## 8. The CI answer

A gate's answer is a VERDICT (categories are ctors, never strings) + a
machine exit code. No prose-only gates. The semantic-diff discipline
(08 §27): where a verdict is "behavior changed", it carries the
distinguishing witness or the equivalence proof.

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
nothing, fails the gate. The current composition — `Gates.gateNames`
(in `gates/Gates.lean`) is the single source; the names below are its
rows in run order, each a CHILD `lake exe gates <name>` process,
run at bounded parallelism (GATES_ALL_JOBS, default 3) with ALL
verdicts collected — the parallel-collection discipline (the
sequential first-failure-stop was the OOM era's shape; the gates are
independent read-only checks, every `--write` is a manual mode), the
report ordered by the registry: packages-check (the gated table ×
lakefile agreement, lib- AND root-level), lint (the enforcement wave:
the lintkit exe's OWN shard fold per gated package — the env/text
linters' CI teeth; the row fails when any package has findings, the
sabotage teeth live in GatesTests.Main), axioms (the sharded,
baselined report), docs-check, gen-check (the stripped byte-tie +
hand-edit detection), code-registry-check, snapshot-check, audit,
artifact-headers, native-policy, coverage, kernel-check (the lean4lean sweep: one
invocation per module — the batch mode's ~300 concurrent replays was
the recorded hang — the leaves pooled at GATES_KERNEL_JOBS, the inner
nodes exclusive, a per-module wall budget at GATES_KERNEL_BUDGET_SECS
whose expiry is an UNKNOWN with a named report, never a hang),
ownership, breaking, decide-first-census + zero-citation-census (the
§8 promotion: the proof-hygiene censuses as BASELINED report-gates —
the findings are data, drift flagged — landed at the first adjudicated
nonempty run) + evidence-redundancy-census (B6; D37's teeth — the
entourage's first question at the hand-written face, the same census
discipline; the first fold's buildable-tree result: the carried-law
fields' own sites, refined away; the baseline lands at the green
re-baseline), nolint-census (the `@[nolint]` opt-out rows'
per-(linter, file) counts, baselined; a new silenced site is a
deliberate re-baseline diff) — each a row, each with teeth.

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

**The census promotions (the enforcement wave's landing — the trigger
executed):** the proof-hygiene censuses stay default-OFF (the census
grade), but their first ADJUDICATED nonempty fold ran and the outcomes
are on record as BASELINED REPORT-GATES (the axiom-report discipline:
output committed, drift flagged, findings are DATA never failures):

- `decide-first` — 65 findings, ALL in the heuristic's own
  false-positive classes (rfl-proved theorems whose elaborated terms
  route through non-computational casts; quantified-hypothesis
  statements the synthesizable-Decidable statement filter lets
  through — not actually closed spaces). Promoted as
  `gates decide-first-census` (notes/decide-first-census.md): a new
  hand script over a closed space is exactly the signal the census
  exists for, and it now surfaces as a review-queue drift line.
- `zero-citation` — 1455 findings, the LAW-LIBRARY class: the theorem
  layer ships as API and mechanically it is indistinguishable from
  dead code (the ~130 reasoned `@[nolint]` rows cover only the sites
  the earlier adjudication touched). Promoted as
  `gates zero-citation-census` (notes/zero-citation-census.md), still
  census-grade: every NEW uncited theorem surfaces as a deliberate
  re-baseline diff naming it (fixed, consumed, or the reasoned
  opt-out).
- `evidence-redundancy` (B6; D37's teeth) — the entourage's first
  question ("does the type already carry it?") as an env linter over
  the HAND-written face: carried-law re-proofs (the
  Codec.decode_encode / Iso.to_inv / Iso.inv_to statement shapes,
  same instance both sides, proof not citing the field) +
  weaker-than-kernel obligation rows (a closed Decidable claim with a
  literal `oracleSwept`/`generatedCheck`/`guestVerified` tier). The
  first fold over the BUILDABLE packages (the tree was red in
  WasmCore.Decode — another lane's in-flight work — during the
  landing): exactly 3 findings, ALL one false-positive class — the
  carried-law fields' own declaration sites (the field decl IS the
  construction; refined away by the name exemption). Class B's fold
  was empty — the honest zero (the generator-level waste the audit
  named is prevented by the entourage's own computation; the fixture
  teeth prove both classes fire). Promoted as `gates
  evidence-redundancy-census` (notes/evidence-redundancy-census.md);
  the baseline's first write lands at the green re-baseline — the
  load-failed packages' sections (the WasmCore-dependent lanes) are
  the blocked first run's named remainder.

(The close-out audit's "measured ZERO census findings" claim did NOT
survive the fresh fold — the earlier `--enable` runs died mid-fold;
the gate rows above carry the honest numbers. The GENERATED-`<m>Keys`
reminder stands: macro-generated declarations remain the census's real
false-positive surface, invisible to source grep.)

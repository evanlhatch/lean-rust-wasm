# 07 — Tooling: gates, byte-tie, CI-as-machine

The correctness story ends in the pipeline: gates that run, artifacts that bind,
and an explanation (CI as a machine) for what the pipeline IS.

## 1. Totality of the emission layer — the prerequisite for everything

- Every emitter, generator, and printer is TOTAL: structural recursion or
  `termination_by` with an explicit size measure. No `partial` in the emission
  layer. (The proof: `Audit.go`'s `termination_by sizeL` is the model.)
- Totality makes the golden equality a THEOREM (see 07 §2) and makes
  `parse∘emit` provable (03).
- The only permitted `partial` anywhere: genuine semantic recursion the
  totality engine cannot see (the LCNF `Code` spine) — each with a written
  reason in the declaration and the allowance ratcheting DOWN, never up.

## 2. Goldens and byte-tie

- The byte-tie binds the CONTENT (stripped of the header: the header's
  timestamp/sha/hash are metadata). The drift check strips the 2-line header and
  compares body bytes + the embedded content hash.
- With total emitters the committed golden is a REPRESENTATION of a theorem:
  `emitter … = committed-bytes` is provable. The gate's job upgrades from
  regen-and-diff to "the equality holds".
- Goldens are data folds of the One Universe value (02 §5): a lane change shows
  as ONE diff surface.
- Rule: never hand-edit a generated file; the one-writer audit (outputs in the
  type, 05 §4) is unconstructible to violate.

## 3. The gates as one machine

- The build/test/verify pipeline IS a machine (the canon row): states =
  check/coverage/axioms/byte-tie/native-policy/kernel-check; transitions = the
  gates; the invariant = emissions are green.
- Run the machine: one driver over the gate registry; each gate is a
  (config, analyse, render, write-or-diff, exit-code) row — the report-gate
  combinator is the executor. No per-gate driver loops.
- The OBLIGATIONS are the gate's data: which lanes, which tiers, which backends
  — armed-and-fired is data, and the CI is a fold over the obligation registry
  (a registered obligation with no discharge, or a claimed evidence that
  resolves to nothing, fails the gate).

## 4. Elaboration-time regression watch

- Type-driven gating (01) shifts work into elaboration; the discipline is to
  keep it SHALLOW (small class graphs, reducible wrappers, head/tail over short
  lists) and to WATCH the cost: the gates exe logs per-module elaboration time
  and flags DELTAS against the committed baseline (the byte-tie philosophy
  applied to time). Absolute budgets are noise; regressions are signal.
- Every `deriving`-staged handler must terminate in linear work over the
  record's fields; a handler that needs a fixpoint or search is a review
  failure.
- The fallback: a type-gate whose elaboration cost breaches the regression
  watch's delta DROPS a ladder rung with a note in the module header (which
  rung it was, the measured cost) — never a silent `maxHeartbeats` bump (09 §1's
  smell).

## 5. The kernel/axiom gates

- Zero `sorry`/`axiom`: a missing theorem is information, a stub is a lie.
- The allowlist: core triple (propext, Classical.choice, Quot.sound) + disclosed
  `_native.native_decide.`/`_native.bv_decide.` trust bases. Disclosure rows are
  part of the gate; a new trust-base use is additive-only with a written
  justification in the same commit.
- The lean4lean replay covers everything not on a disclosed trust base; the
  reduceBool gap list is additive-only and mirrors the native-decide registry.

## 6. The artifact self-audit

Every emitted artifact is scanned against the AuditRule list (no TODO/FIXME/
unwrap/dbg!/unsafe — generated output stays in the safe, finished subset).
The sweep runs over EVERY emitter (schema-lang today; the audit is generic and
extends to all packages and the forge manifests).

## 7. Field notes (operating rules)

- Recipes run from the justfile; watchers wrap the SAME commands (never
  redefine the build).
- The committing rule: byte-tie, one-writer, drift = reviewable diff, not a
  silent regen.
- The CI answer word is a VERDICT (categories are ctors, never strings) and a
  machine exit code; no prose-only gates.

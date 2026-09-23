# 08 — Verification: the proof ladder, tests-as-artifacts, the oracle

## 1. The proof ladder (what each layer of correctness gets)

1. **Types** — the bulk (01 §1 rungs 1–2): unrepresentable states, instance
   gates, defaulted proof fields.
2. **Decide / generated proofs** — `by decide`, `by po_ladder`, family!-emitted
   theorem batteries.
3. **Disclosed native_decide** — heavy decidable judgments, disclosed as data.
4. **Hand theorems** — only relational content (fixpoints, perturbations,
   incremental equivalence), written ONCE at the structure and cited by every
   consumer (`#check_cert`-style resolution keeps citations honest).

The doctrine: a hand-written theorem below rung 4 without a written reason is a
violation; an invariant checked only by a test is a violation. Tests validate
the ladder; they do not substitute for it.

## 2. Interpretation families and ties

- Every universe of expressions/shapes/bytes declares ONE vocabulary (the
  tagless trio: `ExprLang`, `ShapeLang`, `WireLang`) with N readings as
  instances: spec reading, raw reading, emission per target, oracle row.
- The AGREEMENTS between readings are by-parametricity/construction where
  possible; where genuinely separate (boxed vs raw semantics) the tie is ONE
  theorem at the structure, cited, never re-proved per lane.
- The duel (below) is regression over these agreements, not the authority.

## 3. Tests as artifacts

- Tests are data folds of the One Universe + the lane tables: RoundTripSpec
  (golden + mandatory negative built in), machine batteries (happy/reject/
  terminal from the Trans tables), op property batteries (positive + negative
  rows per op), witness/conformance rows.
- Generated test modules are byte-tied like any artifact; the generator emits
  them, so the spec cannot drift from its tests, and the "re-list the op table"
  class of test duplication is structurally impossible.
- PURPOSE-DRIVEN hand tests: only genuinely novel behavior and the corruption
  controls (the negative controls that prove a gate has teeth — vacuous suites
  fail loudly, per the Spec discipline).
- Vacuity tripwire: every positive sweep ships its negative control; a control
  the sampler cannot catch is flagged VACUOUS.
- The boundary: generated TESTS are product surface (sanctioned — they run in
  CI); generated CERTIFICATES are verification objects (forbidden — infer them:
  R11). A generated conformance battery is the former; a generated proof is the
  latter.

## 4. The oracle / differential duel as regression

- The oracle's authority is Lean's own evaluation of the spec's semantics; the
  compiled artifact (wasm, emitted Rust) replays the same surface and must
  agree.
- Rows derive from the registry (signatures + bodies) — no hand-mirrored row
  tables; a new schema fn gets oracle coverage by joining the registry.
- The duel verdicts (expected/observed/category/payloadDiffAt) are the shared
  TestKit verdict; every future engine/frontend's conformance gate is an
  instance of the same conformance machinery.
- Sabotage controls are data rows (corrupt inputs, tampered witnesses,
  swapped conventions) — the gate demonstrably catches a wrong engine.

## 5. The acceptance shape of a correctness claim

A claim lands with: the highest ladder rung that works, its evidence (cited
proof / decided / disclosed native / generated row), its E-code, its Spec rows
(positive + negative + vacuity tripwire), its duel rows where a semantics is
involved, and its 06 recipe entry. Claims are obligations; obligations are
data; the gate runs the data (07 §3).

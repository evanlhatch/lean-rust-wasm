# 04 — Errors and diagnostics

Every failure in the toolkit is structured, total, and curated. A bare error is
an unfinished API.

## 1. The diagnostic envelope (one shape, all channels)

One diagnostic record:

```
Diag {
  code     : String            -- stable machine-readable id (the E-code, 04 §4)
  message  : String            -- the curated rendering
  context  : List Label        -- location/context stack (parse: the ParseError ctx)
  got      : Option String     -- what was attempted
  valid    : List String       -- the closed valid space (nonempty for closed worlds)
  suggest  : Option String     -- did-you-mean-derived fill
  severity : severity          -- error | warning | gate | obligation | info
}
```

Channels that all speak this shape: elaboration errors, parse failures
(`ParseError` — 03 §3 — is a Diag with position fields), lint findings,
gate verdicts, obligation rows, oracle divergences, Rust-side spans (emitted
data), and the wasm guest's thin diagnostics (ids only).

## 2. The did-you-mean rule

- Every failure over a CLOSED world renders the valid space + suggestions:
  "no column `iid` — valid: id, name, email — did you mean: id?".
- ONE implementation provides the engine (`CodegenCore.didYouMean`, the
  Levenshtein cutoff engine) and ONE surface renders the suffix. No
  re-implementations of the `" — did you mean: …"` format (there were five).
- The suffix is data: `suggestFor got valid` — a monotone, deterministic fold.

## 3. Instance-search failures (the type-driven gate's error channel)

Type-driven gating (01 §1 rungs 1–2) is only usable if failure is curated:

- Every instance-gated authoring surface (smart constructors, `dsl!` elaborators,
  `[inv| …]`-style surfaces) CATCHES the synthesized-instance failure and
  renders Diag with the valid space. Do NOT expose the raw typeclass-synthesis
  wall.
- `deriving` handlers (05 §2) are REQUIRED to throw curated failures naming the
  record, the capability, and the actionable fix ("no RowBridge instance for
  Foo — add `deriving RowBridge` or a field-type outside the supported set").
- The closed world is what makes this cheap: the valid space is enumerable, so
  the curation is data.

## 4. The tree-wide E-code universe

One code space for ALL diagnostics, Lean-side and Rust-side:

- Codes allocate from ONE position-derived registry (the faults allocator
  scheme): "E{100+i}" per registered diagnostic kind; append-only; the byte-tie
  pins them.
- Every package registers its diagnostic kinds in this universe (elaboration
  `SchemaDiag` kinds, gate verdicts, Rust spans, oracle divergences are rows).
- The wasm guest emits only code ids; humans and tools resolve ids against the
  registry — the fast-observe story completed: the E-code means the same thing
  in an elaboration error, a gate log, a Rust span, and a guest witness refusal.

## 5. Error hygiene rules

- Errors never silently degrade: an obligation with no evidence is a LOUD gap,
  a decode of corrupt bytes is a refusal, an unsupported construct is a throw —
  never a comment or a sentinel value.
- `Validation` (accumulating) is the error carrier for multi-error passes;
  `Except` for single-error. No implicit conversions between them.
- Error messages target the linked model: domain vocabulary + valid space + the
  action. No raw typeclass traces, no "internal error" without context.
- Every new failure path ships: the Diag shape, its E-code row, its curated
  rendering, and (where a closed world exists) its did-you-mean data — in the
  SAME change as the feature (01 §5).

## 6. Acceptance gate

A tour of failure paths — an unknown column, a corrupt parse, a guest-refused
witness, an undischarged obligation, a drifted artifact — each renders as a
structured Diag with a stable code, a valid-space enumeration, and a
did-you-mean where a closed world exists. No bare `none`, no synthesis walls,
no sentinel falses.

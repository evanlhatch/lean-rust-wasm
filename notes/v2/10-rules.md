# 10 — The hard rules: anti-bloat, anti-off-the-rails (enforcement)

These are the reviewables. Every change passes this checklist; a violation
blocks the change or is called out loudly.

## The inference law (severity: BLOCK)

- **R11 No verification-artifact generation.** Verification objects
  (independence, posets, trace sets, vector clocks, POR batteries, causal
  trails, refinement certificates) are THEOREMS and DEFINITIONAL views of
  what already exists — inferred + proved, never freshly generated
  artifacts. The smell test: a verification object that needs NEW data
  (a table, registry, or emitted file) rather than being computable from
  the declaration + theory is a design error. The only sanctioned
  generation: product surface (emitters: WIT/Rust/goldens) and genuinely
  new embeddings (the portable verifier reuses the one checker). A
  "battery/spec/cert" emitted as a file where a `by decide` obligation over
  the inferred structure would do is a violation (02 §3a, 19, 17).

## The hard rules (severity: BLOCK)

- **R1 No parallel tables/worlds.** A fact lives in ONE table; a second
  implementation of the same table (binop semantics, ctor tags, defaults,
  arities, features, sorters, optable, parsers, did-you-mean renders) anywhere
  in the tree is a violation. Duplicate tables are merged, not tolerated.
- **R2 No new universe for an existing concept.** Re-declaring types/equality/
  HasCol/rows/grammars that exist elsewhere requires a written reason + a named
  consumer, and is default-rejected (01 §4, 09 §2).
- **R3 No hand theorem below the ladder.** An invariant with no rationale on
  the proof ladder (01 §1), or checked only by a test, is a violation.
- **R4 No bare errors.** Every failure over a closed world renders the valid
  space (04 §2); instance gates ship curated failures (04 §3); parsers ship
  `ParseError` (03 §3); obligations with no evidence are loud gaps.
- **R5 No cone violation.** A cone-low module imports nothing cone-high (02 §2);
  the import-ban table enforces it as data.
- **R6 No `partial` without a written reason.** The emission layer is total
  (07 §1); the allowance ratchets down only.
- **R7 No second parser/printer.** Every text artifact consumes TextKit's
  grammar value (03). A per-package hand parser is a migration target, not a
  new option.
- **R8 No `@[derived]`-less generation.** Every framework-emitted decl carries
  the stamp; no new `set_option linter…false` rituals.
- **R9 No hand-mirrored registries.** Derived lists (field lists, type names,
  variant cases, codes, oracle rows, arity tables) come from the registry at
  elaboration; a hand mirror is a violation (the `@[schema]`/validate
  discipline).

## The strong preferences (violation = review question, not block)

- **P1 Consume, don't reimplement.** Before ANY mechanism: name the table the
  kit rides, the recipe (06 R1–R6), the core/Batteries lemma. Un-annotated
  new machinery is flagged.
- **P2 Extensibility as the growth test.** A new capability = rows + instances,
  or the design review asks why not (01 §3).
- **P3 One vertical slice per change.** A capability lands end-to-end
  (record → derive → artifact → byte-tie → duel) then generalizes. No
  half-primitives awaiting later wiring.
- **P4 Diagnostics in the same change as the feature.** A feature that ships
  without its Diag/E-code/curated-failure story is incomplete (04 §5).
- **P5 Tests as artifacts.** New test families are folds over lane data with
  vacuity tripwires; hand tests only for novel behavior + corruption controls
  (08 §3). A new test that re-lists spec/op data is a violation of spirit.
- **P6 Elab-shallow.** Instance search stays shallow; generating handlers stay
  linear in the record; elab-time regression is watched (07 §4).
- **P7 Thin headers, decision records only** (01 §5). Essays, changelogs, and
  stale notes are trimmed at the phase boundary.
- **P8 The leftover rule.** Unreachable modules/capabilities are wired or
  deleted at phase boundaries; "future value" keeps a 06 spec line, not dead
  code (01 §4).

## The mandatory review checklist (every change)

1. R1–R9 pass; any R violation is fixed or escalates with a written reason.
2. The One-Table-Many-Consumers name is on the PR body for every new table.
3. Gates green (build + axioms + gates + byte-tie where emission).
4. Diagnostics: E-code row, curated failure, did-you-mean where closed — in the
   diff.
5. `06-extensibility.md` recipe entry written for new capabilities.
6. Proof ladder rationale on any new theorem.
7. Elab-time delta reviewed (07 §4) where type-gates are added.
8. No comment essay; no generated-file edit; one-writer holds.
9. New tests are folds or named novel/corruption content; vacuity tripwires in
   place.
10. The module cone is declared and honored.

## Escalation

A rule conflict (two rules disagree) resolves: 01 axioms > cone (02) > kernel
constraints (09) > preference. All escalations are recorded in the commit
message with the rule numbers. A change that violates R1/R2/R9 without
escalation is reverted at review, not fixed in place.

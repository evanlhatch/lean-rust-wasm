# v2 — the type-first, extensibility-first engineering doctrine (self-contained)

This directory is the WORKING DOCTRINE + BLUEPRINT for engineering the toolkit.
It supersedes earlier notes for new work: if an older note or a code comment
disagrees, v2 wins (then fix the comment). These docs are self-contained: a new
agent executes a phase in `11-sequencing.md` from these documents alone — the
doctrine (01) tells it HOW to engineer; the blueprint (02/03/12) tells it WHAT
to build and exactly how to lay it out; the sequencing (11) tells it what to
create, delete, migrate, and how to know it is done.

## Reading order (agents)

1. `01-principles.md` — the doctrine: correctness as a code property; the
   decision ladder; the two axioms (closed core / open mounts; closed worlds /
   curated errors); the reuse laws; extensibility as the acceptance test.
2. `02-architecture.md` — the TARGET STATE: three kernels, the cone rule, the
   primitives, the One Universe value, the full module tree, key signatures.
3. `03-codegen.md` — THE text-codegen spec: grammar-as-data, lexer, parser,
   printer, inversion, structured errors, dsl!. Concrete types and the
   acceptance gate. Heaviest investment.
4. `04-errors.md` — diagnostics everywhere: Diag envelope, did-you-mean, the
   tree-wide E-code universe, instance-failure curation.
5. `05-kits.md` — the primitive catalog + the deriving-staged protocol.
6. `06-extensibility.md` — the cookbook: "to add a target/lane/capability/DSL,
   fill N rows". The reuse contract.
7. `07-tooling.md` — totality, goldens/byte-tie, gates-as-machine, elab-time
   regression watch, artifact self-audit.
8. `08-verification.md` — the proof ladder, interpretation families, tests-as-
   artifacts, the oracle/conformance as regression.
9. `09-lean.md` — Lean 4 operative rules (kernel constraints, hygiene,
   instance-search discipline, totality, batteries-first, mathlib discipline).
10. `10-rules.md` — the hard rules (R1–R9) + the mandatory review checklist.
11. `11-sequencing.md` — the WORK PLAN: phases with concrete create/delete/
    migrate/acceptance lists, gates per phase.
12. `12-capabilities.md` — concrete specs for the big capabilities: effects,
    liveness, finite model-checking, shrinking, impact gating, the causal
    trail, session boundaries.
13. `13-data-superpowers.md` — the data plane: migrations synthesized from the
    diff + proven by construction, the what-if inspector, reconciliation/audit
    as Z-set algebra, incremental views, CE GAR gate failures, the portable
    proof-carrying verifier.
14. `14-systems.md` — our own substrate: the codegen pipeline as an
    incremental circuit (impact gating as incrementalize), the spec as an
    event-sourced aggregate, host lifecycles as machines, strengthened circuit
    model.
15. `15-provenance.md` — provenance for generated things: the artifact ledger,
    backward/forward queries, regen ergonomics, layout rules, header↔ledger
    agreement.

## How to execute (the agent protocol)

- Read 01–02 fully; read 12 before any capability work; read 03 before any text
  work; read the phase doc(s) you execute fully; consult 04–10 as rule
  references (especially 10's checklist).
- Every change lands on the committed tree with gates green. One vertical
  slice at a time: a capability lands end-to-end (record → derive → artifact →
  byte-tie → duel), then generalizes.
- Every new artifact/capability/package first writes its entry in
  `06-extensibility.md` (the recipe it implements) and its module home in
  `02-architecture.md` §5. If it cannot be expressed as "rows + instances" in
  an existing recipe, it is a design failure: stop and revisit 02.
- Before writing ANY declaration, run 10's checklist and 09's operative rules.
- Diagnostics are part of every feature (03/04), not an afterthought.
- "Done" means the phase's MECHANICAL acceptance test passes — not "builds".

## General value

The patterns here are toolkit-agnostic: type-first correctness, closed/open
typing, generative codegen (grammar → lexer/parser/printer/inversion), the
rows+instances extensibility contract, finite model-checking, the proof
ladder, and the engineered diagnostics/causal-trail discipline. Read them as
engineering doctrine, not repo history.

Note: docs 13–16 are the newest strata — the data superpowers, the
substrate integration, provenance, and theory — read them after 12 when
working in those areas.

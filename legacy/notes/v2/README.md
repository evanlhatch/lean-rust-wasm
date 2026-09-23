# v2 — the type-first, extensibility-first engineering doctrine (self-contained)

This directory is the WORKING DOCTRINE + BLUEPRINT for engineering the toolkit.
It supersedes earlier notes for new work: if an older note or a code comment
disagrees, v2 wins (then fix the comment). These docs are self-contained: a new
agent executes a phase in `11-sequencing.md` from these documents alone — the
doctrine (01) tells it HOW to engineer; the blueprint (02/03/12) tells it WHAT
to build and exactly how to lay it out; the sequencing (11) tells it what to
create, delete, migrate, and how to know it is done.

## Reading order (agents)

0. `00-core.md` — the minimal core: the three roots, the one carrier, the one
   spine; everything else is instances (read before 01).
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
16. `16-theory.md` — the theory integration: ILC (parked → Changeable-
    deriving), quotients (adopt, one place), delimited continuations
    (vocabulary), bisimulation up-to (adopt into Fusion), difference lists
    (doctrine), indexed-type extensions.
17. `17-foundation-contract.md` — declare once, inherit SIX: the derived
    products every declaration ships by default (canonical, change, effect,
    correspondence, statement, behavior semantics) and their inheritance.
18. `18-systems-semantics.md` — the TLA+/Dafny untapped layer: trace sets +
    refinement, stutter/fairness, assume/guarantee boundaries, function
    contracts; the property-classification doctrine.
19. `19-events.md` — the TraceModel: traces as partial orders; denotation
    (machines/circuits/schedules/provenance denote into it); POR
    soundness proved once; vector clocks; causal debugging as the DAG;
    the INFERENCE LAW (verification = theorem of the declaration, never
    generated artifacts) — 02 §3a, 10 R11. (Mazurkiewicz equivalence,
    happens-before, partial-order reduction, what-if as the cone, slicing,
    MUS, why-provenance.)
20. `20-roots.md` — the layered model: Universe/Change/TraceModel ×
    Statement/Correspondence; kernels and instance libraries; the
    inheritance-of-provability table; the instantiation checklist.
21. `21-application-modeling.md` — application modeling: the completed
    effect kernel (failure row, linearity, determinism, observe), the
    tabular layer (certified rewrites, windows, indexed tables, TVL),
    transactions as instances, and the TRUST DOMAIN primitive.

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

Note: docs 13–21 are the newest strata — the data superpowers, the
substrate integration, provenance, theory, the foundation contract, and the
systems-semantics layer — read them after 12 when working in those areas.

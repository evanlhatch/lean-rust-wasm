# 10 — Sequencing: the work plan

Each phase lands green (build + axioms + gates + byte-tie where
emission). One vertical slice at a time: a capability lands end-to-end
(declare → derive → artifact → byte-tie → duel), then generalizes.
"Done" = the phase's mechanical acceptance test, not "builds".

## Phase 1 — The relational data plane's first slice

The bidirectional proof-of-life (03 §9): keyed tables with a foreign
key; a handwritten Rust command proposes a delta; the incremental
violation query checks the proposal; the transactional adapter commits;
the derived view updates; a view edit maps backward through the checked
lens. Creates: the valid-worlds discipline (02 §1) on one bounded
surface, the FD-driven result typing (02 §3) on its queries, the
violation-relation lane (03 §8), the proposal/commit adapter, the lens
writeback. Acceptance: the slice end-to-end; a violating proposal
refused with the violating rows; a view edit with ambiguous base update
refused with the named ambiguity.

## Phase 2 — The graded carrier + the relational engine

The correspondence library's grading (01 §4: iso/retraction/codec/
normalization/refinement/abstraction with shared composition/transport)
+ the fundamental theorem per interpretation pair (01 §6). Migrates:
the kit's Iso/PartialIso/CheckedProp/Obligation onto the graded library
(statements as the Bool↔Prop instance; obligations as the structure over
it); the per-lane tie families onto the generic theorem. Acceptance:
the lands keep their laws (the axiom report's footprints unchanged or
honestly smaller); a new interpretation pair gets its agreement theorem
from the generic one + per-primitive instances.

## Phase 3 — The deriving protocol's description layer

The typed description of supported structure (05 §3) + the generic
derivations over it; the existing handlers migrate to thin wrappers.
Curated failures land first. Acceptance: a record's entourage derives
from its description alone; a field change is caught in one place; the
reifier count does not grow.

## Phase 4 — The text layer

TextKit's grammar value (typed, bidirectional, the predictive fragment)
+ lexer/parser/printer/inversion + dsl!. Migrates: two existing formats
onto grammar values (a sectioned wire + one manifest); substrait's
Decode onto the kit. Acceptance: goldens byte-identical; `parse∘emit`
is a generated theorem; curated ParseError everywhere; elab-time flat.

## Phase 5 — The One Universe + the Change ladder

The Universe value as the fold of the registries (the extensions stay
the compile-time machinery; the Universe is the snapshot-time object);
the Change capability ladder in the lanes (inverses derived only where
lawful); the event-sourced spec (the snapshot = the integral; the
breaking diff = D). Acceptance: one snapshot covers all lanes; a lane
adds one field + one member registration + one derived reader.

## Phase 6 — The wasm deep work

One instruction AST (design-one-instr-ast.md); the op table (one row per
op driving Sem/checkStack/audit/edgepython); the stack-typed executor;
schema-driven adapters. Acceptance: per that design doc's sequence +
the byte-tie gates.

## Phase 7 — Effects + sessions + the application stratum

The effect/resource split (08 §8) with the footprint laws + the frame
rule; boundary session types with generated adapters; the middleware/DI/
routing/transport/caching/config patterns (08 §29-34) as their slices
arrive. Acceptance: over-permissive composition fails to elaborate;
the WIT capability set = the join of export rows.

## Phase 8 — The systems semantics (liveness, fairness, contracts)

The property taxonomy + trace-set refinement + the observer
parameterization (04 §4) + wp-composition for the contracted lanes +
the monitor mount (08 §26). The TraceModel's heavy half (POR with its
named premises, vector clocks) lands HERE — behind its first concurrent
consumer, per the sequencing correction. Acceptance: a livelocked
variant fails strong-fairness with its trace; a contract's obligations
compute by wp and discharge the routine fragments.

## Phase 9 — The data superpowers

Migrations synthesized from the diff (stable identities required) +
the local preservation equation + what-if + reconciliation/audit as
Z-set algebra + incremental derived views + the semantic-diff witnesses
(08 §27). Acceptance: renaming/widening a demo field yields a generated
upcaster + the discharged preservation obligation + the dry-run over
the committed journal.

## Phase 10 — The portable verifier

The proof-carrying artifact (data + witness + the compiled checker +
the PINNED checker identity — a real digest, not a bare hash) + a
second embedder as the portability proof. Acceptance: two independent
embedders verify identically; a tampered payload/claim/proof refuses
with the same E-code on both sides; the verifier's effect row is
`[read witness-bytes]` only; the doc states what agreement does and
does not prove (portability, not checker soundness).

## Phase 11 — The toolkit on its own substrate

The codegen pipeline as the incremental circuit (impact gating as
incrementalize — 09 §6); the spec as the event-sourced aggregate; the
host lifecycle as a machine; the provenance ledger completing the
chain (spec row → emitter fold → ledger row → byte-tie → obligations →
duel coverage). Acceptance: the forward/backward provenance queries
answer from the ledger; a one-line spec change re-checks exactly the
affected set.

## Standing rules for every phase

The checklist (the hard rules): no parallel tables/worlds; no new
universe for an existing concept (written reason + named consumer or
default-rejected); no hand theorem below its ladder rung without
justification; no bare errors (closed worlds enumerate the valid space;
instance gates ship curated failures; parsers ship ParseError;
undischarged obligations are loud gaps); no cone violation (the ban
table as data); no partial without a written reason; no second parser/
printer (TextKit consumes); no `@[derived]`-less generation; no
hand-mirrored registries. Plus the preferences: consume don't
reimplement; extensibility as the growth test; one vertical slice;
diagnostics in the same change; tests as artifacts (folds with vacuity
tripwires; hand tests only for novel behavior + corruption controls);
elab-shallow; thin headers (owner/exclusions/decision only); the
leftover rule at every phase boundary. Escalation: 01's axioms > cones
> kernel constraints > preferences; conflicts record the rule numbers
in the commit message.

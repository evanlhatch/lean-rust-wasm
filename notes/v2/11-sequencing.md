# 11 — Sequencing: the work plan (phases with concrete artifacts + acceptance)

Each phase lands green: `just lean-build && just lean-axioms && just gates`
(+ byte-tie where emission). Every phase lists what to CREATE, DELETE, and
MIGRATE, and a MECHANICAL acceptance test. One vertical slice at a time:
capability lands end-to-end (record → derive → artifact → byte-tie → duel),
then generalizes.

## Phase 1 — Boundaries (cones first)

**Creates:** `schema-core` package (02 §5 layout): Ty/Value/Field/HasCol/
RowVals/ColPath/VExpr/ExprLang/Lens/Codec/CodecValue/DefaultVal/Bridge moved
(imports rewired; module bodies unchanged at first). `wasm-core` lean_lib:
Wat/Op/Sem/Layout/Audit moved; edgepython + the LCNF backend import it.
`CodegenCore.ElabKit`: AttrKit + GenKit + MemberKit consolidated; faults'
attribute registries ride `declare_registry_member`.

**Deletes:** nothing yet (pure re-homes).

**Migrates:** substrait gains ONE consumer of `schema-core` (Bridge import)
to prove the core is reachable from a public world.

**Acceptance (mechanical):** `grep` — no C0/C1 module imports Mathlib/Dbsp/
Machines; substrait compiles `import SchemaCore.Bridge`; byte-tie green; build/
gates green.

## Phase 2 — Primitives + diagnostics + the deriving protocol

**Creates:** `Statement.lean` (+ mounts: gate/lint/test/obligation); RecordKit
protocol (first capability: `RowBridge` deriving handler — fields + row +
`Iso`); the Diag envelope in `CodegenCore.Errors` + did-you-mean suffix ONE
way; E-code universe extended (every package registers its diagnostic kinds).
**Migrates:** CheckedProp/DeclCheck/BareChecker/Wf-idiom converge on Statement
(first consumers: universe WF, keys legality); five did-you-mean renderers fold
to one. **Deletes:** the parallel decline of the four carriers; the
`set_option linter…false` ritual sites (the `@[derived]` stamp replaces them).

**Acceptance:** a record gains its entourage via ONE `deriving` line; an
unknown-field error renders "valid: …" + did-you-mean from the deriving
handler's curated failure; obligation evidence kinds are CLOSED (compile a
hostile string-typed evidence test that fails); elab-time delta flat.

## Phase 3 — The TraceModel + finite model-checking + liveness (build in from the outset)

**Creates:** `CodegenCore.TraceModel` (19: events + independence + causal
order + the POR-soundness/refinement theorems proved ONCE — the
fundamental model); `CodegenCore.ModelCheck` (12 §3 — finite enum +
transition + decidable property → verified-cert or counterexample-trace;
budget-bounded); `Machines.Trace` liveness predicates (12 §2); the
`machine!` entourage extension — the DENOTATION (events/independence/poset
as definitions over the declaration + effect rows) + the liveness/
fairness/POR-battery rows as `by decide` obligations OVER that denotation
theorem (never generated files; 02 §3a / R11).
**Migrates:** the three existing machine batteries (order/feature-flags/
pipeline) from sampled conformance to exhausted, POR-reduced, inferred
certificates.

**Acceptance (mechanical):** for each machine, the battery states "every
reachable state satisfies P" via the inferred denotation + the POR
soundness citation; independence is a definition over the effect rows with
a `by decide` certificate (no emitted verification artifacts); a
deliberately dead-end machine yields a COUNTEREXAMPLE TRACE that fails
loud; board truncation is a reported error, never silent (12 §3 guard);
the causal/trace-set/vector-clock views are definitional, not generated.

## Phase 4 — The text codegen layer (03)

**Creates:** TextKit files (03 §8): Grammar/Lex/Parse/Guest/Inversion/Dsl.
**Migrates:** re-express TWO existing formats as Grammar values (03 §9: a
sectioned wire + one manifest); substrait's Decode Parser onto the kit.
**Deletes:** the per-format hand parser/printer/proof families they replace.

**Acceptance (mechanical):** goldens byte-identical; `parse∘emit` is a
GENERATED theorem; corrupt/ambiguous rows refused by data; structured
ParseError with position/expected/context/valid-space; elab-time flat.

## Phase 5 — The One Universe + convergence

**Creates:** `Universe.lean` (02 §4) + per-lane fields + snapshot cases.
**Migrates:** items/invariants/updates/keys/witnesses/migrations into the
Universe value; the break gate diffs one file; every goldens fold reads it.
**Deletes:** the parallel registry scaffolding per lane (MemberKit absorbs).
**Convergence (carried items):** the two keyed applicators merge; the nine
neutrality families absorb into lens laws; SType beq into DecidableEq; the
leftover table (06) executed (wire or delete).

**Acceptance (mechanical):** one snapshot file covers all lanes; new lane =
one field + snapshot case + emitter rows; R1 sweep green (no parallel tables).

## Phase 6 — The wasm type-first deep work

**Creates:** `Op.lean` (the ONE op table); stack-typed `Sem.Instr` (checker =
derivation); typed target ASTs (`RustItem : Ty → Type`, …).
**Migrates:** Sem executes Wat.Instr (one AST; the translation seam dies);
adapters fold from the schema (the five hand shapes replaced).
**Deletes:** `lower`/`lowerGo`; the per-op hand places; the `rawCount` vestige.

**Acceptance (mechanical):** `typeSafety`-style theorems hold per op via
induction over derivations; wrong-typed constructs unrepresentable
(grep-negative: no `Instr.raw` in the backend except the documented splice
marker); byte-tie green on the re-emitted artifacts.

## Phase 7 — Effects + sessions (the type-driven app stratum)

**Creates:** `Effect` lattice + `HasEffects` (12 §1); `Boundary` session types
(12 §7). **Migrates:** reads/writes/GuestBan/determinism columns onto the
lattice; adapters generated from boundaries.
**Acceptance:** an over-permissive composition fails to elaborate; the WIT
capability set = the join of exported rows; a wrong boundary fails
construction.

## Phase 8 — Observability + dev loop (the causal trail, impact gating, shrinking, conformance engine)

**Creates:** `CodegenCore.Trace` (the Trail, 12 §6); TestKit `Shrink.lean`
(12 §4); the `--affected` filter (12 §5); the conformance engine (duel as an
instance, 08 §4); the systems-semantics kit (18: trace-set refinement,
stutter/fairness batteries, A/G boundaries, fn contracts) — the machine!
entropy grows the sixth product and the property-classification rows.
**Migrates:** oracle `explain` → full causal trails; the oracle's verdict
machinery → TestKit Verdict; every new engine/frontend gets the conformance
instance. **Adds:** the bisimulation up-to theory into Fusion (16 §4).
**Acceptance:** a sabotaged artifact's trail ends in the divergence category +
the responsible spec row; a one-line spec change re-checks only its package's
artifacts; a failing suite reports a shrunk minimal case; duplicate duels land
as conformance instances, not new harnesses. A two-machine
  system's trace-set-equality + stutter batteries are green; a livelocked
  variant fails strong-fairness with the trace; a guest fn's
  requires/ensures flow boundary+duel (18 §6).

## Standing rules for every phase

- One vertical slice per change; end-to-end before generalize. | R1–R10
  checklist (10) run over each diff. | Every new text artifact consumes 03;
  every legality consumes Statement (05 §1); every table consumes 06 recipes.
  | Elab-time deltas watched (07 §4). | The leftover table updated each phase
  (06); unreachable rows wired or cut.

## Phase 9 — The data plane (migrations, what-if, reconciliation, incremental views)

**Creates:** change-derived migrations + per-migration preservation obligations
(13 §1); the what-if inspector (13 §2); reconciliation + audit-as-integral
(13 §5); incremental derived views (13 §6).
**Migrates:** hand-written upcasters onto `Change`-derived folds; the breaking
gate gains the remedy/obligation rows.
**Deletes:** hand upcasters whose changes are in the closed change enum.

**Acceptance (mechanical):** renaming/widening a demo field yields a generated
upcaster + a discharged preservation obligation + a what-if dry-run over the
committed journal; the diff readout between two points is the algebraic Z-set
delta; a divergent replica converges with the group-law certificate.

## Phase 10 — The portable verifier (the product capstone)

**Creates:** `ProofCarryingArtifact` packaging (13 §3) — data + witness + the
compiled verifier module + declared hash; a SECOND embedder (standalone Rust
host) as the portability proof.
**Migrates:** the guest-checked witness lane into the pack; the conformance
engine rows for the two-embedder identity check.

**Acceptance (mechanical):** two independent embedders verify the same artifact
identically; a tampered payload/claim/proof refuses with the SAME E-code on
both sides; the verifier's effect row is `[read witness-bytes]` only (12 §1).

## Phase 11 — The toolkit on its own substrate (systems + provenance)

**Creates:** provenance infrastructure (15: the artifact ledger + provenance
reports + regen-by-artifact); the codegen pipeline as an incremental circuit
(14 §1 — impact-gated rebuild = incrementalize over stages).
**Migrates:** the gates/forge onto the provenance ledger (byte-tie rows,
one-writer, self-audit read the same ledger); the runtime host lifecycle onto
a machine (14 §3, instantiation/backpressure states).
**Deletes:** ad-hoc per-driver loop tails that the ledger's workflows now fold.

**Acceptance (mechanical):** asking "what spec row feeds this artifact" and
"what artifacts does this spec row affect" are ledger queries; a one-line spec
change re-checks exactly its requested artifacts (provenance-fed impact, 14
§1 + 12 §5); every artifact header resolves to a full provenance chain.

## Standing rules for every phase

- One vertical slice per change; end-to-end before generalize. | R1–R10
  checklist (10) run over each diff. | Every new text artifact consumes 03;
  every legality consumes Statement (05 §1); every table consumes 06 recipes.
  | Elab-time deltas watched (07 §4). | The leftover table updated each phase
  (06); unreachable rows wired or cut. | Data-plane capabilities cite the
  landed algebra theorems (EventSourced/RewindableMachine/Replicas), never
  re-prove them (13 §0). | Generated artifacts always have provenance rows
  (15); a generated file without a ledger entry is a review failure. | Quotients follow 16 §2 discipline (never on wire/guest/decide layers); text = Format/join (16 §5).

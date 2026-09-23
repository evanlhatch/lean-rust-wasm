# 14 — The build map: from-scratch construction + the port/rework map

The v3 system is built FRESH (a new tree), porting proven content from
the current codebase into the new structure — not an in-place migration.
This file is the process + the per-library decisions. The doctrine
(00–10) governs every step; the system description (11) is the as-built
map of the tree being ported FROM.

## 0. The process (how a build step works)

1. **Foundations before content, content before consumers.** Cones in
   order: C0 (machinery) → C1 (domain cores) → C2 (theory) → C3 (apps +
   lanes) → the Rust/WASM consumers LAST (the emission surface must be
   stable before hosts port against it — porting a host against a moving
   emitter is the waste the ordering exists to prevent).
2. **Every port is a vertical slice, green on arrival:** the new tree's
   gates exist from the FIRST commit (the byte-tie, the axiom gate, the
   lints, the kernel sweep — the gates package scaffolds first, thinly,
   and grows). Nothing lands red, ever.
3. **Porting ≠ copying:** a port re-homes the CONTENT (the statements,
   the laws, the proof content) into the new structure's shapes —
   declarations get the new discipline on arrival (the deriving protocol,
   the correspondence declarations, the obligation rows), never a
   verbatim lift of machinery v3 replaces.
4. **Proofs port as content:** a theorem's STATEMENT + its proof term
   are the payload; the new tree's kit absorbs them (the kit's shapes
   exist to receive them). Where a proof fights the new shape, the
   SHAPE is wrong or the port is incomplete — say which, never stub.
5. **Nothing ports museum pieces:** the current tree's delete-or-
   graduate lists and the audits' dead-code findings apply at the port
   boundary — a module/capability with no consumer in the new tree is a
   07 spec line, not a port.
6. **The docs travel with the code:** each ported lane's module headers
   are rewritten thin (owner/exclusions/decision — 01 §5); the design
   docs' content that remains valid folds into the capability specs (08);
   the rest stays in the old tree's history.

## 1. The port/rework map (per current library)

| Current | Verdict | The note |
|---|---|---|
| codegen-core (kit, Emit spine, GenKit/AttrKit, registries) | PORT nearly whole | the kit generalizes to the graded carrier on arrival (Phase 2's work lands AS the port) |
| TextKit | PORT | the parser core; the typed bidirectional grammar layer is Phase 4's build ON TOP of it |
| TestKit | PORT | PropSpec/lcg/harness; Shrink lands per its spec |
| LintKit | PORT | the linter engine + the table, incl. the enforcement lints |
| gates | PORT + grow | the driver + the subcommands; the audit/manifest channels land per 09 |
| Machines | PORT | the machine lane + the fusion bridges; the TraceModel denotation arrives with its first concurrent consumer (Phase 8) |
| dbsp | PORT whole | the proven algebra — and the weighted-relation layer (02 §4) lands as an ABSTRACT layer with ℤ as its first instance; the proven ZSet surface is never rewritten |
| substrait | REWORK-heavy | the Proto types + typed layer + Grammar tables port; the Decode ladder re-homes onto the grammar layer (Phase 4) — its LEMMAS port as content, its parser core is rebuilt |
| schema-lang | SPLIT + PORT | schema-core (Ty/Value/RowVals/Codec/predicates — core-only) ports nearly whole; the lanes port through the Phase-2/5 migrations (graded carrier, the Universe fold, the Change ladder); the Meta layer ports through the description layer (Phase 3); emitters port with laws populated |
| wasm-backend | REWORK-heavy | Wat + the runtime port; Sem/Correct rework per the one-AST design (Phase 6); the oracle ports (its row machinery is current); GenMain ports (the structured seam is landed) |
| std (GuestlangStd) | PORT | the intrinsic bodies + guest impls |
| qlang | REWORK | retargets onto schema-core (its parallel universe dies); its compile logic ports through the retarget |
| edgepython | PORT + delete | the frontend ports; its hand evaluator dies when the op table lands (Phase 6) — until then it stays with its header note |
| ledger / feature-flags / faults | PORT | the dogfoods ride the deriving protocol on arrival |
| proofkit | PORT | its op laws find their consumer in the op table |
| The Rust crates (guestlang-host, guestlang-rt, wasm-delta, oracle-runner, forge, fixtures) | PORT LAST | the post-consolidation crates ride the finalized emission surface; the test evidence (differentials, fault-injection, bolero lanes) ports with them |
| wire / lean-sys / lean-ffi / forge-push-pull / the pool lane | DO NOT PORT | dead in the current tree already; the jj history keeps them |

## 2. The build order (the phase alignment)

1. **The scaffold + the C0 machinery:** the new tree's lakefile + the
   gates' thin skeleton + codegen-core + TextKit + TestKit + LintKit
   ported. The doctrine's discipline (the byte-tie, the axiom gate, the
   lints, the kernel sweep) runs from the first commit.
2. **The C1 cores:** schema-core (the Ty universe + the row layer + the
   codecs + the predicate core) + wasm-core (Wat + the op table's first
   shape + Sem). The graded carrier + the relational engine land here
   (they're machinery — early, per the owner).
3. **The C2 theory:** dbsp + Machines ported; the Change ladder + the
   weighted-relation layer land; the Fusion bridges port.
4. **The C3 app layer:** the schema lanes + Meta + the emitters + the
   errors/diagnostics plane; the deriving protocol complete.
5. **The targets + dogfoods:** vortex, the query fragment, edgepython,
   ledger, feature-flags, faults — each a slice per 07.
6. **The consumers (late, per the owner):** the Rust crates + the wasm
   guests — ported against the stable emission surface, with their
   evidence suites.

Each step's acceptance = its phase's mechanical test (10) + the new
tree's gates green + the ported content's laws cited in the new tree's
axiom report.

## 3. What does NOT port (the honest exclusions)

- The current tree's tooling-internal scars: the per-package lakefiles,
  the retired inventory gate, the clobbered-and-restored recipes — the
  new tree starts with the doctrine's tooling, not the old tree's
  battle history.
- The museum pieces already deleted or flagged (the decruft waves'
  lists are the port boundary's checklist).
- The deferred laws' failed attempts (the snapshot round-trip's three
  attempts): the LAW ports as a deferred row with its cost record; the
  attempts don't.
- v2-as-text: v3 supersedes it; the old tree's notes stay in its own
  history. The studies (notes/studies/) + the decisions ledger ARE the
  durable parts — they port as references.

## 4. The first-commit contents (the scaffold)

The new tree's first commit: the lakefile + the gates' skeleton + the
justfile's thin spine + the notes/ (this doctrine set + the decisions
ledger + the studies) + the C0 libraries' first ports. Acceptance: the
gates run green on the scaffold itself — the byte-tie, the lints, and
the axiom gate all have teeth before any content arrives.

# v3 — the doctrine, synthesized

The toolkit's working doctrine + blueprint. Supersedes v2 (kept in
`notes/v2/` as history) and the older notes (`notes/archive/` carries
them). Every claim here survived four independent reviews + the session's
execution evidence; the *why* of every correction lives in
`decisions.md`, never inline.

**The architecture in two sentences.** Structure composes;
interpretations preserve structure; proofs compose through explicit
relations. Every crossing declares the strongest honest law and reports
what survives; every valid composition is cheap, every required premise
is explicit, every inherited guarantee is mechanically justified.

**What the toolkit IS:** formally model an application in Lean — data,
changes, behavior, protocols, obligations — and generate its
Rust/WASM/WIT/vortex surfaces with the correctness flowing down by
construction. Correctness is a code property: wrongness does not
elaborate, does not synthesize, does not construct, does not typecheck.
Proofs are the residue the type system cannot reach, and even those are
generated, decided, or written once at the structure and cited — never
carried per-instance.

## Reading order (agents and humans)

0. `01-core.md` — the minimal foundation: three roots, one carrier, one
   spine, the relational engine. Read first; everything else is instances.
1. `02-data-plane.md` — the relational center: valid worlds, constraints
   as the shared authority, weighted relations, commands-as-relations.
2. `03-bidirectional.md` — the Lean↔Rust discipline: one owner per fact,
   propose→check→commit, the evidence levels, the complement lens.
3. `04-verification.md` — the proof ladder, obligations, certificates,
   observers, feasibility, the kernel sweep, the trust axes.
4. `05-codegen.md` — the generative layer: grammar-as-data, emitters,
   the deriving protocol, diagnostics.
5. `06-lean-rules.md` — the Lean 4 operative rules (the traps catalog).
6. `07-extensibility.md` — the cookbook: add a target/lane/capability/DSL.
7. `08-capabilities.md` — the capability catalog (concrete specs).
8. `09-gates-ops.md` — gates, byte-tie, provenance, the dev loop.
9. `10-sequencing.md` — the work plan: phases + mechanical acceptance.
10. `decisions.md` — the review corrections as decision records.

## The execution protocol (every change)

- One vertical slice per change: capability lands end-to-end (declare →
  derive → artifact → byte-tie → duel), then generalizes.
- Every new capability first writes its 07 recipe entry + its 08 spec
  line. If it can't be expressed as rows + instances of an existing
  recipe, it is a design failure: stop, revisit 01.
- The review checklist (10's standing rules) runs over every diff.
- Gates green before commit; "done" means the phase's mechanical
  acceptance test passes, not "builds".

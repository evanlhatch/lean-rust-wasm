# 01 — Principles

The doctrine that governs every engineering decision in this toolkit.

## 0. The one-sentence view

Correctness is a CODE PROPERTY: a wrong thing either does not elaborate, does not
synthesize, does not construct, or does not typecheck — it is not caught at
runtime and fixed by a test. Proofs are the residue the type system cannot reach,
and even those are generated or decided, never carried by hand.

## 1. The decision ladder (apply to EVERY invariant)

When some property must hold of a value, structure, artifact, or gate, choose the
highest rung that works. Lower rungs are allowed only with a written reason.

1. **Unrepresentable** — index the type so the illegal state has no constructor
   (`Value : Ty → Type`, `RowVals fs`, `TVal t dims`, length-indexed lists,
   `Fin`-indexed codes/arities). Wrongness cannot be expressed.
2. **No-instance** — legality by instance search (`HasCol`: a misspelled field is
   a missing instance, i.e. an elaboration error, not a runtime bug).
3. **Defaulted proof field** — `p : P := by decide` (or `by po_ladder`) inside the
   structure: constructing the value is discharging the invariant; failure to
   elaborate blocks construction. Covers nodup-ness, legality, coverage, counts.
4. **Generated theorem** — the family! / deriving machinery emits the proof from
   a table (machine! entourage, declare_inversion, wire round-trips).
5. **Disclosed native_decide** — decidable but heavy judgments run in the kernel;
   the disclosure is itself a gate row (the trust base is named and audited).
6. **Hand theorem** — the LAST resort, with a written justification: "this is
   relational/fixpoint/perturbation content the type system cannot compute."

A hand-written theorem with no justification on the ladder, or an invariant
checked only in a test, is a review failure.

## 2. The two axioms

**A1. Closed core / open mounts.** The *core* of any judgment is a closed
enumerable type (`Obligation.Evidence`, `Tier`, `Ty`, grammar terminals). The
*mounts* (gate / lint / test / obligation row / duel) are open; anything can
observe the closed core. An open core (string-typed evidence, string-typed
tiers) dissolves the armed-and-fired discipline — forbidden.

**A2. Closed worlds / curated errors.** Every failure of a closed-world
judgment enumerates the valid space: "no field `iid` — valid: id, name, email"
via the shared did-you-mean machinery. A bare error (typeclass synthesis wall,
`none`, `throw "failed"`) is an unfinished API. This includes instance-search
failures: every instance-gated authoring surface ships a curated "why not" via a
smart constructor or DSL that catches the synthesized-failure and renders the
valid space.

## 3. Extensibility is the acceptance test

Every new target language, capability, lane, or DSL must be expressible as
**rows + instances** (see 06). If a feature needs new modules, new universes, or
new proof families instead of filling tables, it violates the architecture — stop
and revisit 02. The metric that matters is not LOC but the **marginal cost of the
next thing**.

## 4. The reuse laws (make bloat hard)

- **One table, many consumers.** A fact lives in one table row; everything that
  knows it is a fold of the table. Binop semantics, ctor tags, defaults, op
  semantics, feature vocabularies, arities: ONE row, N consumers. Duplicating a
  table into a parallel one anywhere is the highest-severity violation.
- **No new universe for an existing concept.** A new world that re-declares
  types/equality/rows/grammars that exist elsewhere is a decision to reimplement;
  it requires a written reason and a named consumer, and it is default-rejected.
- **Consume, don't reimplement.** Before writing any mechanism, ask: does a kit
  primitive, a core/Batteries lemma, an existing emitter/registry/statement
  family, or a generated artifact already provide this? Cite it. (Checklist in 10.)
- **The leftover rule.** Any module or capability with no consumer is reviewed at
  every phase boundary: wire a consumer or delete it. "Future value" is not a
  reason to keep unreachable code; it is a reason to keep a one-line spec in 06.

## 5. Structure discipline

- **Cones, not packages-by-feature.** Every package/module occupies one dep cone
  (see 02 §2): a cone-low module may never import cone-high modules. Violating
  the cone is what traps reusable cores inside unusable closures.
- **Pure core, IO shell.** Emitters, generators, gates' logic are pure functions
  of data; drivers do IO. The registry is the only ambient state the pure core
  reads.
- **Thin headers, decision records only.** Module headers carry owner, deliberate
  exclusions, driving decision — three lines. No essay archaeology, no changelog,
  no book-report provenance.
- **Diagnostics are part of the feature** (04): any API that can fail ships the
  failure's structure and its curated rendering in the same change.

## 6. Tech-debt response (what "off the rails" looks like)

Violations to stop the line for: parallel tables/worlds (4), `partial def`
without a written reason (09 §6), hand theorems on the ladder below rung 4
without justification (01 §1), instance gates without curated errors (A2),
emitter byte-drift without a regen cycle (07), new universe re-declarations (4),
and comment essays (5). The review checklist in 10 exists to make stopping cheap.

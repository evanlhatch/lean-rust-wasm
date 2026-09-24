# decisions.md — the correction ledger

Every review correction + every doctrine-changing decision, one entry
each: what changed, why, where it landed. The doctrine files state the
true thing; THIS file carries the why. New corrections append.

## From the four reviews (2026-09-22/23)

**D1. Crossings are graded, not isomorphic.** My (00-core v1) compression
"Statement ≅ Correspondence" overclaimed: soundness alone is a directed
map; completeness upgrades it. → the graded-correspondence library
(01 §4). Provenance: review 1 §1.

**D2. "Provably irreducible" roots → evidence-not-theorem.** The roots'
separation walls are documented engineering evidence (no negative
states; posets can't express conflict; closed codes can't behave);
a better model may exist and would be adopted deliberately. → 01 §1.
Provenance: review 1 §1.

**D3. Change is a capability ladder.** Reversibility is the upper rung,
not the foundation (set-forgets-old-value, emails don't un-send,
compensation ≠ undo). → 01 §2 + the lanes' change rows. Provenance:
review 1 §2.

**D4. The migration law's correct shape.** The LOCAL equation
(`migration (applyOld s e) = applyNew (migration s) (upcast e)`), with
replay preservation by ONE induction — replaces implying migration
correctness follows from possessing a Change instance. → 02 §-migrations
+ the witness lane's shape. Provenance: review 1 §2.

**D5. The incremental derivative needs the old input.**
`f (apply x dx) = apply (f x) (deriveChange f x dx)` — `Δf Δ` alone is
insufficient. → the ILC parking note. Provenance: review 1 §2.

**D6. The TraceModel's poset ≠ a machine's behavior.** One poset = one
execution's causal order; behavior = a SET of executions with conflict.
Transition semantics authoritative; traces/posets/observations/
equivalences are derived views. Finite states ≠ finite executions;
trace-eq ≠ bisim; fairness is an assumption; POR preserves only the
named property classes under explicit premises; bounded exploration
answers proved/refuted/unknown. → 01 §3 + the TraceModel docs. The
review caught this BEFORE the heavy half was built — the strongest
evidence for docs-first review. Provenance: review 1 §3.

**D7. Effects ≠ resources.** Set union cannot enforce linearity
(`{consume h} ∪ {consume h}` loses the double-spend). Effects = upper
bounds; resources = usage accounting with context-splitting; the frame
rule is the independence foundation. Plus: a metadata effect row proves
nothing unless the implementation respects it (footprint laws named).
→ 08 §8 + the effects lane. Provenance: review 1 §4.

**D8. wp-composition is the contract layer's composition engine** —
scoped to the contracted lanes (contracts/sessions/transactions/
effects); total pure functions keep direct proofs. → 08 §36.
Provenance: review 1 §5.

**D9. R11 reversed to "no duplicate semantic authority."** Generated
evidence + independent checking is the strongest architecture (the
certificate pattern); what stays forbidden is a verification artifact
as a second authority. → 04 §3. Provenance: review 1 §6.

**D10. Trust has four axes** (strength/method/checker/assumptions),
not one domain value; dependencies compute from the evidence chain.
`oracleSwept` = tested agreement, never a universal theorem.
→ 04 §6. Provenance: review 1 §6.

**D11. The grammar foundation gets the honest fragment.** Typed
bidirectional combinators; the certified predictive-grammar fragment
(ambiguity undecidable in general); rep needs progress; FIRST+FOLLOW;
the two honest laws (parse∘print = id; print∘parse = canonicalize);
text-roundtrip ≠ artifact semantics. → 05 §1. Provenance: review 1 §7.

**D12. Capability-directed derivation, not inherit-everything.** Not
every type has a computable canonical form; not every change is
reversible; not every property is decidable. Derive lazily; obligations
at the declaration site. → 05 §3 + 07. Provenance: review 1 §8 +
review 2 §9 (thin wrappers, generic theorem first).

**D13. The distributed/data corrections.** Transactions need crash/
visibility/isolation content beyond batch+inverse; Z-set merge commutes
but `Δ+Δ≠Δ` (replication needs event identity/dedup); exactly-once is
specified at a named observable boundary under named failure
assumptions; migration discovery needs stable identities; position-
derived E-codes drift on import order (stable persisted allocation);
config last-wins is not a semilattice. → 02/03/04/08 respective sections.
Provenance: review 1 §9.

**D14. Four verification dimensions added:** abstract interpretation
(soundness per transfer function + untrusted-search/verified-checker;
shrinking is NOT CEGAR — CEGAR = abstraction + concretization check +
refinement), relational verification/hyperproperties (noninterference,
schedule-independence — single-execution properties can't say these),
crash/recovery refinement (first-class crash steps + persistent/volatile
separation), quantitative semantics (a graded interpretation, on
request). → 08's new sections + 04. Provenance: review 1 §10.

**D15. Build/artifact corrections.** Provenance demand-sets are unsound
for additions (negative/collection dependencies recorded; conservative
invalidation proved); artifact ownership is global (cross-emitter
disjointness + declared-vs-actual agreement); the portable verifier
pins the CHECKER by digest (two embedders agreeing proves portability,
not soundness). → 09 §4 + Phase 10. Provenance: review 1 §11.

**D16. The relational engine is the proof-reuse spine.** Bundled
interpretations + explicit relations + per-primitive preservation +
one generic theorem per interpretation pair — replaces generating
theorem batteries per declaration. → 01 §6. Provenance: review 2 §1.

**D17. Meaning ≠ representation.** `Represents concrete abstract` +
operation preservation; isomorphism is often unnecessarily strong
(hash tables with different tombstones represent the same map).
→ 01 §4's table + the graded library. Provenance: review 2 §2.

**D18. Observer-parameterized equivalence.** "Same behavior" takes the
observer as data (api/audit/perf/security observers); instrumentation
preserves API semantics without pretending logs unchanged. → 04 §4.
Provenance: review 2 §3.

**D19. The description layer.** Reflect each record once into a typed
description; derivations are generic over it (thin wrappers per
declaration). The ONE deliberate meta-universe exception (R2). → 05 §3
+ Phase 3. Provenance: review 2 §4+§9.

**D20. Dependent schemas first-class** (length dependencies, tagged
payloads) with the honest target story (storage repr + smart
constructors + boundary validators + correspondence theorem) and the
ingress note (dynamic validation stays). → 08 §16's guard + the Ty
lane. Provenance: review 2 §5.

**D21. Spec sanity is a gate row.** Feasibility obligations (admissible
initial state, valid inputs, assumptions permit an environment, the
generator reaches its cases); emptiness declared, never mistaken for
success. → 04 §5. Provenance: review 2 §6.

**D22. Compatibility from contracts, directionally.** Producer/consumer/
wire roles; a stronger precondition breaks callers, a stronger
postcondition helps them; structural diffs generate candidate
compatibility proofs, not verdicts. → 02 §-compatibility + the breaking
gate's v2. Provenance: review 2 §7.

**D23. Certificates connect the actual objects.** A cited theorem must
quantify over the actual source/target/observation — name-pins are
provenance, not proof-linkage. → 04 §8's acceptance shape. Provenance:
review 2 §8.

**D24. Semantic profiles as phantom metadata** (units/overflow/
rounding/collation) — explicitly not money types (the scope lock
stands); the immediate value: integer overflow semantics (wrap vs trap)
becomes explicit. → 08's catalog. Provenance: review 2 §12 + the
scope-lock reconciliation.

**D25. The migration-composition law** (upcast v1→v2 ∘ v2→v3 agrees
with v1→v3) lands now; the categorical apparatus (adjunctions) parks
behind its trigger. → 08 §19. Provenance: review 2 §13.

**D26. The semantic-diff witness verdict.** A behavior change carries
the distinguishing input (searched, checked against both, shrunk) or
the proved observational equivalence. → 08 §27 + 09 §8. Provenance:
review 3 §4.

**D27. The coordination classifier** (invariant confluence): commuting
≠ merge-preserves-invariant; the classifier answers safe/partitioned/
coordination-required/unknown with named remedies. → 08 §18 + 02 §8.
Provenance: review 3 §2.

**D28. Validity at the transaction boundary** + the command/delta/event
trichotomy (a command can fail; a net delta erases intermediate
history; an event records occurrence + causality). → 03 §7. The
event-sourcing lane's types corrected to hold the distinction.
Provenance: review 4 §7.

**D29. Constraints as incremental violation relations** — the commit
gate is a violation query's empty result; the incremental result proves
equal to full recomputation once at the circuit theory. The strongest
single composition in the set. → 03 §8. Provenance: review 4 §8.

**D30. Wires are triples** (format × delivery × protocol); FFI is the
synchronous in-process wire; the connector library is the wiring
discipline over ports. → 08 §23-24. Provenance: the session's design
discussion + review 4's transport discipline.

## From the session's execution (the process decisions that held)

**D31. Delete-or-graduate:** infrastructure without a consumer is a
finding; a landing without its consumer order paired is a protocol
violation. Provenance: the review-2026-09-16 audit's standing list.

**D32. The correspondence preference** (the ladder's location rule):
true Iso > PartialIso into the canonical image > decidable check > gate
— a re-derived law where an iso exists is a finding. Now subsumed by
D1's grading (the graded library names WHICH correspondence) — the
preference order survives as the grading's own ranking.

**D33. Docs are executable:** every claim in notes/ checks against the
tree (the docs-check gate); a doctrine doc naming a wrong symbol is the
failure mode this project kept paying for.

**D34. Agents report premise corrections, then proceed on the spirit.**
Every work order's premises are verified first; a wrong premise is a
finding, not a blocker.

**D35. One writer per artifact; byte-tie is law; never hand-edit a
generated file; the gates are the executable doctrine.** (The oldest
rules — they survived every review.)

## From the surface discussion (2026-09-24, the owner's direction)

**D36. The frontend inherits idioms, never invents them.** The surface
vocabulary is the two inherited idioms — the snapshot idiom (SQL:
tables/keys/refs/rules) and the stream idiom (git/dbsp: journals/deltas/
views) — proven CONJUGATE by the fusion bridges (journal = D∘run). The
categorical machinery (folds/carriers/engines) is implementation, never
exposed. → 16-surface.md §§1-3.

**D37. The evidence entourage picks the weakest SUFFICIENT evidence.**
Construction-guaranteed facts get NO generated proof (the type is the
evidence); decidable facts get kernel proofs, never sweeps; unbounded
facts get sweeps + controls + validity-preserving shrinkers. The tier is
computed from the evidence kind; redundant generated proofs are lint
findings. → 16 §3.

**D38. The semantic-profiles lane is ACTIVATED** (was WATCH) — the
game-engine product forces the float question: `Float Deterministic`
(fixed-point, codec-legal) vs `Float Fast` (honest forfeits) as phantom
indices; Money/units/time profiles erase at runtime. → 16 §4.5.

**D39. The model's strengthening program**: carrier-as-graph unification
→ the coalgebraic half (finality — TraceModel's missing deep theorems)
→ the hyperproperty substrate (self-composition + the security
observer) → the Descr functorial deepening → typed contexts (with the
first language). → 16 §4.

**D40. The game-engine activation**: ECS = the data plane (change
detection IS incremental maintenance; parallel scheduling IS the
disjointness theorem); rollback = the fusion bridges; saves =
migrations; assets = the provenance ledger; budgets = the cost lane.
No vertical features; each reading is rows + instances. → 16 §6.

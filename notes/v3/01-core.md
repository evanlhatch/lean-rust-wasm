# 01 — The core

The minimal generating set. Everything else in this doctrine is an
instance of something here. A proposed addition that names no slot here
is a design failure (07's recipes are the slots' working surface).

## 1. The three roots

| Root | Question | The wall (evidence, not a theorem) |
|---|---|---|
| **Universe** | what is | finite data; initial-algebra side: closed codes + total denotation |
| **Change** | what changes | the capability ladder — see §2; states don't invert; NOT behavior |
| **TraceModel** | what behaves | events + causal order + CONFLICT (alternative executions); NOT data |

The roof over them: the algebra/coalgebra duality. Universe = the
initial-algebra side (data, folds). TraceModel = the final-coalgebra
side (behavior: a machine's trace structure is its coalgebraic
semantics; bisimulation is its equality). Change = the symmetry layer
between them. A new shape is data, behavior, or a crossing — the answer
names what it inherits.

**Irreducibility is engineering evidence, not a formal ceiling.** The
walls that keep them apart today: Change needs symmetry that states
don't have (no negative state); a single event poset cannot express
conflict (so TraceModel ≠ a plain DAG — see the behavior discipline
below); Universe's closed codes can't express behavior. If a better
model exists, the roots extend deliberately — record it in decisions.md.

**Temporality is not a root.** Time IS the TraceModel's order: logical
time = the causal order (Lamport); a global clock = the degenerate
total-order case; rate/duration = metric data over the order (Universe
content: Tick/Rate values). **Resources are not a root:** fuel/budgets/
size = monotone consumption, a Change instance (monus). **Provenance is
not a root:** the artifact ledger is an event log; the causal trail is
the TraceModel of the build. **The named fourth-root trigger:**
probability (randomized semantics) — only that earns one, only when a
product lane needs it.

## 2. Change, as a capability ladder

Change is NOT assumed reversible. The honest hierarchy — an instance
declares how far up it sits:

```
applicable change          (a patch that applies)
→ composable               (patents compose: Δ₁;Δ₂)
→ with identity            (the no-op)
→ reversible               (an inverse exists — requires the delta to
                            retain old information)
→ commuting                (disjoint changes commute)
→ additive / group         (the Z-set instance: dbsp)
```

Evidence the hierarchy is real: `set name := "Alice"` forgets the old
name unless the delta stores it; an email can't be un-sent (compensation
≠ undo); removing a schema field forgets; saturating subtraction loses
information; event replay works for non-commutative updates.

Derive inverses only where lawful (the derivation machinery knows which
field-changes retain old information). Two laws every Change instance
wants, stated correctly:

```
migration (applyOld s e) = applyNew (migration s) (upcast e)
  -- the LOCAL equation; replay preservation follows ONCE by induction

f (apply x dx) = apply (f x) (deriveChange f x dx)
  -- the incremental derivative depends on the OLD INPUT x, not Δ alone
```

## 3. The TraceModel, stated honestly

The foundational behavior object: events + causal order + CONFLICT +
occurrence identity (an event is not its label — the same label twice is
two occurrences).

**The transition semantics is authoritative.** A machine's behavior is
the SET of its executions — with choice (pending → approved | rejected
is conflict, not order), repetition, and divergence. The derived VIEWS
(shared theory through explicit denotation laws):

- the sequential trace set (refinement = inclusion, parameterized by
  the observation — 04);
- per-execution causal posets (the DAG of happens-before);
- observations (what a chosen observer sees);
- equivalences (bisimulation is stronger than trace equivalence —
  pick per claim; stutter-invariance needs observation-hiding).

The corrections that cost real review rounds — do not re-pay:

- Finite states do NOT imply finite executions (loops) — fairness is an
  environment ASSUMPTION, never derived from the transition table.
- Partial-order reduction preserves the NAMED property classes only
  (end-state predicates, deadlock-freedom) under EXPLICIT premises
  (enabledness preservation, visibility, property-compatibility) —
  commuting final states do not preserve intermediate properties
  (the x≥y counterexample: two commuting writes, the violation is
  mid-execution of one order).
- Bounded exploration returns three honest answers: PROVED (a
  certificate) / REFUTED (a counterexample trace) / UNKNOWN (the
  reason). Budget exhaustion is UNKNOWN — never silently a verdict.

## 4. The ONE carrier: graded correspondences

Every crossing between two presentations declares its strongest honest
law from ONE library — never pretending lossless:

| Crossing kind | The law | Example |
|---|---|---|
| Isomorphism | both round trips | row ↔ native record |
| Retraction/embedding | one round trip | checked universe ⊂ raw items |
| Codec | decode∘encode = id; the accepted-byte policy explicit | the wire |
| Normalization | sound + idempotent; completeness when available | canonical forms |
| Refinement/simulation | behavior preservation in the named direction | impl ≤ spec |
| Abstraction | sound approximation (over, never exact) | the analysis lane |

The library owns: identity, composition, product/sum lifting, transport,
the commuting-diagram discipline. **Statements are one instance**: a
checked fact is the correspondence between the decidable shadow and the
proposition — `{a // check a = true} → {a // P a}` via soundness; an Iso
when completeness holds, an honest one-ended map when it doesn't.
**Obligations** = a correspondence instance + tier + evidence record
(the discharge substrate — the tier set is closed, the evidence kinds
are closed, a row whose evidence's tier mismatches fails construction).

## 5. The spine (one)

**Registry → Interpretation → artifact.** Accumulate (the compile-time
event log: append-only extensions, replay = the snapshot) then read
(a fold). Two fusions that make this ONE concept:

- **An emitter is an interpretation** — a reading of the universe into
  the target's grammar. Its law field, byte-tie, checked-universe input
  are the interpretation's correspondence, cited.
- **The generative engine is an emitter into the Lean-syntax target.**
  `family!`/`deriving` handlers are `spec → List (decl + law)` — the
  same shape. They inherit the emitter discipline: generated decls carry
  laws, the generated surface is byte-tie-stable, `@[derived]` is the
  artifact header.

## 6. The relational engine (the proof-reuse mechanism)

The center of mass for proofs: **bundled interpretations + an explicit
relation family + per-primitive preservation + ONE generic theorem per
interpretation pair.**

```
per-primitive:  R (eval₁ p) (eval₂ p)        -- proved once per primitive
composition:    R-preserving f, g ⟹ R-preserving (f ∘ g)
                ─────────────────────────────
whole program:  R ⟦e⟧₁ ⟦e⟧₂                  -- by structural induction, ONCE
```

The interpretation pairs this serves: spec ↔ generated impl (semantic
agreement), unoptimized ↔ optimized (observational equivalence), abstract
↔ concrete (sound approximation), old ↔ new schema (migration), full ↔
incremental (maintenance), concrete ↔ instrumented (same result after
hiding instrumentation).

Discipline: relations compose (R∘S) — the multi-stage pipeline's
end-to-end preservation is one composite relation + transitivity;
reflexivity is the determinism theorem for free; the stateful lanes need
Kripke-style evolving relations (the relation grows with the state —
a named extension, never a hidden assumption). Loops/recursion/effects
need their own relational rules — parametricity alone doesn't supply them.

## 7. The discipline layer (summary — the details are 04/06)

The ladder: unrepresentable > no-instance > defaulted decide > generated
> disclosed native > hand theorem (the LAST resort, and a small generic
hand lemma is OFTEN the best foundation — the ladder ranks the LOCATION
of correctness, not the count of handwritten proofs). Plus: the gates
machine (09), the diagnostics discipline (05 §errors), the extensibility
acceptance test (07).

## The acceptance test for this file

A new shape asks five questions: which root (data/behavior/crossing —
or the named degenerate cases), which carrier grade, which spine reading,
which ladder rung, which gate row. If the answers are all instances, the
shape lands by declaration. If not, the core extends deliberately — in
this file, never in a code comment.

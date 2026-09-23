# 02 — The data plane: relational semantics as the center

For tabular applications, the center is typed relational semantics —
not records. Records are row TYPES; tables are collections of rows;
functions are functional relations; commands are state-transition
relations; constraints are propositions over relations.

**The crucial separation:** relational semantics specifies meaning; the
executable query algebra implements the supported fragment. An arbitrary
logical relation does not automatically become an efficient query or a
generated function.

## 1. The schema describes valid worlds

A record schema names fields; a relational schema states the whole
world's validity:

```
Order: customerId : CustomerId → existing Customer
       orderId uniquely determines the order
       total = sum of line amounts
       shipped ⇒ successful payment exists
```

The primary object:

```lean
structure ValidDatabase (S : Schema) where
  db   : DatabaseInstance S
  ok   : ConstraintsHold S db      -- the proof field
```

Operations preserve valid worlds: `ValidDatabase S → Command →
Result (ValidDatabase S)`. Runtime storage carries no proofs — a
verified operation plus validated ingress maintains the invariant; an
optimized implementation connects through a representation relation
(04's graded carrier).

**The payoff:** one constraint, many derived uses — smart constructors,
migration obligations, query optimization, cardinality inference,
command preconditions, counterexample generation, diagnostics,
coordination requirements. The constraint is the shared authority; the
capabilities derive.

## 2. Relational logic as the shared language

The useful fragment needs little:

| Logic | Tabular reading |
|---|---|
| conjunction | join |
| existential quantification | projection |
| disjunction | union (set semantics) |
| equality | selection / equijoin |
| predicate substitution | query composition |

The same expression serves as executable query, logical proposition,
incremental maintenance input, provenance carrier, optimization target,
and explanation source. Constraints are statements about query results:
`MissingCustomerReferences = empty`. A diagnostic carries the violating
rows — never a bespoke per-checker payload.

Honest boundary: do NOT force all constraints into positive queries.
Negation, aggregation, universal conditions, ordering each need explicit
additional semantics with named laws.

## 3. Functional dependencies are determinacy theorems

Keys are not metadata — they are determinacy theorems:
`OrderId → CustomerId, Status, Total` means matching OrderId determines
the rest. They drive API SHAPE:

```
ordinary query:      OrderId → List Order
key-backed query:    OrderId → Option Order     -- at most one row
key + existence:     OrderId → Order            -- the precondition in the type
```

Join types distinguish one-to-one / many-to-one / one-to-many /
many-to-many — derived guarantees about output multiplicity, not
documentation. The inference is conservative: failure to prove
uniqueness yields a collection result, never invented uniqueness.

## 4. One relation semantics, a family of weights

```text
Relation K Row = finitely-supported mapping Row → K
```

| Weight K | Meaning |
|---|---|
| Bool | membership (sets) |
| Nat | multiplicity (bags) |
| ℤ | signed multiplicity (deltas — the dbsp instance) |
| provenance polynomial | which source rows contributed, and how |

Positive relational algebra: union adds weights, join multiplies,
projection sums over preimages. **The one theorem:**

```
h (evaluate Q input) = evaluate Q (h input)
  -- for h a weight-map preserving the required operations
```

Provenance, counts, membership, and deltas connect through the generic
theorem, not per-query proofs. Limits (named, honest): deduplication is
nonlinear; negation needs more than a semiring; ordered operations need
explicit order; general aggregation needs its own contracts; negative
multiplicities are for changes, not materialized business tables.

## 5. Commands are relations; three realization paths

A command specifies a relation, not an implementation:

```
Reserve before request after ⟵
  requested stock exists; reservation created; available inventory
  decreases correctly; unrelated inventory unchanged; references valid
```

Three paths behind ONE correctness interface ("the implementation's
result satisfies the command relation"):

1. **Derive** — when the relation structurally determines the output.
2. **Check** — the programmer supplies the function; prove its graph
   satisfies the relation.
3. **Search** — a solver proposes; a verified checker validates (the
   certificate pattern, 04 §3).

The supporting law family: existence (the operation can succeed under
the precondition), uniqueness (the output is determined), preservation
(a valid world maps to a valid world), frame (unrelated state
unchanged). Composition is relational: `(R ; S)(b, a) := ∃ mid, R b mid
∧ S mid ∧ S mid a` — contract propagation, refinement, transactions,
and migration correctness all reuse it.

## 6. The optimizer is a proof engine

Constraints license rewrites (key + inclusion + projection ⇒ a join can
disappear under the right semantics). The optimizer interface returns:

```
optimized query + proof: every valid database gives equivalent results
```

An untrusted optimizer proposes the rewrite sequence; the kernel checks
it. The SAME rewrite library improves runtime plans and shrinks proof
obligations. The optimizer itself need not be globally proved correct —
checked output is the narrow honest path.

## 7. Writable views, where justified

The bidirectional problem: edit the view → which base changes follow?
Relational lenses: view + update policy + laws (read-after-write returns
the requested view; an unchanged view preserves the source). Derive the
writable fragment from keys/dependencies; expose ambiguity precisely
(an aggregate edit with many base preimages refuses or demands a policy).

Combine with the delta discipline: a proposed view delta ΔV maps to a
base delta ΔB; the checker verifies `query (B + ΔB) = V + ΔV` + base
constraints + the chosen policy. Forward incremental maintenance and
checked backward updates are the same machinery.

## 8. Coordination requirements from invariants (invariant confluence)

The question: can independently-valid updates merge without violating
the invariant? **Commuting operations ≠ merged state preserves the
invariant** (two commuting withdrawals can jointly overdraw). The
classifier answers per operation:

```
safe under merge | safe under declared ownership partition
| requires coordination (name the remedy: serialize / partition /
  escrow / strengthen-precondition / change-conflict-policy)
| unknown (the proof obligation remains open — honest)
```

The CALM connection: monotone queries coordinate-free under the model's
assumptions; negation ("no payment exists") requires knowing the input
is complete — that knowledge costs coordination, a watermark, a closed
epoch, or a declared assumption. Never a blanket distributed-correctness
claim: delivery, failures, durability, ordering stay explicit.

## 9. Datalog as the executable fragment (not a programming language)

Small, declarative, recursive, with a direct least-fixpoint semantics —
for relational closure (eligibility, reachability, dependency,
authorization, pending obligations). Lean foundation: typed predicates,
safe/range-restricted rules, the monotone consequence operator, LFP
semantics, evaluation correctness, incremental correctness for the
supported fragment. Finite-domain Boolean facts give finite-height
iteration. **The trap:** finite keys alone don't terminate recursive
bag weights — stratified negation is deliberate; arithmetic generation,
aggregation, recursive weights, external effects are separate extensions
with named laws. Lean computes; Datalog closes relations; typed pure
primitives connect them.

## 10. Indexes, caches, subscriptions = materialized queries

One semantic equation for all of them: `storedDerived = query base` —
maintained incrementally by the same law. Representation relations
connect the maintained result to Rust storage (a B-tree range scan
represents a relational range query; a hash lookup an equality
selection). This deletes separate hand-written invalidation systems.
Boundary: external inputs (time, config, permissions, rates) are explicit
query inputs, or the dependency story is incomplete.

## 11. Explanations are query semantics

- why present → the supporting derivations;
- why absent → the blocking conditions under declared completeness
  assumptions;
- what would change the result → sensitivity analysis;
- which change repairs the constraint → a candidate repair checked
  against the specification.

A violation renders as: the failing fact + the completeness assumption
+ the required witness. Never a generic invariant failure.

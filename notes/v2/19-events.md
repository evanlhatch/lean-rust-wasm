# 19 — The TraceModel: traces as partial orders (the fundamental model)

THE foundational model object. A TRACE is a partial order on events
(happens-before); a linear log is ONE linear extension. Two events with no
order between them may fire in either order — and "in either order, same
effect" IS our proven commutation laws. So causality, commutativity,
model-checking, and debugging are one concept, and the tree's existing
theorems (batch_order_irrelevant, applySeq_perm,
DeltaSystem.disjoint_commutes, the update2-compat law) are the independence
axioms.

## Denotation (the inheritance mechanism)

Executable shapes (machines, circuits, cascades, stage schedules, updates,
type universes, provenance ledgers) DENOTE into the TraceModel: a definition
"the events/runs of X, causally ordered, with independence" that IS the
model instance for X. Execution stays concrete (step functions); verification
— trace sets (linear extensions), POR soundness, vector clocks, fairness,
refinement, causal cones, slicing — is the theory of the model, inherited by
every denotation. A machine's BEHAVIOR is the labeled poset; the state graph
is a projection (equivalence classes of runs).

## 0. The definitions (concrete)

```lean
-- an event is a labeled step (from a machine/lane declaration)
structure Event (m : Machine) where
  label : m.Label
  -- independence: the license to swap adjacent events (the POR axiom).
  -- DERIVED from the effect rows (12 §1): disjoint write sets + no
  -- read/write interference — the update2-compat shape, machine-generalized.
  writes : Finset (Effect.location)
  reads  : Finset (Effect.location)

def Independent (e₁ e₂ : Event m) : Prop :=
  Disjoint e₁.writes e₂.writes ∧
  e₁.reads ∩ e₂.writes = ∅ ∧ e₂.reads ∩ e₁.writes = ∅

-- happens-before: the partial order (Lamport), built from program order +
-- message/causal order (a boundary send precedes the receiver's receive).
inductive Before (e₁ e₂ : Event m) : Prop where
  | program  : e₁ comes before e₂ in the run
  | sendRecv : boundary send of e₁ causally precedes the receiver's event
  -- transitive closure lifts it; antisymmetry = the poset law

-- Mazurkiewicz equivalence: same poset, different linear extensions.
def SameTrace (r₁ r₂ : List (Event m)) : Prop :=
  -- the posets induced by r₁ and r₂ coincide (as arrive-orders after
  -- commuting adjacent independent pairs)

-- the trace SET of a machine = the set of linear extensions of the poset
def TraceSet (m : Machine) : Set (List m.Label)  -- every extension of the poset
```

## 1. The connection to what we PROVED

- `applySeq_perm` / `batch_order_irrelevant` / `DeltaSystem.disjoint_commutes`
  are Mazurkiewicz independence laws for their worlds: commuting adjacent
  independent steps reaches the same state.
- **THE POR THEOREM (proved ONCE, in the foundation):** with `Independent`
  derived, firing independent adjacent events in either order reaches the
  same state — the commutation law generalizing the list-row versions to
  machine events; and therefore exploring ONE representative per
  commutation-class covers the whole class (POR soundness).
- Trace-set (18 §1) = the set of linear extensions; `refines ⊆` reasoned on
  the poset; machine equivalence ⇔ equal posets (Mazurkiewicz trace
  equivalence — strictly finer than begin-order, exactly commute-exact).

## 2. Causal debugging as the DAG

- The inspector (13 §2) and the causal trail (12 §6) render the HASSE diagram
  of the poset, not a linear log: one event's earliest causes are its
  happen-before ancestors; one event's consequences are its upward cone.
- **Vector clocks:** a per-event timestamp derived from the poset
  (increment-on-event, max-merge on send/receive) makes "e₁ happens-before
  e₂" O(1) — the data structure the inspector + the causal trail use.
- **What-if = the cone:** mutating an event recomputes exactly its upward
  causal cone (slicing) — the inspector's what-if becomes "splice a
  modified event; replay the cone."

## 3. Model-checking as a byproduct (partial-order reduction)

- The model-check battery (12 §3) explores REPRESENTATIVES per
  commutation-class, not all sequences: POR soundness (18 §1, proved once)
  is cited, so the reduced board covers the full class.
- A cast of failure: a counterexample is returned as (class representative +
  the causal graph to the failing state) — the report is the poset, and
  fixing means finding the minimal failing cone (slicing + shrinking, 13 §4
  and TestKit.Shrink — the MUS/MUC of the event model).

## 4. Inheritance (the seventh product, the "by default" story)

A `machine!`/process declaration's DENOTATION (its events, independence,
poset) is a DEFINITION over the declaration + its effect rows, and the
verification objects are THEOREMS over that denotation — inferred, not
generated (the inference law, 02 §3a):

1. event set = a fold of the labels/effects,
2. `Independent` = a definition from the effect rows + a `by decide`
   certificate (the only per-declaration residue),
3. the poset = the denotation of a run (program order + boundary causality),
4. trace-equivalence/trace set = definitions (image of the steps); the
   POR-soundness and refinement theorems are proved ONCE in the foundation,
5. the POR-sound battery = a DECIDED OBLIGATION over the inferred
   independence (a check, not a generated file),
6. vector clocks + Hasse = derived redundant representations (definitions
   with correctness lemmas) for debugging ergonomics only.

Every verification object is proof-over-declaration; nothing is emitted
unless it is product surface (emitters) or a new embedding (the portable
verifier reuses the one checker). This is the "genuine research-grade
capability without dev overhead": the verification stack is the theory of
the declaration, not artifacts of a generator.

## 5. Canon additions folded (the reading list, mapped)

- Mazurkiewicz traces — the mathematical name for commute-exact trace
  equivalence (this doc).
- Lamport happens-before + vector clocks — the poset + its O(1) order test.
- Partial-order reduction — the model-checking optimizer we now license.
- Program slicing — the what-if cone (13 §2).
- MUS (minimal unsatisfiable cores) — 13 §4's minimal failing sub-universe,
  named for the checker lanes.
- Why-/where-provenance — the DB term for the causal trail (15).
- CRDT note: our Replicas row IS causally-ordered replication —
  the same partial-order model; delta-CRDT literature is the convergence
  law (Replicas.group-law) seen from the event side.
- Event-B refinement — 18 §1's refinement maps (spec↔impl coupling).

## 6. Acceptance (mechanical)

1. Two machines whose events commute pairwise have the SAME poset — the
   trace-equivalence + POR battery green (and `refines` both ways).
2. The inspector renders the Hasse diagram of a committed journal; a what-if
   splice changes exactly its upward cone (the sliced replay).
3. A livelock/deadlock shows as a fair-cycle in the poset battery with the
   reduced representative + the graph.
4. The model-check battery's certificate cites the POR-soundness theorem —
   a battery that samples without the citation is a review finding.
5. A new machine lands all seven products as proofs-over-declaration: no
   hand-written causality/POR/vector-clock proofs, and NO generated
   verification artifacts (the independence certificate + `by decide`
   obligation is the only residue; nothing is emitted).

## Guard rules

- POR/independence theorems are foundation-level, cited — never re-proved
  per machine (an independence law is decided per machine or generated, and
  the POR soundness lives in the foundation once).
- The poset is finite for enumerated machines (the decid field); infinite
  machines stay theorem territory (18 §1 guard).
- Causality via boundary sends is DATA (the send/receive edges from
  sessions/AG), never free-form.

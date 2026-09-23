# 20 — The roots: Universe · Change · TraceModel, and two carriers

The layered model that makes correctness inherit. dbsp and Machines are
INSTANCE LIBRARIES, not the foundation — the roots are three orthogonal
semantics (what is / what changes / what behaves) plus two carriers
(provability, crossing). Build on the roots; declare instances; the proof
inherits.

## 1. The layers

```
THEORY ROOTS         (abstract semantics; prove ONCE)
  Universe  : closed codes + total El               what is
  Change    : patch/valid/invert/diff + DeltaSystem what changes, reversibly
  TraceModel: events + independence + causal order  what behaves
CARRIERS
  Statement     : checked facts with mounts         what's provable
  Correspondence: Iso/PartialIso w/ law in the type what crosses
ENGINEERING KERNELS (concrete languages)
  Ty (is the Universe) · Wat (op semantics = steps → TraceModel)
  Ckt (dataflow semantics → TraceModel + group via Change)
INSTANCE LIBRARIES (declared; inherit)
  Machines (a generator syntax; semantics = the labeled poset)
  dbsp (the group instance of Change + stream theory: D/I, incrementalize)
  event sourcing · migrations · rewind · replication · model checking ·
  refinement · provenance · the data plane (13/18/19) — all instances
```

## 2. Why not "dbsp as foundation"

- The delta root is `Change` (patch/valid/invert/diff) + `DeltaSystem`
  (static write-disjoint commutes) — more general than the abelian group.
- Keyed updates are positional-replacement; machines aren't groups;
  migrations are morphisms, not group elements. The group is ONE instance.
- dbsp's contribution (D/I, incrementalize, journals-as-D) is the group/
  stream theory OVER the root — the root earns it; dbsp inherits.

## 3. Why machines are an application of TraceModel

- A machine's execution unfolds a labeled event poset; the state graph is a
  projection (equivalence classes of runs). Causality, POR, fairness,
  refinement, counterexamples are TraceModel theory on the DENOTATION.
- Machines stay the authoring syntax (guards/actions/batteries); semantics
  lives at the root, so bisimulation/refinement/liveness/model-checking are
  instances of the once-proved theory, not per-machine proofs (19).

## 4. The inheritance-of-provability table

| Declare… | …an instance of | Inherit (proved once, cited) |
|---|---|---|
| a `Change` | Change/Difference/ChangeInversion/Noc | rollback (`correct_invert`), journal rewind, what-if, migration preservation (13 §1) |
| write-disjoint batches | DeltaSystem | order-freedom (`applySeq_perm`), convergence-by-commutation |
| a group diagonal | dbsp's additive Change | D/I inverse (worlds↔journals), incrementalize |
| a behavior (machine/circuit/schedule) | TraceModel | trace sets, POR soundness, refinement-⊆, fairness/cycles, vector clocks |
| a crossing | Correspondence | the round-trip law, unparser drift-freedom, wire correctness |
| a legality | Statement | gates/lints/tests/obligations/duels/guests — one shape |

## 5. The instantiation checklist (what "adding a shape" is)

1. Name WHICH root(s) the shape's semantics is an instance of (Universe/
   Change/TraceModel; the carriers when legality/crossing apply).
2. Write the INSTANTIATION: the definition (the denotation to the root's
   vocabulary) + the certificate (by decide / generated / decided).
3. CITE the root theorems the shape inherits — downstream proofs are
   citations of root theorems, never re-derivations.
4. If a shape cannot instantiate a root, that is a FOUNDING decision:
   the root extends (rare, additive) — record it in 20.
5. Verification of the shape = oracle/regression over inherited facts, not
   new proofs (the inference law, 02 §3a / R11).

## 6. The cognitive-overhead shield

A new shape is a DECLARATION that IS an instance: the theory arrives with
it (root theorems are cited, never re-proved); downstream tests become
regression over inherited facts; the dev never thinks about the proof —
"what is / what changes / what behaves / what's provable / what crosses"
are the only five questions a shape asks, and the answers are instances.

## 7. Acceptance

- A new record/op/machine lands as an instance of ≥1 root, with the
  certificate and the cited inheritance; grep: no re-derived root theorem
  in the new shape.
- Two unrelated shapes with a shared root share the shared theory (a
  keyed-update batch and a replica stream both cite the same commutation
  lesson, from their DeltaSystem/Change instances).
- The layered model is the docs' spine: roots (01-02, 16-20), kernels
  (02), instances (12-15, 17-19), sequencing (11) — no layer re-invents
  a higher layer's theory.

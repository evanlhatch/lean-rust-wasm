/-
# Circuit.Compile — the query fragment's circuit compilation + the agreement

Owned by: the Circuit agent (the mandate tree, `circuit/`).

The query-lane connection (the honest minimal): the query fragment's
operators → the circuit's nodes, with the agreement theorem — the
compiled circuit's whole-input denotation IS the query's evaluation.

- `compile` — the substrate's query grammar (`ZSet.Query`, the
  one-row-type fragment of ZSet.Relation) → the circuit. The grammar
  and the circuit are the SAME tree, read twice: union → the union
  node, join → the join node (the cross term rides `Ckt.step`),
  project/filter → the `oProject`/`oFilter` templates.
- `compile_ok` — **THE COMPILATION'S AGREEMENT**:
  `(compile q).denote m = ZSet.evaluate q m`, one structural induction.
  The delta face needs NO second theorem: `Ckt.incrementalize_ok`
  composes with it, so every compiled query is maintained incrementally,
  for free.

THE NAMED BOUNDARY (reported, not hidden): the query LANE's typed
fragment (`Query.Q` — the computed result schemas, the join's appended
`fs ++ gs` carrier, the projection's `c.fields` schema) does NOT
compile at this seed. Two attempts, both defeated:

1. the fixed-index compilation (`Q fs fs → Option (Ckt (RowVals fs))`)
   DEFINES fine (the equation compiler unifies the data indices), but
   its agreement theorem cannot use `induction` — `Q`'s recursor
   generalizes the second index, and the fixed-index motive does not
   typecheck;
2. the general-index compilation mistypes the nodes: the single-typed
   circuit carries ONE row type, while a select-tree's top schema
   (`gs`) differs from its base schema (`fs`) — the subtree's output
   rows and the node's predicate rows disagree unless `gs = fs`.

Both are the type-indexed circuit's follow-up (Circuit.Basic's header:
the dependent-match motive over `Type`-valued indices cannot carry the
per-node `CanonKey` instances at this seed). The INCREMENTAL discipline
— the delta evaluation, the cross term, the old-values parameters, THE
agreement theorem — is fully certified at the seed's shape.

The five questions (notes/v3/01-core.md):
- **Root**: the data plane's query fragment meets the derivative
  discipline (02 §4 + 03 §9): the query's evaluation is the circuit's
  whole-input denotation, so THE agreement theorem maintains every
  compiled query incrementally, for free.
- **Carrier grade**: none of its own — the fragment consumed read-only
  (ZSet.Relation's grammar + its `evaluate`).
- **Spine reading**: none — the Ckt lane's compilation face.
- **Ladder rung**: hand theorems of the structural-induction kind —
  the agreement, once.
- **Gate rows**: the axiom report + CircuitTests' pins (the compiled
  query's known-answer weights + the agreement exercise + the mandatory
  negative controls).

Core-only (imports ZSet + Circuit.Basic — the cone rule).
-/

import Circuit.Basic
import ZSet
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Circuit

open ZSet

variable {α : Type} [CanonKey α] [DecidableEq α]

/-! ## The fragment's compilation -/

/-- The fragment's operators → the circuit's nodes: the grammar and the
    circuit are the SAME tree, read twice. -/
def compile (q : ZSet.Query α) : Ckt α :=
  match q with
  | .idQ => .input
  | .union q1 q2 => .union (compile q1) (compile q2)
  | .join q1 q2 => .join (compile q1) (compile q2)
  | .project g q => .lift (.oProject g) (compile q)
  | .filter p q => .lift (.oFilter p) (compile q)

/-- **THE COMPILATION'S AGREEMENT**: the compiled circuit's whole-input
    denotation IS the query's evaluation. One structural induction; the
    delta face needs NO second theorem — `Ckt.incrementalize_ok`
    composes with it, so every compiled query is maintained
    incrementally, for free. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by CircuitTests.Axioms (#print axioms); THE compilation's agreement — the delta face composes with `Ckt.incrementalize_ok` (every compiled query maintained incrementally for free)"]
theorem compile_ok (q : ZSet.Query α) (m : ZSet α) :
    (compile q).denote m = ZSet.evaluate q m := by
  induction q with
  | idQ => rfl
  | union q1 q2 ih1 ih2 =>
      show addW ((compile q1).denote m) ((compile q2).denote m) = _
      rw [ih1, ih2, ZSet.evaluate]
  | join q1 q2 ih1 ih2 =>
      show joinW ((compile q1).denote m) ((compile q2).denote m) = _
      rw [ih1, ih2, ZSet.evaluate]
  | project g q ih =>
      show projectW g ((compile q).denote m) = _
      rw [ih, ZSet.evaluate]
  | filter p q ih =>
      show filterW p ((compile q).denote m) = _
      rw [ih, ZSet.evaluate]

end Circuit

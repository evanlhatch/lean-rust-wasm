/-
# Circuit.Basic — the incremental circuit template + THE agreement theorem

Owned by: the Circuit agent (the mandate tree, `circuit/`).

Mined from `legacy/lean/dbsp/Dbsp/Circuit.lean` (the flatlandc-
certification template: the parameterized `Ckt`/`Func`/`denoteF` shape +
`incrementalize_ok` + `recursive_opt_ok`) — PORTED FRESH over the landed
substrate: the streams + `AddCommGroup` machinery becomes the Z-set
layer (`ZSet.Weighted Int α`, the canonical-rep weighted relation), and
the delay/integral/feedback stream operators become the collection
operators the doctrine actually maintains (03-bidirectional §8-9): no
fixpoint, no clock — the honest minimal circuit is a TREE of operator
nodes over one base wire, whose incremental face computes the output
delta from the input delta plus the old integrated values.

What lands here:

- `OpF` / `denoteF` — the operator templates (the closed set the
  emitter wires) and their meaning over the weighted relations: filter
  restricts, project sums over preimages, distinct dedups, threshold
  gates (the latter two NONLINEAR — 02 §4's named limits).
- `Circuit.Ckt` — the circuit: nodes as typed operations over the
  weighted relations + the wire. All nodes sit over the ONE base row
  type `α` (the wire's type). NAMED FOLLOW-UP (the boundary, not a
  defect): the legacy's type-indexed `Ckt Func a b` (the join's product
  carrier, the projection's row-map) needs a dependent match motive
  `fun β _ => ZSet β` over `Type`-valued indices — which cannot carry
  the per-node `CanonKey` instances (the motive does not elaborate;
  probed against the v4.33.0 equation compiler). The type-indexed shape
  returns with its first consumer that needs it; the INCREMENTAL
  DISCIPLINE certified here is index-free.
- `Ckt.denote` — the whole-input evaluation (the circuit's semantics).
- `Ckt.step` — THE INCREMENTAL FACE: the same circuit evaluated on the
  delta. Linear operators step on the delta alone (`filterW_add`,
  `projectW_add`); the join's delta carries THE CROSS TERM (03 §9:
  `Δ(A⋈B) = ΔA⋈B + A⋈ΔB + ΔA⋈ΔB`); the nonlinear nodes carry the
  old-values discipline as PARAMETERS — `distinctStep`/`thresholdStep`
  read the old integrated input `i` by name, riding the landed
  `distinctW_add_ok`/`thresholdW_add_ok` laws.
- `Ckt.incrementalize_ok` — **THE THEOREM**: the incremental evaluation
  agrees with the full recomputation,
  `c.denote (b + d) = c.denote b + c.step b d` — full recomputation IS
  the maintained result, proved ONCE at the circuit theory (03 §8's
  composition), by structural induction over the circuit shape.
- `optOnce` / `Ckt.recursiveOpt` / `Ckt.recursive_opt_ok` — the mined
  rewrite pass: a bottom-up local-rewrite driver whose soundness is ONE
  induction (`optOnce_ok` is the per-rewrite premise; here the union
  re-association, denotation-preserving by `addW_assoc`).

Honest boundaries (named, not hidden): the tree shape carries no
feedback/delay (a fixpoint operator needs the stream layer — not landed
here); the complexity claim (change-proportional work) is the emitter's
obligation downstream — THIS file certifies AGREEMENT, not cost; the
nonlinear steps consume the old integrated state (the parameters `i` in
`distinctStep`/`thresholdStep`) — never inferred linear from Z-set
shapes (03 §9).

The five questions (notes/v3/01-core.md):
- **Root**: Change (01 §2) — the derivative discipline's circuit face
  (03 §8-9): the violation-relation maintainer's foundation.
- **Carrier grade**: the Z-set canonical-rep relation consumed, never
  re-carried; the circuit itself is pure structure (an inductive), its
  two readings (whole-input / delta) are functions.
- **Spine reading**: none — the Ckt lane's seed substrate.
- **Ladder rung**: hand theorems of the structural-induction kind —
  `incrementalize_ok` ONCE over the shape (the legacy's proof discipline).
- **Gate rows**: the axiom report + CircuitTests' pins (the worked
  two-operator agreement, the cross-term teeth, the old-values teeth,
  the mandatory negative controls).

Core-only (imports ZSet — the cone rule; no mathlib, no Batteries).
-/

import ZSet
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Circuit

open ZSet

/-! ## The operator templates + their meaning -/

/-- The operator templates: the closed set the emitter wires (the
    legacy `Func` parameter's honest-minimal instance — closed HERE).
    `oThreshold` carries its positive-domain proof field (1 ≤ k — the
    honest domain: a threshold at or below zero fires on absent rows,
    ZSet.Relation's named limit). -/
inductive OpF (β : Type) : Type where
  /-- Selection: keep the rows satisfying the predicate. -/
  | oFilter : (β → Bool) → OpF β
  /-- Projection: relabel rows along the row-map (sums over preimages). -/
  | oProject : (β → β) → OpF β
  /-- DISTINCT: deduplication (nonlinear — steps need the old values). -/
  | oDistinct : OpF β
  /-- THRESHOLD: weights at least `k` become 1 (nonlinear like distinct). -/
  | oThreshold : (k : Int) → 1 ≤ k → OpF β

/-- The templates' meaning over the weighted relations (the legacy
    `denoteF` — one function fixing what every node computes). -/
def denoteF [CanonKey β] [DecidableEq β] (o : OpF β) (m : ZSet β) : ZSet β :=
  match o with
  | .oFilter p => filterW p m
  | .oProject g => projectW g m
  | .oDistinct => distinctW m
  | .oThreshold k _ => thresholdW k m

/-! ## The nonlinear steps (the old-values discipline, as parameters) -/

/-- The DISTINCT delta: the old distinct state plus the transition term
    that READS the old integrated input `i` (ZSet.Relation's
    `distinctHAt` — the old-values rule, the parameter is load-bearing).
    Defined as the difference of the two distinct states; the law below
    pins it to the landed transition term exactly. -/
def distinctStep [CanonKey β] [DecidableEq β] (i d : ZSet β) : ZSet β :=
  addW (distinctW (addW i d)) (neg (distinctW i))

/-- The distinct step's weight IS the landed transition term. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `opStep_law`'s distinct case (THE node law `Ckt.incrementalize_ok` rides) + pinned by CircuitTests.Axioms (#print axioms)"]
theorem distinctStep_ok [CanonKey β] [DecidableEq β] (i d : ZSet β) (a : β) :
    weightW (distinctStep i d) a = distinctHAt i d a := by
  rw [distinctStep, addW_ok]
  have hn : weightW (neg (distinctW i)) a = -weightW (distinctW i) a :=
    weight_neg (distinctW i) a
  rw [hn, distinctW_add_ok]
  simp only [wkindInt_add]
  omega

/-- The THRESHOLD delta — the same old-values shape. -/
def thresholdStep [CanonKey β] [DecidableEq β] (k : Int) (i d : ZSet β) : ZSet β :=
  addW (thresholdW k (addW i d)) (neg (thresholdW k i))

/-- The threshold step's weight IS the landed transition term. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `opStep_law`'s threshold case (THE node law `Ckt.incrementalize_ok` rides) + pinned by CircuitTests.Axioms (#print axioms)"]
theorem thresholdStep_ok [CanonKey β] [DecidableEq β] (k : Int) (hk : 1 ≤ k)
    (i d : ZSet β) (a : β) :
    weightW (thresholdStep k i d) a = thresholdHAt k i d a := by
  rw [thresholdStep, addW_ok]
  have hn : weightW (neg (thresholdW k i)) a = -weightW (thresholdW k i) a :=
    weight_neg (thresholdW k i) a
  rw [hn, thresholdW_add_ok k hk]
  simp only [wkindInt_add]
  omega

/-! ## The node-level incremental face -/

/-- The operator's delta step: the node's INCREMENTAL face (the delta
    in, the output delta out). The linear cases consume the delta
    ALONE; the nonlinear cases take the old integrated input `i` (the
    old-values parameters, load-bearing — see CircuitTests' teeth). -/
def opStep [CanonKey β] [DecidableEq β] (o : OpF β) (i d : ZSet β) : ZSet β :=
  match o with
  | .oFilter p => filterW p d
  | .oProject g => projectW g d
  | .oDistinct => distinctStep i d
  | .oThreshold k _ => thresholdStep k i d

/-- THE NODE LAW: `denoteF o (i + d) = denoteF o i + opStep o i d` —
    proved ONCE per template; this is what `Ckt.incrementalize_ok`
    consumes at every `lift` node. The linear cases are the landed
    homomorphism laws (the delta ALONE determines the step); the
    nonlinear cases route the old input `i` through the landed
    old-values laws. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `Ckt.incrementalize_ok` at every `lift` node (THE node law) + pinned by CircuitTests.Axioms (#print axioms)"]
theorem opStep_law [CanonKey β] [DecidableEq β] (o : OpF β) (i d : ZSet β) :
    denoteF o (addW i d) = addW (denoteF o i) (opStep o i d) := by
  cases o with
  | oFilter p => exact filterW_add p i d
  | oProject g => exact projectW_add g i d
  | oDistinct =>
      apply extW
      intro a
      show weightW (distinctW (addW i d)) a
        = weightW (addW (distinctW i) (distinctStep i d)) a
      rw [addW_ok, distinctStep_ok, distinctW_add_ok]
      rfl
  | oThreshold k hk =>
      apply extW
      intro a
      show weightW (thresholdW k (addW i d)) a
        = weightW (addW (thresholdW k i) (thresholdStep k i d)) a
      rw [addW_ok, thresholdStep_ok k hk, thresholdW_add_ok k hk]
      rfl

/-- The LINEAR operators' honesty pin: their steps ignore the old
    state entirely — `opStep o i d = opStep o j d` for any old `i j`.
    (The nonlinear operators deliberately do NOT satisfy this — the
    old-values parameter is load-bearing, pinned in CircuitTests.) -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by CircuitTests.Axioms (#print axioms); the linear operators' honesty pin — the old-values parameter is load-bearing only for the nonlinear ones (the old-values teeth's general statement)"]
theorem opStep_linear_oldFree [CanonKey β] [DecidableEq β] (p : β → Bool)
    (i j d : ZSet β) :
    opStep (.oFilter p) i d = opStep (.oFilter p) j d := rfl

/-! ## The circuit: nodes + the wire -/

/-- THE CIRCUIT TEMPLATE (the legacy `Ckt`, ported fresh over the
    weighted relations): a tree of operator nodes over ONE base wire.
    Every node reads and writes the wire's row type `α` (the named
    follow-up on the type-indexed generalization is in this file's
    header). -/
inductive Ckt (α : Type) [CanonKey α] [DecidableEq α] : Type where
  /-- The wire: the base relation itself. -/
  | input : Ckt α
  /-- An operator node over one subcircuit's output. -/
  | lift (o : OpF α) (c : Ckt α) : Ckt α
  /-- Two subcircuits' outputs UNION (weights add — linear). -/
  | union (c1 c2 : Ckt α) : Ckt α
  /-- Two subcircuits' outputs JOIN (weights multiply — the cross term). -/
  | join (c1 c2 : Ckt α) : Ckt α
  /-- A subcircuit's output relabeled along the row-map. -/
  | project (g : α → α) (c : Ckt α) : Ckt α

variable {α : Type} [CanonKey α] [DecidableEq α]

/-- The whole-input evaluation (the circuit's semantics): the circuit
    reads the base relation and computes its output relation. -/
def Ckt.denote (c : Ckt α) (b : ZSet α) : ZSet α :=
  match c with
  | .input => b
  | .lift o sub => denoteF o (sub.denote b)
  | .union s1 s2 => addW (s1.denote b) (s2.denote b)
  | .join s1 s2 => joinW (s1.denote b) (s2.denote b)
  | .project g sub => projectW g (sub.denote b)

/-- THE INCREMENTAL FACE: the same circuit evaluated on the delta —
    given the OLD base `b` and the delta `d`, the output delta. Linear
    nodes step on the delta alone; the join node carries THE CROSS TERM
    (03 §9); the nonlinear nodes consume the old integrated values of
    their subcircuits (the parameters `i` of `distinctStep`/
    `thresholdStep`, realized here as the subcircuits' old outputs). -/
def Ckt.step (c : Ckt α) (b : ZSet α) (d : ZSet α) : ZSet α :=
  match c with
  | .input => d
  | .lift o sub => opStep o (sub.denote b) (sub.step b d)
  | .union s1 s2 => addW (s1.step b d) (s2.step b d)
  | .join s1 s2 =>
      addW (joinW (s1.step b d) (s2.denote b))
        (addW (joinW (s1.denote b) (s2.step b d))
          (joinW (s1.step b d) (s2.step b d)))
  | .project g sub => projectW g (sub.step b d)

/-! ## THE AGREEMENT THEOREM (the mined `incrementalize_ok`) -/

/-- The Int-level distributivity identity (the join case's cross-term
    arithmetic; the four products are atoms for `omega`). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `joinW_cross` (the cross-term arithmetic — the four products as atoms for omega)"]
theorem int_cross (a b c d : Int) :
    (a + b) * (c + d) = a * c + (b * c + (a * d + b * d)) := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega

/-- The union shuffle (the union case's arithmetic at the Z-set level):
    the four summands re-associate freely (weights add). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `Ckt.incrementalize_ok`'s union case (the four summands re-associate)"]
theorem addW_shuffle (a b c e : ZSet α) :
    addW (addW a b) (addW c e) = addW (addW a c) (addW b e) := by
  apply extW
  intro x
  simp only [addW_ok, wkindInt_add]
  omega

/-- The join's cross-term law at the Z-set level (03 §9's
    `Δ(A⋈B) = ΔA⋈B + A⋈ΔB + ΔA⋈ΔB` read forward: joining two merged
    states is the four joins). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `Ckt.incrementalize_ok`'s join case (03 §9's cross-term law)"]
theorem joinW_cross (a1 d1 a2 d2 : ZSet α) :
    joinW (addW a1 d1) (addW a2 d2)
      = addW (joinW a1 a2)
          (addW (joinW d1 a2) (addW (joinW a1 d2) (joinW d1 d2))) := by
  apply extW
  intro x
  simp only [addW_ok, joinW_ok, wkindInt_add, wkindInt_mul]
  exact int_cross _ _ _ _

/-- **THE COMPILER CERTIFICATE** (the mined `incrementalize_ok`, at the
    collection setting): the incremental evaluation agrees with the full
    recomputation —

    `c.denote (b + d) = c.denote b + c.step b d`

    i.e. the maintained result (old output + the stepped delta) IS the
    recomputed result. Proved ONCE, by structural induction over the
    circuit shape: the linear nodes by the landed homomorphism laws,
    the join node by the cross-term law, the nonlinear nodes riding the
    landed old-values laws with the old input as a PARAMETER. This is
    03 §8's "the foundation proves the incremental result equals full
    recomputation — ONCE, at the circuit theory". -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by CircuitTests (full_eq_maintained) + CircuitTests.Axioms (#print axioms); THE compiler certificate — 03 §8's agreement, proved once at the circuit theory"]
theorem Ckt.incrementalize_ok (c : Ckt α) (b d : ZSet α) :
    c.denote (addW b d) = addW (c.denote b) (c.step b d) := by
  induction c with
  | input => rfl
  | lift o sub ih =>
      show denoteF o (sub.denote (addW b d))
        = addW (denoteF o (sub.denote b)) (opStep o (sub.denote b) (sub.step b d))
      rw [ih, opStep_law]
  | union s1 s2 ih1 ih2 =>
      show addW (s1.denote (addW b d)) (s2.denote (addW b d))
        = addW (addW (s1.denote b) (s2.denote b)) (addW (s1.step b d) (s2.step b d))
      rw [ih1, ih2,
        addW_shuffle (a := s1.denote b) (b := s1.step b d)
          (c := s2.denote b) (e := s2.step b d)]
  | join s1 s2 ih1 ih2 =>
      show joinW (s1.denote (addW b d)) (s2.denote (addW b d))
        = addW (joinW (s1.denote b) (s2.denote b))
            (addW (joinW (s1.step b d) (s2.denote b))
              (addW (joinW (s1.denote b) (s2.step b d))
                (joinW (s1.step b d) (s2.step b d))))
      rw [ih1, ih2,
        joinW_cross (a1 := s1.denote b) (d1 := s1.step b d)
          (a2 := s2.denote b) (d2 := s2.step b d)]
  | project g sub ih =>
      show projectW g (sub.denote (addW b d))
        = addW (projectW g (sub.denote b)) (projectW g (sub.step b d))
      rw [ih, projectW_add]

/-! ## The local rewrite pass (the mined `recursive_opt_ok`) -/

/-- One local rewrite: re-associate a left-nested union (denotation
    preserved by `addW_assoc`). The legacy `opt` parameter's
    honest-minimal instance — a closed function, not a parameter; the
    open-oracle shape returns with the first second rewrite. -/
def optOnce (c : Ckt α) : Option (Ckt α) :=
  match c with
  | .union (.union a b) e => some (.union a (.union b e))
  | _ => none

/-- The per-rewrite soundness: when `optOnce` fires, the denotation is
    preserved (the rewrite is LOCAL — it never inspects the input). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `Ckt.recursive_opt_ok`'s rewrite cases (the per-rewrite premise) + pinned by CircuitTests.Axioms (#print axioms)"]
theorem optOnce_ok (c c' : Ckt α) (h : optOnce c = some c') :
    c'.denote = c.denote := by
  cases c with
  | input => simp [optOnce] at h
  | lift o sub => simp [optOnce] at h
  | join s1 s2 => simp [optOnce] at h
  | project g sub => simp [optOnce] at h
  | union c1 c2 =>
      cases c1 with
      | input => simp [optOnce] at h
      | lift o sub => simp [optOnce] at h
      | join s1 s2 => simp [optOnce] at h
      | project g sub => simp [optOnce] at h
      | union a b =>
          simp only [optOnce, Option.some.injEq] at h
          subst h
          funext x
          exact (addW_assoc (a.denote x) (b.denote x) (c2.denote x)).symm

/-- Bottom-up optimization: rewrite each node where `optOnce` fires,
    keep the recursively-optimized children otherwise (the legacy
    `recursiveOpt`, mined shape-for-shape). -/
def Ckt.recursiveOpt (c : Ckt α) : Ckt α :=
  match c with
  | .input => .input
  | .lift o sub =>
      (optOnce (.lift o (recursiveOpt sub))).getD (.lift o (recursiveOpt sub))
  | .union s1 s2 =>
      (optOnce (.union (recursiveOpt s1) (recursiveOpt s2))).getD
        (.union (recursiveOpt s1) (recursiveOpt s2))
  | .join s1 s2 => .join (recursiveOpt s1) (recursiveOpt s2)
  | .project g sub => .project g (recursiveOpt sub)

/-- **THE REWRITE CERTIFICATE** (the mined `recursive_opt_ok`): the
    bottom-up pass preserves the denotation of EVERY circuit — local
    rewrites, certified globally by one induction. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by CircuitTests.Axioms (#print axioms); THE rewrite certificate — local rewrites certified globally by one induction (the rewrite suite's denotation pin)"]
theorem Ckt.recursive_opt_ok (c : Ckt α) : c.recursiveOpt.denote = c.denote := by
  induction c with
  | input => rfl
  | lift o sub ih =>
      show ((optOnce (Ckt.lift o (recursiveOpt sub))).getD _).denote = _
      cases h : optOnce (Ckt.lift o (recursiveOpt sub)) with
      | none =>
          rw [Option.getD_none]
          funext x
          show denoteF o ((recursiveOpt sub).denote x) = denoteF o (sub.denote x)
          rw [ih]
      | some c' =>
          rw [Option.getD_some, optOnce_ok _ _ h]
          funext x
          show denoteF o ((recursiveOpt sub).denote x) = denoteF o (sub.denote x)
          rw [ih]
  | union s1 s2 ih1 ih2 =>
      show ((optOnce (Ckt.union (recursiveOpt s1) (recursiveOpt s2))).getD _).denote = _
      cases h : optOnce (Ckt.union (recursiveOpt s1) (recursiveOpt s2)) with
      | none =>
          rw [Option.getD_none]
          funext x
          show addW ((recursiveOpt s1).denote x) ((recursiveOpt s2).denote x)
            = addW (s1.denote x) (s2.denote x)
          rw [ih1, ih2]
      | some c' =>
          rw [Option.getD_some, optOnce_ok _ _ h]
          funext x
          show addW ((recursiveOpt s1).denote x) ((recursiveOpt s2).denote x)
            = addW (s1.denote x) (s2.denote x)
          rw [ih1, ih2]
  | join s1 s2 ih1 ih2 =>
      funext x
      show joinW ((recursiveOpt s1).denote x) ((recursiveOpt s2).denote x)
        = joinW (s1.denote x) (s2.denote x)
      rw [ih1, ih2]
  | project g sub ih =>
      funext x
      show projectW g ((recursiveOpt sub).denote x) = projectW g (sub.denote x)
      rw [ih]

end Circuit

/-
# CircuitTests — the incremental discipline's pins, teeth, and controls

Positive pins + the MANDATORY negative controls (15-patterns #5); the
runner is TestingKit's (`mainOfSuites`). The fixture rows are `Nat`
(the canonical `CanonKey Nat` instance); every value-level pin is a
worked known-answer weight.

Suites:

1. `agree` — the worked two-operator circuit (a join of the base with
   its positive-filtered self): full recomputation vs the maintained
   result (old output + stepped delta) pinned weight-for-weight, with
   `Ckt.incrementalize_ok` as the general statement. The negative
   controls: the cross-term sabotage (the join's delta WITHOUT
   `ΔA⋈ΔB` gives 8 where the truth is 9 — caught) and the
   dropped-old-output sabotage (the step alone — caught).
2. `old-values` — the nonlinear node's discipline: the distinct
   circuit's full vs maintained agreement, the old-values parameter
   PROVED load-bearing (two different old states, same delta,
   different steps), the linear operator's old-free step pinned. The
   negative controls: the `distinctW d` sabotage (ignores the old
   state — caught) and the false linearity claim (caught).
3. `compile` — the query compilation's agreement exercised: the
   compiled two-operator query's known-answer weights + the agreement
   pinned through `compile_ok` + the delta face (the compiled query
   maintained incrementally = recomputed). The negative controls: the
   dropped-filter sabotage (a different query, different weights —
   caught) and the false disagreement (claims the delta face breaks —
   caught).
4. `rewrite` — the bottom-up pass: the reassociation fires (the shape
   changes) and the denotation is preserved (`recursive_opt_ok`).
   The negative controls: the claim that the pass changes the
   denotation (caught) and the claim that the pass is the identity on
   the rewritten shape (caught).

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the lane's theorems — the core-triple-only surface or the build
fails. Evidence, not architecture — the five-question block lives in
the modules under test.
-/

import Circuit
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import CircuitTests.Axioms

open Circuit TestingKit ZSet

/-! ## The fixture: the base, the delta, the two-operator circuit -/

/-- The base relation: rows 1, 2, 3 at weights 1, 2, −1. -/
def b0 : ZSet Nat := fromList [(1, 1), (2, 2), (3, -1)]

/-- The delta: +1 at row 2, +1 at row 3 (cancels), +2 at row 4. -/
def d0 : ZSet Nat := fromList [(2, 1), (3, 1), (4, 2)]

/-- The selection: keep the rows with key ≤ 2 (the predicate is over
    the ROWS, not the weights — 02 §4's selection reads the keys). -/
def pos : Nat → Bool := fun n => decide (n ≤ 2)

/-- THE WORKED CIRCUIT (two operators): the join of the base wire with
    its positive-filtered self. -/
def cTwo : Ckt Nat := .join .input (.lift (.oFilter pos) .input)

/-- The full recomputation on the merged state. -/
def fullTwo : ZSet Nat := cTwo.denote (addW b0 d0)

/-- The maintained result: the old output plus the stepped delta. -/
def maintainedTwo : ZSet Nat := addW (cTwo.denote b0) (cTwo.step b0 d0)

/-- THE AGREEMENT, at the fixture (the general theorem's instance). -/
theorem full_eq_maintained : fullTwo = maintainedTwo :=
  Ckt.incrementalize_ok cTwo b0 d0

/-- The cross-term sabotage: the join's delta WITHOUT `ΔA⋈ΔB` (03 §9's
    named cross term dropped). -/
def stepNoCross (b d : ZSet Nat) : ZSet Nat :=
  addW (joinW d (filterW pos b)) (joinW b (filterW pos d))

/-- The sabotaged maintained result. -/
def noCrossTwo : ZSet Nat := addW (cTwo.denote b0) (stepNoCross b0 d0)

/-- The dropped-old-output sabotage: the stepped delta alone, no old
    output — the second sabotage family. -/
def stepOnlyTwo : ZSet Nat := cTwo.step b0 d0

/-! ## Suite 1: the two-operator agreement -/

def specAgree : Spec := Spec.ofList "agree"
  (fun _ => do
    -- full recomputation = maintained result, as DATA
    assert (fullTwo == maintainedTwo) "full ≠ maintained (the theorem's face)"
    -- the known-answer weights: row 2 merged to 3, joined 3*3 = 9
    assert (weight fullTwo 2 = 9) s!"row 2: got {weight fullTwo 2}, want 9"
    assert (weight maintainedTwo 2 = 9) s!"maintained row 2: got {weight maintainedTwo 2}, want 9"
    -- row 1 untouched: 1*1 = 1
    assert (weight fullTwo 1 = 1) s!"row 1: got {weight fullTwo 1}, want 1"
    -- row 3 cancels: 0 * 0 = 0
    assert (weight fullTwo 3 = 0) s!"row 3: got {weight fullTwo 3}, want 0"
    -- row 4 arrives in the delta only: base 0, joined 0*2 = 0
    assert (weight fullTwo 4 = 0) s!"row 4: got {weight fullTwo 4}, want 0"
    -- the cross term is LOAD-BEARING: Δ ⋈ Δ' ≠ 0 at row 2
    assert (weight (joinW d0 (filterW pos d0)) 2 = 1)
      s!"cross term: got {weight (joinW d0 (filterW pos d0)) 2}, want 1")
  [ ("no-cross-sabotage", fun _ =>
      assert (noCrossTwo == fullTwo)
        "the no-cross delta must DISAGREE with the recomputation (it drops ΔA⋈ΔB)"),
    ("step-only-sabotage", fun _ =>
      assert (stepOnlyTwo == fullTwo)
        "the step alone must DISAGREE with the recomputation (it drops the old output)"),
    ("wrong-known-answer", fun _ =>
      assert (weight fullTwo 2 = 8)
        "the 8-claim must fail: the cross term makes row 2 weigh 9, not 8") ]
  1 42

/-! ## Suite 2: the nonlinear node's old-values discipline -/

/-- The distinct circuit (one nonlinear node over the wire). -/
def cDist : Ckt Nat := .lift .oDistinct .input

/-- Two old states + one shared delta: the old-values parameter's
    load-bearing fixture. -/
def i1 : ZSet Nat := fromList [(5, 2)]
def i2 : ZSet Nat := fromList [(5, 5)]
def dd : ZSet Nat := fromList [(5, -2)]

/-- The sabotage: the distinct step that ignores the old state (reads
    the delta alone — the discipline 03 §9 forbids). -/
def distinctStepSabotaged (_i d : ZSet Nat) : ZSet Nat := distinctW d

def specOldValues : Spec := Spec.ofList "old-values"
  (fun _ => do
    -- full recomputation = maintained (the theorem's face at the node)
    assert (cDist.denote (addW i1 dd) == addW (cDist.denote i1) (cDist.step i1 dd))
      "distinct: full ≠ maintained"
    -- the known answers: 2 → 1 distinct, then 0 (canceled) — full 0
    assert (weight (cDist.denote (addW i1 dd)) 5 = 0)
      s!"distinct full at 5: got {weight (cDist.denote (addW i1 dd)) 5}, want 0"
    assert (weight (addW (cDist.denote i1) (cDist.step i1 dd)) 5 = 0)
      s!"distinct maintained at 5: got {weight (addW (cDist.denote i1) (cDist.step i1 dd)) 5}, want 0"
    -- the old-values parameter is LOAD-BEARING: same delta, different
    -- old states, DIFFERENT steps (weight-level: −1 vs 0 at row 5)
    assert (weight (cDist.step i1 dd) 5 = -1 ∧ weight (cDist.step i2 dd) 5 = 0)
      "the old-values parameter must be load-bearing (i1's step crosses zero, i2's does not)")
  [ ("distinct-delta-sabotage", fun _ =>
      assert (addW (cDist.denote i1) (distinctStepSabotaged i1 dd)
          == cDist.denote (addW i1 dd))
        "the delta-only distinct step must DISAGREE (it ignores the old state)"),
    ("false-linearity", fun _ =>
      assert (weight (cDist.step i1 dd) 5 = weight (cDist.step i2 dd) 5)
        "the linearity claim must fail: the old state changes the step") ]
  1 42

/-! ## Suite 3: the query compilation's agreement -/

/-- The compiled two-operator query: the positive-filtered base joined
    with the base (the circuit `cTwo`'s query face). -/
def qTwo : ZSet.Query Nat :=
  .join (.filter pos .idQ) .idQ

/-- Its compiled circuit. -/
def cCompiled : Ckt Nat := compile qTwo

/-- The full recomputation of the compiled query on the merged state. -/
def fullCompiled : ZSet Nat := cCompiled.denote (addW b0 d0)

/-- The maintained result through the circuit's delta face. -/
def maintainedCompiled : ZSet Nat :=
  addW (cCompiled.denote b0) (cCompiled.step b0 d0)

/-- The dropped-filter sabotage: the JOIN WITHOUT the selection — a
    different query with different weights. -/
def cNoFilter : Ckt Nat := .join .input .input

def specCompile : Spec := Spec.ofList "compile"
  (fun _ => do
    -- the compilation's agreement (compile_ok's face), as data
    assert (cCompiled.denote b0 == ZSet.evaluate qTwo b0)
      "compiled denotation ≠ query evaluation"
    -- known answers over the base: row 2: filter 2, join 2*2 = 4
    assert (weight (cCompiled.denote b0) 2 = 4)
      s!"compiled row 2: got {weight (cCompiled.denote b0) 2}, want 4"
    -- row 3 is filtered out (weight −1): 0 * (−1) = 0
    assert (weight (cCompiled.denote b0) 3 = 0)
      s!"compiled row 3: got {weight (cCompiled.denote b0) 3}, want 0"
    -- THE DELTA FACE: the compiled query maintained incrementally IS
    -- the recomputation (incrementalize_ok through compile)
    assert (fullCompiled == maintainedCompiled)
      "the compiled query's delta face disagrees with the recomputation")
  [ ("dropped-filter-sabotage", fun _ =>
      assert (cNoFilter.denote b0 == cCompiled.denote b0)
        "the unfiltered join must DISAGREE (row 3's −1 self-join is filtered away)"),
    ("false-delta-break", fun _ =>
      assert (!(fullCompiled == maintainedCompiled))
        "the claim that the delta face breaks must fail (the theorem holds)") ]
  1 42

/-! ## Suite 4: the bottom-up rewrite pass -/

/-- A left-nested union — `optOnce`'s fire shape. -/
def cU : Ckt Nat :=
  .union (.union .input (.lift (.oFilter pos) .input)) .input

/-- The pass's output. -/
def cOpt : Ckt Nat := cU.recursiveOpt

/-- THE SHAPE PIN (compile-time): the pass reassociated the left-nested
    union — the rewrite FIRED. -/
theorem cOpt_reassociated :
    cOpt = .union .input (.union (.lift (.oFilter pos) .input) .input) := rfl

/-- The pass is NOT the identity on this shape (the negative control's
    compile-time face). -/
theorem cOpt_ne : ¬ (cOpt = cU) := by
  intro h
  rw [cOpt_reassociated] at h
  injection h with h1 _
  cases h1

def specRewrite : Spec := Spec.ofList "rewrite"
  (fun _ => do
    -- the denotation is preserved (recursive_opt_ok's face), as data
    assert (cOpt.denote b0 == cU.denote b0)
      "the rewrite pass changed the denotation"
    -- known answer: the union's weight at 2: 2 + 2 + 2 = 6
    assert (weight (cOpt.denote b0) 2 = 6)
      s!"rewritten weight at 2: got {weight (cOpt.denote b0) 2}, want 6")
  [ ("denotation-change-sabotage", fun _ =>
      assert (!(cOpt.denote b0 == cU.denote b0))
        "the claim that the pass changes the denotation must fail"),
    ("wrong-known-answer", fun _ =>
      assert (weight (cOpt.denote b0) 2 = 5)
        "the 5-claim must fail: the union's row-2 weight is 6") ]
  1 42

/-! ## The driver -/

def main : IO UInt32 :=
  mainOfSuites
    [("agree", [specAgree]),
     ("old-values", [specOldValues]),
     ("compile", [specCompile]),
     ("rewrite", [specRewrite])]

/-
ContractsTests.Feasibility — the feasibility discipline's teeth (B2:
the spec-sanity row, 04 §5 + D21). The full suite lives HERE because
the teeth import `Contracts.Feasibility` — and the GatesTests root is
C0 machinery (the cone table, LintKit.Cone.coneOfRoot?): the cone rule
sits the discipline's tests on the discipline's own cone. The
gate-level pins over the census's DATA (the counts + the planted
vacuous row's caught face) stay in GatesTests.Main, import-clean.

Positive pins + the MANDATORY negative controls (15-patterns #5):

- the honest verdicts are closed data: unchecked is the WARNING cell
  and is NOT checked; the declared emptiness IS checked (declared ≠
  passed); a `feasible` verdict always names its evidence;
- the census render is drift-watched: a verdict change, a name change,
  and an added row each change the bytes;
- THE unforgeability: the planted vacuous contract has NO admissible
  input (`vacuousC_no_witness`) — a witness row for it is a row the
  type face refuses to forge, so its honest census cell is the
  DECLARED emptiness, rendered visibly, never a silent pass;
- the REAL census consumes the discipline: the counts are pinned, no
  registered spec is unchecked, and the planted vacuous contract's own
  row is the declared-empty cell.
-/

import Contracts.Feasibility
import Gates.Feasibility
import TestingKit.Harness

namespace ContractsTests.Feasibility

open Contracts TestingKit

/-- The planted vacuous contract's honest census row: the DECLARED
emptiness (the `feasible` verdict is the one the discipline refuses —
`vacuousC_no_witness` leaves no admissible input to witness). -/
def feasVacRow : Feas.SpecRow :=
  { name := "vacuousC (the planted inconsistent contract)", lane := "contracts"
    verdict :=
      Contract.feasVerdict (Feasibility.declaredVacuous (c := vacuousC))
        "the planted vacuous contract — requires unsatisfiable" }

/-- A second row (the added-row drift control). -/
def feasVacRow2 : Feas.SpecRow :=
  { name := "another registered spec", lane := "contracts"
    verdict := .unchecked }

/-! ## The VC face's pins (FeasibleVc + the feasible point discharge) -/

-- the census specimen's program: both increments
def bothProg : Prog :=
  Prog.seq (Prog.assign 1 (fun _ => 1)) (Prog.assign 2 (fun _ => 1))

theorem wpBothReg : wp bothProg (fun _ s' => s' 1 = 1 ∧ s' 2 = 1) (fun _ => 0) := by
  rw [wp_iff bothProg (fun _ s' => s' 1 = 1 ∧ s' 2 = 1) (fun _ => 0)]
  decide

theorem vcBothReg : cBothReg.vc bothProg (fun _ => 0) := wpBothReg

instance : Decidable (cBothReg.vc bothProg (fun _ => 0)) := isTrue vcBothReg

-- the feasible point discharge FIRES at the admissible state (the
-- witness is a required argument, carried)
theorem feasDischarge_fires :
    Contract.feasiblePointDischarge "vc-cBothReg@0" `ContractsTests.Feasibility
      cBothReg bothProg (fun _ => 0) ⟨rfl, rfl⟩ = some (.decided true) := by decide

-- and its soundness, at the indexed strength: the verdict proves the VC
-- AT the admissible state
theorem feasDischarge_sound_pin :
    cBothReg.requires (fun _ => 0) ∧ cBothReg.vc bothProg (fun _ => 0) :=
  Contract.feasiblePointDischarge_sound "vc-cBothReg@0" `ContractsTests.Feasibility
    cBothReg bothProg (fun _ => 0) ⟨rfl, rfl⟩ feasDischarge_fires

-- THE non-vacuity conclusion: the discharged VC proves an admissible
-- input EXISTS (04 §5's first obligation — the vacuous contract has no
-- such row, by vacuousC_no_witness)
theorem nonvacuous_pin : ∃ s, cBothReg.requires s :=
  Contract.feasibleVc_nonvacuous cBothReg bothProg (fun _ => 0)
    (have _fv : FeasibleVc cBothReg bothProg (fun _ => 0) := ⟨⟨rfl, rfl⟩⟩; _fv)

-- the negative control's pin: the planted vacuous contract has NO
-- admissible input (the compile IS the unforgeability tooth)
example : ¬ ∃ s, vacuousC.requires s := vacuousC_no_witness

def feasSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList
      "the feasibility discipline's teeth (the B2 row: the spec-sanity census)"
      (fun _ => do
        -- the honest verdicts: unchecked is the WARNING cell and is NOT
        -- checked; the declared emptiness IS checked (declared ≠ passed)
        assert (Feas.Verdict.checked Feas.Verdict.unchecked == false)
          "an unchecked row counted as checked — the warning is fiction"
        assert ((Feas.Verdict.render Feas.Verdict.unchecked).startsWith "WARNING")
          "the unchecked cell lost its WARNING rendering"
        assert (Feas.Verdict.checked (Feas.Verdict.declaredEmpty "n"))
          "the declared emptiness counted as unchecked"
        assert ((Feas.Verdict.render (Feas.Verdict.declaredEmpty "n")).startsWith "vacuous (DECLARED")
          "the declared-empty cell lost its DECLARED rendering"
        -- the bridge: the proof-carrying declared vacuity maps to the
        -- declared-empty census cell — NEVER to a pass
        match Contract.feasVerdict (Feasibility.declaredVacuous (c := vacuousC)) "n" with
        | .declaredEmpty _ => pure ()
        | _ => assert false "the declared vacuity rendered as a pass"
        -- the census render is drift-watched: a verdict change, a name
        -- change, and an added row each change the bytes
        let one := Feas.renderCensus [feasVacRow]
        assert ((Feas.renderCensus [{ feasVacRow with verdict := .unchecked }]) != one)
          "a verdict change did NOT change the census — the drift check is fiction"
        assert ((Feas.renderCensus [{ feasVacRow with name := "renamed" }]) != one)
          "a name change did NOT change the census — the drift check is fiction"
        assert ((Feas.renderCensus [feasVacRow, feasVacRow2]) != one)
          "an added row did NOT change the census — the drift check is fiction"
        -- the planted vacuous row renders the DECLARED cell — visible,
        -- never a silent pass
        assert (one.contains "vacuous (DECLARED")
          "the planted vacuous contract's row rendered as a pass"
        -- THE REAL CENSUS consumes the discipline: the counts are pinned
        -- (6 registered specs: 4 feasible, 2 declared-empty, 0 unchecked)
        let (n, feas, decl, unch) := Gates.Feasibility.counts Gates.Feasibility.census
        assert (n == 6) s!"the feasibility census drifted: {n} rows"
        assert (feas == 4) s!"the feasibility census drifted: {feas} feasible rows"
        assert (decl == 2) s!"the feasibility census drifted: {decl} declared-empty rows"
        assert (unch == 0)
          "an UNCHECKED registered spec — the warning is data; re-adjudicate and re-baseline"
        -- and the planted vacuous contract's own row is the declared-empty cell
        assert ((Gates.Feasibility.census.any fun r =>
            r.name.startsWith "vacuousC" &&
            match r.verdict with | .declaredEmpty _ => true | _ => false))
          "the planted vacuous contract's census row is not the declared-empty cell"
        pure ())
      [ ("the unchecked row must pass as checked (a LIE — caught)", fun _ =>
          assert (Feas.Verdict.checked Feas.Verdict.unchecked)
            "the control demands the unchecked row pass")
      , ("the vacuous contract must admit a feasible verdict (a LIE — caught)", fun _ =>
          -- the fiction: registering the planted vacuous contract as
          -- FEASIBLE. The compile refuses (vacuousC_no_witness — no
          -- admissible input exists to witness); the runtime face: its
          -- honest row is the declared-empty cell, never a pass.
          match Contract.feasVerdict (Feasibility.declaredVacuous (c := vacuousC)) "n" with
          | .feasible _ => pure ()
          | _ => assert false "the control demands the feasible verdict")
      ]
    1 42 ]

end ContractsTests.Feasibility

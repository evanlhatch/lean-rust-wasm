/-
Gates.Feasibility — the spec-sanity gate row (`gates feasibility
[--write] [--accept-drift]`; item B2, 04 §5 + D21).

An inconsistent contract holds vacuously and proves nothing: a
`requires balance < 0 ∧ balance ≥ 0` admits every implementation, and
every "verified" claim over it is noise. The feasibility obligations
(04 §5): an admissible initial state exists; the operation has valid
inputs; the assumptions permit an environment; the generator reaches
its intended cases. This row answers them AS DATA over the tree's
REGISTERED specs — the census:

- the CONTRACTS lane's rows ride the proof-carrying face
  (`Contracts.Contract.Feasibility`'s witness — the admissibility proof
  is a FIELDS, it cannot be forged; `Contracts.FeasibleVc`'s witness
  likewise for the VCs) through the census bridge
  (`Contract.feasVerdict`);
- the MACHINES lane's rows CITE the battery's non-vacuity verdicts
  (`Machines.Testing.invariantNonVacuous`, pinned in MachinesTests) —
  consumed, never duplicated (no second non-vacuity engine exists).

The honest verdicts (`Contracts.Feas.Verdict`): feasible-with-evidence
/ declaredEmpty / unchecked — NEVER a silent pass. The census is
CENSUS-GRADE (the 09 §8 rule, the nolint-census precedent): the first
run's findings are DATA, baselined in notes/feasibility-census.md; a
drift (a new registered spec, a verdict change) is the deliberate
re-baseline diff, never a failure flood. The TEETH are the discipline
itself (GatesTests.Feasibility): a planted vacuous contract has NO
admissible input (`Contracts.vacuousC_no_witness`), so a `feasible`
verdict for it is unforgeable — its honest row is `declaredEmpty`,
which the census renders VISIBLY; and every render byte is
drift-watched.

The five questions (notes/v3/01-core.md): none of its own — a census
row (data + drift) over the feasibility discipline.
-/
import Contracts
import Contracts.Feasibility
import Gates.ObligationView
import Gates.Packages
import Gates.Common

namespace Gates.Feasibility

open Contracts
open Gates.Driver

/-- THE gate's OWN claim (the obligation's type index — B7's
    self-application lands HERE first): a certificate filed under a
    different gate's claim is a different TYPE, so this feasibility
    row cannot be discharged by another gate's run. -/
instance : Gates.ObligationView.GateClaim "feasibility" := ⟨⟩

/-- THE first feasibility census: the tree's registered specs with
preconditions, one row per spec. The contracts rows carry (or declare)
their admissibility through the proof-carrying bridge; the machines
rows cite the battery's non-vacuity verdicts by name — the pins live
in MachinesTests, the gate consumes them as citations (census-grade).
A lane whose specs have preconditions joins by adding rows HERE (the
loud gap: the census's row list is the data — a lane absent from it is
a lane the spec-sanity report does not cover, named in the baseline
header). -/
def census : List Feas.SpecRow :=
  [ { name := "cBothReg / both increments (the both-cells contract)", lane := "contracts"
      verdict :=
        Contract.feasVerdict cBothReg_witness
          "witness: the zero state (the carried proof — Contracts.cBothReg_witness)" }
  , { name := "cWrongReg / both increments (feasible, NOT satisfied)", lane := "contracts"
      verdict :=
        Contract.feasVerdict cWrongReg_witness
          "witness: the zero state — the precondition is satisfiable; \
            the VC is what refuses (feasibility ≠ verification)" }
  , { name := "vacuousC (the planted inconsistent contract)", lane := "contracts"
      verdict :=
        Contract.feasVerdict (Feasibility.declaredVacuous (c := Contracts.vacuousC))
          "requires s 1 < 0 ∧ s 2 > 0 — unsatisfiable over the state model \
            (vacuousC_no_witness: NO admissible input exists)" }
  , { name := "sumWhile guard (the summing loop's precondition)", lane := "contracts"
      verdict :=
        .feasible "witness stOf 0 0 5 — cited: ContractsTests.sumLoopSat \
          (the four VCs sumVCs discharged)" }
  , { name := "m3i tick invariant (the battery's non-vacuity)", lane := "machines"
      verdict :=
        .feasible "cited: MachinesTests.Main — invariantNonVacuous m3i \
          statesFull = .proved (the battery3i_nonvacuous pin)" }
  , { name := "mGhost invariant (the ghost machine's empty guard set)", lane := "machines"
      verdict :=
        .declaredEmpty "cited: MachinesTests.Main — invariantNonVacuous \
          mGhost ghostStates = .refuted .vacuous (the battery REFUTES the \
          vacuous guard; the emptiness is the battery's verdict)" }
  ]

/-- The census's honest counts: (specs, feasible, declared-empty,
unchecked). The unchecked count is the WARNING face — reported at
every run, never silent. -/
def counts (rows : List Feas.SpecRow) : Nat × Nat × Nat × Nat :=
  rows.foldl
    (fun (acc : Nat × Nat × Nat × Nat) r =>
      match r.verdict with
      | .feasible _ => (acc.1 + 1, acc.2.1 + 1, acc.2.2.1, acc.2.2.2)
      | .declaredEmpty _ => (acc.1 + 1, acc.2.1, acc.2.2.1 + 1, acc.2.2.2)
      | .unchecked => (acc.1 + 1, acc.2.1, acc.2.2.1, acc.2.2.2 + 1))
    (0, 0, 0, 0)

/-- The committed baseline. -/
def baselinePath : System.FilePath := "notes/feasibility-census.md"

/-- `feasibility [--write] [--accept-drift]` — the gate row. -/
def run (write acceptDrift : Bool) : IO UInt32 := do
  let text := Feas.renderCensus census
  let (n, feas, decl, unch) := counts census
  -- the human face on stderr (the report block is the baseline bytes)
  IO.eprintln s!"feasibility: {n} registered specs — {feas} feasible, \
    {decl} declared-empty, {unch} UNCHECKED (the warnings)"
  for r in census do
    if !Feas.isChecked r.verdict then
      IO.eprintln s!"feasibility: {r.lane}/{r.name}: {r.verdict.render}"
  -- THE OBLIGATION TAIL (B7's adoption — the run IS the discharge
  -- attempt): the gateObligation row → the discharge attempt (the
  -- baseline diff's three faces ARE the verdict's) → `certify`'s mint
  -- AS DATA. The certificate gates the quiet face: a mint is the
  -- discharged run (no finding exists); a refusal (a STALE or absent
  -- certificate) falls to the LOUD `diffCheck` face — the same
  -- drift/absent lines as before, byte-identical (the diff is re-run
  -- against the SAME committed bytes, so its render agrees with the
  -- verdict by construction). Behavior unchanged; the discipline is
  -- now the gate's own.
  let row := Gates.ObligationView.gateObligation "feasibility"
    "the registered specs' feasibility census"
  let evidence := Gates.ObligationView.certificate
    baselinePath.toString "feasibility"
  let verdict := Gates.ObligationView.attempt
    (← Driver.diffBaseline baselinePath text) evidence
  Driver.reportGate "feasibility" baselinePath text write acceptDrift false
    "feasibility: clean — the registered specs' feasibility census in sync"
    (do
      match Gates.ObligationView.certify row verdict with
      | some _ => return false
      | none =>
          Driver.diffCheck "feasibility" "census"
            "the registered specs' feasibility rows changed (a new spec, a verdict \
              change — re-adjudicate, then re-baseline)"
            baselinePath text)

end Gates.Feasibility

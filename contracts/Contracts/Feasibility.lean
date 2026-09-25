/-
# Contracts.Feasibility — the VCs' feasibility face (04 §5 + D21)

The spec-sanity discipline as DATA (item B2). An inconsistent contract
holds vacuously and proves nothing: `requires balance < 0 ∧ balance ≥ 0`
admits every implementation. `Contracts.Contract` already carries the
per-contract face (`Contract.Feasibility` — the proof-carrying witness /
the declared vacuity / the unchecked warning, `sat_of_inconsistent` as
the tripwire). THIS module adds what B2 lands:

1. **The VC face**: a verification condition is only as good as its
   ADMISSIBLE ENTRY STATE — `FeasibleVc` carries the admissibility
   witness, and the point discharge through the feasibility face
   (`Contract.feasiblePointDischarge`) is sound AT the indexed strength:
   a `.decided true` proves the VC at an admissible state, and the
   non-vacuity theorem (`feasibleVc_nonvacuous`) concludes that an
   admissible input EXISTS (04 §5's first obligation).
2. **The census face**: the honest verdicts as closed data
   (`Feas.Verdict` — feasible-with-evidence / declaredEmpty / unchecked,
   NEVER a silent pass), the lane-agnostic census row (`Feas.SpecRow`),
   and the canonical render the `feasibility` gate baselines. The
   bridge (`Contract.feasVerdict`) maps the PROOF-CARRYING per-contract
   rows onto the census verdicts — the census cites, never re-encodes.

The negative control is THE theorem below (`vacuousC_no_witness`): the
planted vacuous contract — a `requires` that looks like a real
precondition but is unsatisfiable — has NO admissible input, so a
`witness` verdict for it is a row the type face refuses to forge; the
honest row is `declaredEmpty` (visible, declared) or `unchecked` (the
warning), never a pass.

The five questions (notes/v3/01-core.md):
- root: Universe — the feasibility verdicts + census rows as closed
  data over the fragment.
- carrier grade: none — the verdict is plain data; the discipline is
  the proof-carrying witness field (the vacuous row cannot claim it).
- spine reading: none — the lanes' feasibility rows ride it; nothing
  is accumulated here (the census LIST is the gate's data).
- ladder rung: rung 6 — small hand theorems (the discharge's soundness
  routes through `Contract.pointDischarge_sound` /
  `Kit.Obligation.decideDischarge_sound`; the non-vacuity conclusion).
- gate row: the `feasibility` gate row (Gates.Feasibility) consumes
  this module's census face; ContractsTests pins the contract face.

Core-only: imports Contracts.Wp + Kit.Obligation only (the cone rule).
-/

import Contracts.Wp
import Contracts.Contract
import Kit.Obligation

namespace Contracts

/-! ## The VC's feasibility face -/

/-- THE VC's feasibility row: a verification condition is checked at a
STATE, and only an ADMISSIBLE state makes the check non-vacuous (04 §5:
"the operation has valid inputs"). The witness is carried in the type —
a `requires` that is unsatisfiable cannot construct this row. -/
structure FeasibleVc (c : Contract Nat) (p : Prog) (s : State) where
  /-- The entry state is admissible — the witness, carried. -/
  adm : c.requires s

/-- The VC discharge THROUGH the feasibility face: the point discharge
runs at an entry state whose admissibility is PROVEN (`h`) — the
vacuous-contract trap (`Contract.sat_of_inconsistent`) cannot hide a
discharge behind an inadmissible state, because the witness is a
required argument, never an assumption. -/
def Contract.feasiblePointDischarge (label : String) (provenance : Lean.Name)
    (c : Contract Nat) (p : Prog) (s : State) (h : c.requires s)
    [Decidable (c.vc p s)] : Option Kit.Evidence :=
  -- the witness is carried (the feasibility row); the discharge is the
  -- point discharge — one backend, no parallel machinery
  let _ := h
  c.pointDischarge label provenance p s

/-- SOUNDNESS of the feasible point discharge, at the indexed strength:
a `.decided true` verdict proves the VC at an ADMISSIBLE state — the
non-vacuous fragment of the satisfaction claim. Routes through
`Contract.pointDischarge_sound` (→ `Kit.Obligation.decideDischarge_sound`). -/
theorem Contract.feasiblePointDischarge_sound (label : String)
    (provenance : Lean.Name) (c : Contract Nat) (p : Prog) (s : State)
    (h : c.requires s) [Decidable (c.vc p s)]
    (hd : Contract.feasiblePointDischarge label provenance c p s h
            = some (.decided true)) :
    c.requires s ∧ c.vc p s :=
  ⟨h, c.pointDischarge_sound label provenance p s hd⟩

/-- THE non-vacuity conclusion (04 §5's first obligation): a VC checked
through the feasibility face proves an ADMISSIBLE INPUT EXISTS. A spec
whose `requires` is unsatisfiable has no `FeasibleVc` row — the
existence claim below is exactly what the vacuous contract cannot give. -/
theorem Contract.feasibleVc_nonvacuous (c : Contract Nat) (p : Prog) (s : State)
    (fv : FeasibleVc c p s) : ∃ s, c.requires s :=
  ⟨s, fv.adm⟩

/-! ## The census face — the honest verdicts as closed data -/

/-- The census verdict (04 §5's three honest faces, lane-agnostic so
the machines' cited battery verdicts ride the same row):
`feasible` names its evidence (a carried witness or a cited
non-vacuity verdict); `declaredEmpty` DECLARES the unsatisfiable
`requires` (emptiness is sometimes intentional — then it's declared,
never mistaken for success); `unchecked` is the WARNING cell —
reported, never a pass. -/
inductive Feas.Verdict where
  | feasible (evidence : String)
  | declaredEmpty (note : String)
  | unchecked
deriving BEq, Repr, Inhabited

/-- The verdict's honesty face: checked = the row answers the
feasibility obligation (witness or declared emptiness). -/
def Feas.Verdict.checked : Feas.Verdict → Bool
  | .feasible _ => true
  | .declaredEmpty _ => true
  | .unchecked => false

/-- The verdict's cell rendering (the census's row tail). -/
def Feas.Verdict.render : Feas.Verdict → String
  | .feasible e => s!"feasible ({e})"
  | .declaredEmpty n => s!"vacuous (DECLARED — {n})"
  | .unchecked => "WARNING: admissibility unchecked"

/-- One registered spec's census row: the spec's name, the lane that
owns it, the verdict. -/
structure Feas.SpecRow where
  name : String
  lane : String
  verdict : Feas.Verdict
deriving BEq, Repr, Inhabited

/-- The row's TSV line (`lane<TAB>name<TAB>verdict`). -/
def Feas.SpecRow.render (r : SpecRow) : String :=
  s!"{r.lane}\t{r.name}\t{r.verdict.render}"

/-- The canonical census render: the header + the rows sorted by
(lane, name) — the `feasibility` gate's baseline bytes. -/
def Feas.renderCensus (rows : List SpecRow) : String :=
  let sorted := rows.toArray.qsort fun a b =>
    a.lane < b.lane || (a.lane == b.lane && a.name < b.name)
  String.intercalate "\n"
    ([ "# Feasibility census — the registered specs' admissibility rows"
     , "GENERATED by `lake exe gates feasibility --write` — do not hand-edit."
     , "CI runs `feasibility` without --write; a diff fails the gate."
     , "The honest verdicts (04 §5): feasible (evidence named) / vacuous"
     , "(DECLARED) / unchecked (the WARNING) — never a silent pass."
     , "lane\tname\tverdict" ]
    ++ sorted.toList.map (·.render))

/-- THE bridge: the proof-carrying per-contract feasibility row
(`Contract.Feasibility`) → the census verdict. The census CITES the
carried witness (the admissibility proof rides the type — it cannot be
forged), never re-encodes it. -/
def Contract.feasVerdict {c : Contract Nat} (f : Feasibility c)
    (evidence : String) : Feas.Verdict :=
  match f with
  | .witness _ _ => .feasible evidence
  | .declaredVacuous =>
      -- the registrar's note is CARRIED (the declared emptiness names
      -- its reason — 04 §5: the emptiness is declared, with the note)
      .declaredEmpty s!"the requires is unsatisfiable — the satisfaction \
        proves nothing (sat_of_inconsistent); {evidence}"
  | .unchecked => .unchecked

/-! ## The lane's registered specimens — the census's contracts rows -/

/-- A REGISTERED worked contract (the lane's census specimen): from
cells 1, 2 zero, the two increments land both at 1. The witness: the
zero state — the admissibility proof CARRIED (never asserted). -/
def cBothReg : Contract Nat where
  requires := fun s => s 1 = 0 ∧ s 2 = 0
  ensures := fun _ _ s' => s' 1 = 1 ∧ s' 2 = 1

/-- cBothReg's witness: the zero state is admissible. The PROOF is the
feasibility row — the census cites it, it cannot forge it. -/
def cBothReg_witness : Feasibility cBothReg :=
  .witness (fun _ => 0) ⟨rfl, rfl⟩

/-- A registered contract whose precondition is satisfiable but whose
POSTcondition fails (the tests' wrong-postcondition discipline): the
census's point — FEASIBLE is not SATISFIED; the VC is what refuses. -/
def cWrongReg : Contract Nat where
  requires := fun s => s 1 = 0 ∧ s 2 = 0
  ensures := fun _ _ s' => s' 1 = 99 ∧ s' 2 = 1

/-- cWrongReg's witness: the precondition is satisfiable (that is ALL
feasibility claims). -/
def cWrongReg_witness : Feasibility cWrongReg :=
  .witness (fun _ => 0) ⟨rfl, rfl⟩

/-! ## The negative control — the planted vacuous contract -/

/-- The PLANTED vacuous contract (04 §5's inconsistent contract, the
decidable disguise): the `requires` reads like a real precondition but
is unsatisfiable over the state model — it admits every program. -/
def vacuousC : Contract Nat where
  requires := fun s => s 1 < 0 ∧ s 2 > 0
  ensures := fun _ _ _ => True

/-- THE unconstructibility tooth: the planted vacuous contract has NO
admissible input — `FeasibleVc`'s witness field and
`Contract.Feasibility.witness`'s proof field are rows the type face
refuses to forge for it. A `feasible` verdict for this contract is a
LIE the discipline makes unrepresentable; the honest row is
`declaredEmpty`, and the census renders it visibly. -/
theorem vacuousC_no_witness : ¬ ∃ s : State, vacuousC.requires s := by
  rintro ⟨s, h⟩
  have h1 : s 1 < 0 := h.1
  omega

end Contracts

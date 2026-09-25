/-
# Contracts.Contract — the contract surface + the obligation + the feasibility discipline

The contract lanes' surface (notes/v3/08-capabilities.md §36): a
contract is `requires` (the precondition over the ENTRY state) +
`ensures` (the postcondition over the entry state, the result, the EXIT
state — the old-state/input/output/new-state discipline the review
names). A program SATISFIES its contract as the obligation — the
Prop-indexed `Kit.Obligation` (a discharge proves the ACTUAL claim, the
type says it). The wp discipline (`Contracts.Wp`) computes the
verification conditions (`Contract.vc`) — the toolkit's face; the
routine fragments discharge through the decidableNow backend, the
remaining domain-specific goals surface as hand theorems
(`Contract.sat_of_vc` reduces satisfaction to exactly the VCs).

The feasibility discipline (notes/v3/04-verification.md §5): an
inconsistent contract holds vacuously and proves nothing — admissibility
is DATA carried with the satisfaction (`Feasibility`, `Satisfied`), the
vacuous case is DECLARED (`sat_of_inconsistent` + `.declaredVacuous`),
never mistaken for success. The honest minimal: the witness row + the
declared-vacuity row + the unchecked warning; the full witness
discipline is the follow-up.

The five questions (notes/v3/01-core.md):
- root: Universe (the contract structure + the obligation rows + the
  feasibility rows as closed data over the fragment).
- carrier grade: the obligation's claim index — a discharge filed under
  a different claim is a different TYPE (Kit.Obligation's discipline,
  consumed read-only).
- spine reading: none — the lanes' contracts ride it.
- ladder rung: rung 3 (the feasibility row is carried at construction
  in `Satisfied`) + rung 6 (`sat_of_vc`, `sat_of_inconsistent`, the
  point-discharge soundness — small hand theorems).
- gate row: none yet — ContractsTests.Axioms pins the axiom cones.
-/

import Contracts.Wp
import Kit.Obligation
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Contracts

/-! ## The contract surface -/

/-- The contract: the precondition over the entry state, the
postcondition over the entry state / result / exit state — the
old-state/input/output/new-state discipline the review names. The
result-carrying discipline (08 §36's full shape): the fragment's
programs return `Nat` results (`Prog.exec`'s pair), so the result
parameter is lived-in — `Contract Nat` is this engine's instantiation. -/
structure Contract (result : Type := Unit) where
  /-- The precondition: over the ENTRY state. -/
  requires : State → Prop
  /-- The postcondition: over the entry state, the result, the EXIT state. -/
  ensures : State → result → State → Prop

/-- Satisfaction: the program's execution from every admissible entry
state lands in the postcondition — THE obligation's claim, over the
entry state, the RESULT, and the exit state. -/
def Contract.sat (c : Contract Nat) (p : Prog) : Prop :=
  ∀ s, c.requires s → c.ensures s (p.exec s).1 (p.exec s).2

/-! ## The wp discipline's toolkit face -/

/-- The verification condition at an entry state: the wp-computed
precondition (the toolkit computes it — the developer never writes it by
hand; the review's §5). The postcondition rides the result + the exit
state — §36's full shape. -/
def Contract.vc (c : Contract Nat) (p : Prog) (s : State) : Prop :=
  wp p (fun x s' => c.ensures s x s') s

/-- THE wp discipline's sufficiency theorem: the wp-computed
precondition suffices for the contract's satisfaction — the obligations
are EXACTLY the verification conditions. The compound obligations derive
STRUCTURALLY (the composition/conditional rules are `wp`'s definitional
arms); what remains after the routine fragments discharge are the
domain-specific goals, and they surface as the VCs, never hidden. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (cBoth_sat); the wp discipline's sufficiency theorem — the obligations are exactly the VCs"]
theorem Contract.sat_of_vc (c : Contract Nat) (p : Prog)
    (h : ∀ s, c.requires s → c.vc p s) : c.sat p :=
  fun s hr => wp_sound p (fun x s' => c.ensures s x s') s (h s hr)

/-! ## The obligation integration (Kit.Obligation, read-only) -/

/-- The satisfaction obligation: the claim IS `c.sat p` (the type
index — a discharge proves the actual claim). The `provedAtElab` tier is
the honest assignment for the symbolic route: the claim is discharged by
the hand theorem citing `Contract.sat_of_vc` (+ the surfaced VCs), not
by a decision procedure. -/
def Contract.obligation (label : String) (provenance : Lean.Name)
    (c : Contract Nat) (p : Prog) :
    Kit.Obligation (Contract Nat × Prog) (c.sat p) :=
  { label := label, tier := .provedAtElab
    payload := (c, p), provenance := provenance }

/-- The point obligation: the VC at a concrete entry state — the routine
fragment. The `decidableNow` tier is honest HERE: the `Decidable`
instance gates the constructor, so a non-decidable VC cannot get this
tier by this route. -/
def Contract.pointObligation (label : String) (provenance : Lean.Name)
    (c : Contract Nat) (p : Prog) (s : State) [Decidable (c.vc p s)] :
    Kit.Obligation (Contract Nat × Prog × State) (c.vc p s) :=
  { label := label, tier := .decidableNow
    payload := (c, p, s), provenance := provenance }

/-- The routine fragment's discharge: Kit's decidableNow backend, over
the obligation's OWN claim (tier-gated — any other tier returns `none`,
the loud gap). A false VC returns `none` too: the backend REFUSES, it
never fabricates evidence. -/
def Contract.pointDischarge (label : String) (provenance : Lean.Name)
    (c : Contract Nat) (p : Prog) (s : State) [Decidable (c.vc p s)] :
    Option Kit.Evidence :=
  (Contract.pointObligation label provenance c p s).decideDischarge

/-- SOUNDNESS of the point discharge, at the indexed strength (routes
through `Kit.Obligation.decideDischarge_sound`): a `.decided true`
verdict proves the obligation's own claim — the VC. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (pointSound_pin); the point discharge's soundness at the indexed strength (routes through Kit.Obligation.decideDischarge_sound)"]
theorem Contract.pointDischarge_sound (label : String) (provenance : Lean.Name)
    (c : Contract Nat) (p : Prog) (s : State) [Decidable (c.vc p s)]
    (h : Contract.pointDischarge label provenance c p s = some (.decided true)) :
    c.vc p s := by
  unfold pointDischarge at h
  exact Kit.Obligation.decideDischarge_sound _ (by rfl) h

/-! ## The feasibility discipline (04 §5) -/

/-- The feasibility row: an inconsistent contract holds vacuously and
proves nothing — admissibility is DATA carried with the satisfaction,
never mistaken for it. The honest minimal: the carried witness / the
DECLARED vacuity / the unchecked warning (the full witness discipline is
the follow-up). -/
inductive Feasibility (c : Contract Nat) where
  /-- An admissible initial state EXISTS — the witness is carried. -/
  | witness (s : State) (h : c.requires s) : Feasibility c
  /-- Emptiness is intentional and DECLARED — the satisfaction proves
  nothing, and the row says so. -/
  | declaredVacuous : Feasibility c
  /-- No witness yet — the honest gap: reported, never a pass. -/
  | unchecked : Feasibility c

/-- The report face: the row is checked (witness or declared vacuity)
or it is not (`unchecked` — the spec-sanity report's warning cell). -/
def Feasibility.checked {c : Contract Nat} : Feasibility c → Bool
  | .witness _ _ => true
  | .declaredVacuous => true
  | .unchecked => false

/-- The report face: the row's rendering (the spec-sanity report's
cell — 04 §5: emptiness is sometimes intentional, then it's DECLARED). -/
def Feasibility.render {c : Contract Nat} : Feasibility c → String
  | .witness _ _ => "admissible (witness carried)"
  | .declaredVacuous => "vacuous (DECLARED — the satisfaction proves nothing)"
  | .unchecked => "WARNING: admissibility unchecked"

/-- THE vacuity tripwire (04 §5): an inconsistent `requires` admits
EVERY program — the satisfaction holds vacuously, proving nothing.
Named so the vacuous success is never mistaken for verification; the
honest pairing is `Satisfied` (below), which carries the row. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by ContractsTests (vac_pin); THE vacuity tripwire (04 §5) — the vacuous success is never mistaken for verification"]
theorem Contract.sat_of_inconsistent (c : Contract Nat) (p : Prog)
    (h : ∀ s, ¬ c.requires s) : c.sat p :=
  fun s hr => absurd hr (h s)

/-- The satisfaction + feasibility pairing: the obligation's honest
shape — the claim and its admissibility row TOGETHER (never one without
the other where vacuity is possible). -/
structure Satisfied (c : Contract Nat) (p : Prog) where
  proof : c.sat p
  feas : Feasibility c

-- The pairing's Prop-face projection — the claim field (the
-- satisfaction rides the type; claim + feasibility row TOGETHER). The
-- full witness discipline is the header's named follow-up.
attribute [nolint linter.guestlang.zeroCitation "public API: the pairing's claim field — the satisfaction rides the type (claim + feasibility row TOGETHER, never one without the other where vacuity is possible); the full witness discipline is the header's named follow-up"]
  Satisfied.proof

end Contracts

/-
# Kit.Obligation — the obligation substrate (the discharge tier system)

Every checkable fact as data (15-patterns #4): label + computed tier +
payload + provenance + closed evidence; the discharge backends live
once HERE; a row whose evidence's tier mismatches the obligation's
fails construction (`Discharged` — armed-but-unfired becomes
unrepresentable); an undischarged obligation is a loud gap.

Provenance: mined from `legacy/lean/codegen-core/CodegenCore/Kit.lean`
(the `Obligation` section, verbatim theorem content for the
`decideEvidence`/`decideDischarge` family + their soundness/
completeness theorems). Deliberately OUT (no consumer in this
landing): the certificate-citation resolution gate (legacy C7 —
`Dbsp.Certs.#check_cert`'s home is downstream, not core).

Core-only: `Name`/`String` are prelude types — nothing schema-shaped
crosses this line.

The five questions (notes/v3/01-core.md):
- root: none — the discipline layer's substrate over checkable facts
  (01 §4: an obligation = a correspondence instance + tier + evidence).
- carrier grade: none of its own — a row PACKAGES tier + evidence;
  the mis-wire rule (tier mismatch fails construction) is the
  unrepresentable grade.
- spine reading: none — the lanes' obligations ride it; nothing is
  accumulated or read here.
- ladder rung: this file DEFINES the tier set (the rung vocabulary:
  provedAtElab > decidableNow > generatedCheck > oracleSwept >
  guestVerified); the backends' soundness/completeness are hand
  theorems, ported verbatim.
- gate row: none yet — Kit is outside Gates.Packages' gated set;
  KitTests.Axioms pins the backends' axiom cones.
-/

import Lean

namespace Kit

/-! ## The closed tier set -/

/-- The discharge tier: WHICH backend discharges the obligation. A
    BACKEND ASSIGNMENT, not a property of the fact (kernel proof /
    decide / generated runtime check / oracle sweep / guest-verified). -/
inductive Tier where
  | provedAtElab
  | decidableNow
  | generatedCheck
  | oracleSwept
  | guestVerified
deriving Repr, BEq, DecidableEq, Inhabited

/-- The tier's rendering (emitted doc comments + test pins). -/
def Tier.render : Tier → String
  | .provedAtElab => "proved-at-elab"
  | .decidableNow => "decidable-now"
  | .generatedCheck => "generated-check"
  | .oracleSwept => "oracle-swept"
  | .guestVerified => "guest-verified"

instance : ToString Tier := ⟨Tier.render⟩

/-! ## The closed evidence set -/

/-- The discharge's EVIDENCE: which backend artifact carries it — a
    cited kernel theorem, a decide result, a generated check fn (at an
    artifact path), an oracle row reference, or a guest-checked
    witness. -/
inductive Evidence where
  | citedProof (thm : Lean.Name)
  | decided (result : Bool)
  | generatedCheck (artifact fn : String)
  /-- The differential sweep's reference: the oracle fn the row
      replays. The ref is evidence of a SWEEP, never a proof. -/
  | oracleRow (ref : String)
  /-- `artifact` = the byte-tied witness file; `ref` = the obligation's
      label inside it. -/
  | guestWitness (artifact ref : String)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The evidence's tier: every evidence shape belongs to exactly one
    backend. A discharge whose evidence's `.tier` differs from the
    obligation's tier is MIS-WIRED — checkable as data, and the
    `Discharged` structure below makes the mismatch UNCONSTRUCTIBLE. -/
def Evidence.tier : Evidence → Tier
  | .citedProof _ => .provedAtElab
  | .decided _ => .decidableNow
  | .generatedCheck _ _ => .generatedCheck
  | .oracleRow _ => .oracleSwept
  | .guestWitness _ _ => .guestVerified

/-! ## The obligation as data -/

/-- A checkable fact as data: the label, the computed discharge tier,
    the lane's own payload, and the declaring declaration. Registration
    COMPUTES the tier; backends READ it. -/
structure Obligation (α : Type) where
  label : String
  tier : Tier
  payload : α
  provenance : Lean.Name
deriving Inhabited

/-- A discharge: the obligation plus its evidence, with the MIS-WIRE
    RULE IN THE TYPE — `Evidence.tier ev` must equal `o.tier`, so a
    tier-mismatched discharge fails to construct. (`tierOK` defaults to
    `by decide` — for concrete obligations + evidence the mismatch is a
    `decide`-refutable literal.) -/
structure Discharged (α : Type) where
  obligation : Obligation α
  evidence : Evidence
  tierOK : evidence.tier = obligation.tier := by decide

/-- The data-level mis-wire check (for surfaces that inspect, not
    construct): the tiers disagree — the loud, greppable gap. -/
def tierMismatch (o : Obligation α) (e : Evidence) : Bool :=
  e.tier != o.tier

/-! ## The decidableNow backend — ONE implementation, many lanes -/

/-- The verdict combinator: a decidable claim → `.decided true` on a
    TRUE verdict, `none` on a false one (the loud gap — the backend
    refuses, it does not fabricate evidence). -/
def Obligation.decideEvidence (claim : Prop) [Decidable claim] :
    Option Evidence :=
  match decide claim with
  | true => some (.decided true)
  | false => none

/-- SOUNDNESS of the decidableNow backend: a `.decided true` verdict
    means the claim HOLDS (`of_decide_eq_true`; no new trust base).
    This is THE proof — per-lane `*_sound` theorems route through it. -/
theorem Obligation.decideEvidence_sound {claim : Prop} [Decidable claim]
    (h : Obligation.decideEvidence claim = some (.decided true)) : claim := by
  unfold decideEvidence at h
  cases hd : decide claim with
  | true => exact of_decide_eq_true hd
  | false =>
      rw [hd] at h
      simp at h

/-- COMPLETENESS: a true claim fires the backend to the `.decided
    true` evidence — the tier fires on the claims it can decide. -/
theorem Obligation.decideEvidence_of_claim {claim : Prop} [Decidable claim]
    (h : claim) : Obligation.decideEvidence claim = some (.decided true) := by
  unfold decideEvidence
  rw [decide_eq_true h]

/-- The tier-GATED application: only the `decidableNow` rung is served
    by this backend (`none` = the loud gap: a hand-set tier the lane
    cannot serve, or a FALSE decide verdict). `claim` is the lane's
    claim over the OBLIGATION; the `Decidable` instance is the lane's
    decision procedure. -/
def Obligation.decideDischarge {α : Type} (claim : Obligation α → Prop)
    [∀ o : Obligation α, Decidable (claim o)] (o : Obligation α) :
    Option Evidence :=
  match o.tier with
  | .decidableNow => decideEvidence (claim o)
  | .provedAtElab | .generatedCheck | .oracleSwept | .guestVerified => none

/-- SOUNDNESS of the tier-gated application (the per-lane `*_sound`
    bodies route through here). -/
theorem Obligation.decideDischarge_sound {α : Type} (claim : Obligation α → Prop)
    [∀ o : Obligation α, Decidable (claim o)] (o : Obligation α)
    (ht : o.tier = .decidableNow)
    (h : o.decideDischarge claim = some (.decided true)) : claim o := by
  unfold decideDischarge at h
  rw [ht] at h
  exact decideEvidence_sound h

/-- COMPLETENESS of the tier-gated application: a true claim discharges
    to the `.decided true` evidence — the backend FIRES on the claims
    it can decide. -/
theorem Obligation.decideDischarge_of_claim {α : Type} (claim : Obligation α → Prop)
    [∀ o : Obligation α, Decidable (claim o)] (o : Obligation α)
    (ht : o.tier = .decidableNow) (hc : claim o) :
    o.decideDischarge claim = some (.decided true) := by
  unfold decideDischarge
  rw [ht]
  exact decideEvidence_of_claim hc

end Kit

/-
# Kit.Obligation — the obligation substrate (the discharge tier system)

Every checkable fact as data (15-patterns #4): label + computed tier +
payload + provenance + closed evidence — and THE CLAIM ITSELF, as the
TYPE INDEX: `Obligation α P` is indexed by the proposition `P` the row
claims (notes/v3/04-verification.md §2 + the review's correction: a
discharge must prove the ACTUAL claim, never a claim-shaped name). The
backends discharge the obligation's OWN index — a discharge whose
content does not prove `P` FAILS TO ELABORATE (the mis-wire rule's
deepest promotion: today it is not merely detected, it is
unrepresentable). An undischarged obligation is a loud gap.

Provenance: mined from `legacy/lean/codegen-core/CodegenCore/Kit.lean`
(the `Obligation` section, verbatim theorem content for the
`decideEvidence`/`decideDischarge` family + their soundness/
completeness theorems), then indexed by the claim. Deliberately OUT
(no consumer in this landing): the certificate-citation resolution
gate (legacy C7 — `Dbsp.Certs.#check_cert`'s home is downstream, not
core).

Core-only: `Name`/`String` are prelude types — nothing schema-shaped
crosses this line.

The five questions (notes/v3/01-core.md):
- root: none — the discipline layer's substrate over checkable facts
  (01 §4: an obligation = a correspondence instance + tier + evidence,
  with the claimed proposition as the index).
- carrier grade: none of its own — a row PACKAGES tier + evidence; the
  mis-wire rules are the unrepresentable grade (tier mismatch fails
  `Discharged`'s construction; claim mismatch fails to ELABORATE — the
  claim is the index, the backends take none).
- spine reading: none — the lanes' obligations ride it; nothing is
  accumulated or read here. (A collection face over heterogeneous
  claims would be a `Σ`-wrapper — no consumer yet, so it does not
  exist: the leftover rule.)
- ladder rung: this file DEFINES the tier set (the rung vocabulary:
  provedAtElab > decidableNow > generatedCheck > oracleSwept >
  guestVerified); the backends' soundness/completeness are hand
  theorems, ported verbatim, restated at the indexed strength (a
  discharge PROVES the indexed claim — the type says it).
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

/-! ## The obligation as data — indexed by its claim -/

/-- A checkable fact as data, INDEXED BY ITS CLAIM: the label, the
    computed discharge tier, the lane's own payload, and the declaring
    declaration — with the claimed proposition `P` as the TYPE INDEX.
    Registration COMPUTES the tier; backends READ it and discharge `P`
    itself (no claim parameter exists to mis-wire). The claim's content
    stays opaque (a Prop — the display faces read the label + tier +
    payload, never the claim's content). -/
structure Obligation (α : Type) (P : Prop) where
  label : String
  tier : Tier
  payload : α
  provenance : Lean.Name
deriving Inhabited

/-- The row's claim, as a projection: the type index, named for the
    soundness statements' reading — `decideDischarge_sound` concludes
    `o.claim`. Definitionally `P` (an `abbrev`: the instance search in
    the soundness bodies must see through it). -/
abbrev Obligation.claim {α : Type} {P : Prop} (_o : Obligation α P) : Prop := P

/-- A discharge: the obligation plus its evidence, with BOTH mis-wire
    rules in the type — `Evidence.tier ev` must equal `o.tier` (the
    tier mismatch fails to construct), and the obligation's claim is
    the index `P` (a discharge filed under a different claim is a
    different TYPE — it fails to elaborate). (`tierOK` defaults to
    `by decide` — for concrete obligations + evidence the mismatch is a
    `decide`-refutable literal.) -/
structure Discharged (α : Type) (P : Prop) where
  obligation : Obligation α P
  evidence : Evidence
  tierOK : evidence.tier = obligation.tier := by decide

/-- The data-level mis-wire check (for surfaces that inspect, not
    construct): the tiers disagree — the loud, greppable gap. -/
def tierMismatch (o : Obligation α P) (e : Evidence) : Bool :=
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
    cannot serve, or a FALSE decide verdict). THE CLAIM IS THE
    OBLIGATION'S OWN INDEX — there is no claim parameter to mis-wire;
    `P`'s `Decidable` instance is the lane's decision procedure. -/
def Obligation.decideDischarge {α : Type} {P : Prop} (o : Obligation α P)
    [Decidable P] : Option Evidence :=
  match o.tier with
  | .decidableNow => decideEvidence P
  | .provedAtElab | .generatedCheck | .oracleSwept | .guestVerified => none

/-- SOUNDNESS of the tier-gated application, AT THE INDEXED STRENGTH:
    a discharge proves the obligation's OWN claim — the conclusion is
    the index `P` (`o.claim`, definitionally), so a discharge whose
    content proves a different proposition cannot state this theorem
    (the per-lane `*_sound` bodies route through here). -/
theorem Obligation.decideDischarge_sound {α : Type} {P : Prop}
    (o : Obligation α P) [Decidable P]
    (ht : o.tier = .decidableNow)
    (h : o.decideDischarge = some (.decided true)) : o.claim := by
  unfold decideDischarge at h
  rw [ht] at h
  exact decideEvidence_sound h

/-- COMPLETENESS of the tier-gated application: a true claim discharges
    to the `.decided true` evidence — the backend FIRES on the claims
    it can decide. -/
theorem Obligation.decideDischarge_of_claim {α : Type} {P : Prop}
    (o : Obligation α P) [Decidable P]
    (ht : o.tier = .decidableNow) (hc : P) :
    o.decideDischarge = some (.decided true) := by
  unfold decideDischarge
  rw [ht]
  exact decideEvidence_of_claim hc

end Kit

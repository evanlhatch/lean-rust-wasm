/-
# SchemaLang.Obligation — schema-level obligations (W7.1 phase 1; W9.3 fifth tier)

The kit's `CodegenCore.Obligation` instantiated at the invariant
registry row: every `schema_invariant` registration IS an obligation
(label = the invariant's name, payload = the `InvariantItem` — the
VExpr is the checkable fact, the citation the proved tier's evidence,
tier = the enforcement ladder's rung read as a backend assignment,
provenance = the name as a declaration key).

The DISCHARGE registry: `SchemaObligation.discharge` maps an obligation
to its evidence — a proved row's cited kernel theorem (resolved at
registration, `checkCitation?`) or a boundary row's generated check fn
(`invariants_generated.rs`). A `none` verdict is the LOUD gap: the tier
claims a backend the row cannot name — the "armed but unfired" pattern
as data, not as a comment. `discharge_isSome_of_computed` proves
computed-tier obligations always discharge (W9.3: the disjunct
statement — the computed invariant rungs OR a witness-backed
guestVerified row whose certificate CHECKS).

## The guestVerified backend (W9.3 — notes/design-guest-verified.md §3)

The fifth tier's discharge has TWO halves at two sites (the doc's
"host-side vs guest-side discharge"):

- HOST (here): the discharge IS the witness — the caller PROVIDES a
  `WitnessRef` (the certificate + the decoded context it certifies
  against + the artifact name W9.4 will emit it under), the arm runs
  W9.2's checker (`WitnessCheck.checkWitnessArtifact`) host-side and
  fires `.guestWitness` evidence ONLY on acceptance, with the
  certificate's label pinned to the obligation's (a certificate for
  another obligation refuses — the mis-wire check as data).
  `discharge_guestVerified_sound` cites `checkWitnessArtifact_sound`:
  a fired discharge IS the claim's `WHolds` denotation. Fuel
  exhaustion = refusal, no retry (owner decision 2 — the shipped fuel
  is part of the certificate; a low cap rejects true claims LOUDLY).
- GUEST (W9.5/W9.6, NOT here): re-check via the COMPILED checker at
  the point of use, over the transported bytes. This module is the
  host boundary; the guest re-check is the consumption boundary.

Witness GENERATION (emitting the byte-tied `.wtn` artifact the
evidence names) is W9.4 — out of scope here. Deviations from the
doc's §3 (each forced, each recorded):

1. `InvariantItem.witnessRef` and `Invariant.Tier.guestVerified` are
   NOT landed: `SchemaLang/Invariant.lean` is outside this order's
   file scope (W8.2 is concurrent in the package). The witness reaches
   `discharge` as an explicit ARGUMENT instead (the host presents the
   certificate at discharge time) — the doc's "a provided witness"
   shape. `guestVerified` obligations are hand-tiered at the kit
   level, exactly like `decidableNow` (no invariant-lane rung computes
   them; registration support is W9.4).
2. The doc's `WitnessRef` = artifact × label; here it also carries the
   certificate (`Witness.Witness`) and the decoded context
   (`WitnessCheck.RowValsP`) — the arm CHECKS, so the checker needs
   them (the doc's map-only arm deferred the check to W9.4's
   self-check; this order wires the check into the discharge itself).

Ownership: the obligation lane (this module + CodegenCore.Kit's
Obligation). Deliberate exclusions: assumptions (no consumer); a
∀-rows decide closure (the decidableNow backend discharges the
DEFAULT-ROW claim — the one row every registered invariant already
carries a verdict for, the emitted `#[test]`'s row — not a
universal closure); the oracle backend (`Tier.oracleCovered` is a
closed ctor until its first consumer lands); updates/machines as
obligations (later phases); witness generation (W9.4) and the
guest-side re-check (W9.5) — the boundary halves named above.
-/

module

public import CodegenCore
public import SchemaLang.Emit.Invariant
public import SchemaLang.WitnessCheck

@[expose] public section

namespace SchemaLang

/-- The schema-level obligation: the kit's shape at the invariant
    registry row. (`abbrev`, not `def` — the view must reduce at
    elaboration-time resolution, the kit discipline.) -/
abbrev SchemaObligation := CodegenCore.Obligation InvariantItem

/-- The invariant ladder's rungs, read as backend assignments:
    `boundaryCheck` is the emitted Rust check fn, `proved` the cited
    kernel theorem resolved at elaboration, `oracleCovered` the
    (unwired) differential sweep. `decidableNow` has no invariant-lane
    SOURCE (no `Tier` ctor maps to it — invariants execute on rows,
    they are not closed props); the backend below serves hand-tiered
    obligations over the default-row claim. -/
def Tier.toObligationTier : Tier → CodegenCore.Obligation.Tier
  | .boundaryCheck => .generatedCheck
  | .proved => .provedAtElab
  | .oracleCovered => .oracleSwept

/-- The obligation VIEW of a registered invariant (additive — the item
    is unchanged; emitters keep reading the item, the byte-tie holds).
    Provenance is the name as a declaration key: W7.5's provenance
    extension covers `Item`s, not invariant rows (the follow-up). -/
def InvariantItem.obligation (it : InvariantItem) : SchemaObligation :=
  { label := it.name
  , tier := it.tier.toObligationTier
  , payload := it
  , provenance := it.name.toName }

/-- The view's tier IS the item's tier, mapped. -/
theorem InvariantItem.obligation_tier (it : InvariantItem) :
    it.obligation.tier = it.tier.toObligationTier := rfl

/-! ## The decidableNow backend (W7.1 phase 2) -/

/-- The decidableNow CLAIM at the invariant lane: the registered
    predicate VALIDATES the all-default row
    (`SchemaLang.defaultRow?` — the same row the emitted `#[test]`
    pins, so the decide discharge and the Rust CI replay decide the
    SAME fact). Invariants execute on rows, so the decidable claim is
    a ROW claim; the default row is the row the lane already carries
    everywhere. A record whose fields lack literal defaults (tensor
    dims, `.ty` refs) has no row to decide on: the claim is `False`,
    the backend refuses. The match-on-Option shape (not `∃`) keeps
    the `Decidable` instance a two-arm split. -/
def SchemaObligation.decidableClaim (o : SchemaObligation) : Prop :=
  match SchemaLang.defaultRow? o.payload.inv.fields with
  | some row => validates o.payload.inv.expr row = true
  | none => False

/-- The claim IS decidable: a valued default row reduces it to a
    `Bool` equation (`validates` computes); a default-less record is
    `False`. This instance is the backend's decision procedure —
    `discharge` runs it via `decide` at query time. -/
instance (o : SchemaObligation) : Decidable o.decidableClaim := by
  unfold SchemaObligation.decidableClaim
  split <;> infer_instance

/-! ## The guestVerified backend (W9.3) -/

/-- A PROVIDED witness (design §3's `WitnessRef`, extended — the
    header's deviation 2): the artifact name W9.4's emitter will write
    the certificate under (the evidence's `artifact`), the certificate
    itself (its `label` field is the evidence's `ref` — the obligation
    it certifies), and the decoded context the claim is checked
    against (the row + the chain lane's log segment). -/
structure SchemaObligation.WitnessRef where
  artifact : String
  witness : Witness.Witness
  ctx : WitnessCheck.RowValsP

/-- THE DISCHARGE. A proved row's evidence is its citation (resolved
    at registration — `checkCitation?`); a boundary row's evidence is
    the emitted check fn in the emitter's declared output; a
    decidableNow row's evidence is the kernel's own `decide` over
    `decidableClaim` (WIRED — phase 2); a guestVerified row's evidence
    is the PROVIDED witness, fired ONLY when the certificate's label
    IS the obligation's AND W9.2's checker accepts the certificate at
    its own shipped fuel (W9.3 — the host half; the soundness theorem
    below cites `checkWitnessArtifact_sound`). `none` = the loud gap:
    a proved-tier claim with no citation (a hand-set tier, since the
    registration computes it), a FALSE decide verdict, a default-less
    record, the unwired `oracleSwept`, a guestVerified row with no
    provided witness / a label mismatch / a REFUSED check (tampered
    certificate, insufficient fuel — exhaustion is refusal, owner
    decision 2) — discharge refuses, it does not fabricate evidence. -/
def SchemaObligation.discharge (o : SchemaObligation)
    (w : Option SchemaObligation.WitnessRef := none) :
    Option CodegenCore.Obligation.Evidence :=
  match o.tier with
  | .provedAtElab => o.payload.proofName.map .citedProof
  | .generatedCheck =>
      some (.generatedCheck (Emit.Invariant.invariantEmitter.outputs.head!)
        (Emit.Invariant.checkFnName o.payload))
  | .decidableNow =>
      match decide o.decidableClaim with
      | true => some (.decided true)
      | false => none
  | .oracleSwept => none
  | .guestVerified =>
      match w with
      | some wr =>
          if wr.witness.label == o.label &&
             WitnessCheck.checkWitnessArtifact wr.witness wr.ctx then
            some (.guestWitness wr.artifact wr.witness.label)
          else none
      | none => none

/-- The guestVerified arm, as an equation (the proofs below rewrite
    with it instead of re-splitting the discharge's match). -/
theorem SchemaObligation.discharge_guestVerified_eq (o : SchemaObligation)
    (ht : o.tier = .guestVerified) (w : Option SchemaObligation.WitnessRef) :
    o.discharge w =
      (match w with
       | some wr =>
           if wr.witness.label == o.label &&
              WitnessCheck.checkWitnessArtifact wr.witness wr.ctx then
             some (.guestWitness wr.artifact wr.witness.label)
           else none
       | none => none) := by
  unfold SchemaObligation.discharge
  rw [ht]

/-- SOUNDNESS of the guestVerified backend (the tier's host half): a
    FIRED discharge means the witness's claim HOLDS over the decoded
    context the certificate certifies against — the evidence is
    produced only after W9.2's checker accepted the certificate at its
    own shipped fuel, so `checkWitnessArtifact_sound` transports the
    verdict to `WHolds`. (The guest-side re-check at consumption — the
    COMPILED checker over the transported bytes — is W9.5's boundary,
    not this theorem's.) -/
theorem SchemaObligation.discharge_guestVerified_sound (o : SchemaObligation)
    (wr : SchemaObligation.WitnessRef) (ht : o.tier = .guestVerified)
    (h : (o.discharge (some wr)).isSome = true) :
    WitnessCheck.WHolds wr.witness.claim wr.ctx.row wr.ctx.log := by
  rw [o.discharge_guestVerified_eq ht] at h
  dsimp only at h
  split at h
  · next hc =>
      rw [Bool.and_eq_true] at hc
      exact WitnessCheck.checkWitnessArtifact_sound _ _ hc.2
  · simp at h

/-- The backend FIRES on an accepted certificate (the tier's `isSome`
    is not vacuous): label agreement + an accepting check at the
    certificate's own fuel yields the `.guestWitness` evidence naming
    the artifact and the certified label. -/
theorem SchemaObligation.discharge_guestVerified_of_accept (o : SchemaObligation)
    (wr : SchemaObligation.WitnessRef) (ht : o.tier = .guestVerified)
    (hlabel : wr.witness.label = o.label)
    (hcheck : WitnessCheck.checkWitnessArtifact wr.witness wr.ctx = true) :
    o.discharge (some wr) =
      some (.guestWitness wr.artifact wr.witness.label) := by
  rw [o.discharge_guestVerified_eq ht]
  dsimp only
  have hc : (wr.witness.label == o.label &&
      WitnessCheck.checkWitnessArtifact wr.witness wr.ctx) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hlabel, hcheck⟩
  rw [if_pos hc]

/-- SOUNDNESS of the decidableNow backend: a `.decided true` verdict
    on a decidableNow-tier obligation means the claim HOLDS — the
    kernel's `decide` validated the registered predicate on the
    all-default row (`of_decide_eq_true`; no new trust base, no
    fabricated evidence). -/
theorem SchemaObligation.discharge_decidableNow_sound (o : SchemaObligation)
    (ht : o.tier = .decidableNow)
    (h : o.discharge = some (.decided true)) : o.decidableClaim := by
  unfold SchemaObligation.discharge at h
  rw [ht] at h
  cases hd : decide o.decidableClaim with
  | true => exact of_decide_eq_true hd
  | false =>
      rw [hd] at h
      simp at h

/-- COMPLETENESS of the decidableNow backend: a true claim discharges
    to the `.decided true` evidence — the backend FIRES on the claims
    it can decide (the tier's `isSome` is not vacuous). -/
theorem SchemaObligation.discharge_decidableNow_of_claim (o : SchemaObligation)
    (ht : o.tier = .decidableNow) (h : o.decidableClaim) :
    o.discharge = some (.decided true) := by
  unfold SchemaObligation.discharge
  rw [ht, decide_eq_true h]

/-- Computed-tier obligations ALWAYS discharge: a tier computed by
    `tierOf` from the row's own citation can name its evidence, and
    (W9.3's disjunct — design §3) a guestVerified row backed by a
    PROVIDED witness whose label matches and whose certificate CHECKS
    at its shipped fuel fires too. The "armed but unfired" pattern is
    unrepresentable for registered rows (the `schema_invariant`
    command computes the tier — Reflect.lean); for the fifth tier the
    hypothesis IS the witness-backed assignment (registration carrying
    the witness spec is W9.4 — the disjunct's right side is what its
    registrations will satisfy). -/
theorem SchemaObligation.discharge_isSome_of_computed (o : SchemaObligation)
    (w : Option SchemaObligation.WitnessRef)
    (h : o.tier = (tierOf o.payload.proofName).toObligationTier
      ∨ (o.tier = .guestVerified ∧ ∃ wr, w = some wr
          ∧ wr.witness.label = o.label
          ∧ WitnessCheck.checkWitnessArtifact wr.witness wr.ctx = true)) :
    (o.discharge w).isSome = true := by
  cases h with
  | inl h =>
      cases hp : o.payload.proofName with
      | none =>
          rw [hp] at h
          unfold SchemaObligation.discharge
          rw [h]
          rfl
      | some pn =>
          rw [hp] at h
          unfold SchemaObligation.discharge
          rw [h, hp]
          rfl
  | inr h =>
      obtain ⟨ht, wr, hw, hlabel, hcheck⟩ := h
      rw [hw, o.discharge_guestVerified_of_accept wr ht hlabel hcheck]
      rfl

end SchemaLang

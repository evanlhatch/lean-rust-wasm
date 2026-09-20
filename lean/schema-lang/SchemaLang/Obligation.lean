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

1. `InvariantItem.witnessRef` and the invariant lane's `guestVerified`
   rung computation are
   NOT landed: the tier value exists (the kit's rung — `SchemaLang.Tier`
   IS the kit's tier), but no invariant-lane computation produces it. The witness reaches
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
universal closure); the oracle backend's RESOLUTION half (the gates
driver's `obligation-check` — the row universe lives in wasm-backend,
cross-package by construction; here only well-formedness is
checkable); updates/machines as obligations (later phases); witness
generation (W9.4) and the guest-side re-check (W9.5) — the boundary
halves named above. The oracle ref's naming convention is the demo
world's record-named exports (`user-valid` for `User`): a ref for an
invariant over a record with no record-named export (e.g. the
`order-error-valid` variant export) has no convention yet — it cannot
discharge (loud), the first consumer's to land with registration.

W9.x (the LAST rung wired): the oracleSwept arm discharges on a
WELL-FORMED row reference (non-empty, naming the payload's record —
the lightest honest check available HERE: schema-lang cannot see the
oracle's row universe). RESOLUTION — the ref names an ACTUAL oracle
row — is the gates driver's `obligation-check` (lean/gates), the
cross-package half: the gates exe loads both environments, so a
claimed-but-dangling ref fails CI. The ref is evidence of a SWEEP,
not a proof — nothing here claims oracle rows prove anything.
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

/-- The obligation VIEW of a registered invariant (additive — the item
    is unchanged; emitters keep reading the item, the byte-tie holds).
    The tier needs NO mapping: `SchemaLang.Tier` IS the kit's tier (the
    abbrev pin in Invariant.lean) — the item's tier rides across
    verbatim. Provenance is the name as a declaration key: W7.5's
    provenance extension covers `Item`s, not invariant rows (the
    follow-up). -/
def InvariantItem.obligation (it : InvariantItem) : SchemaObligation :=
  { label := it.name
  , tier := it.tier
  , payload := it
  , provenance := it.name.toName }

/-- The view's tier IS the item's tier (one ladder — the alias). -/
theorem InvariantItem.obligation_tier (it : InvariantItem) :
    it.obligation.tier = it.tier := rfl

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

/-! ## The oracleSwept backend (the ladder's last rung, W9.x) -/

/-- ASCII case fold, kernel-reducible (Char.toLower's map is wf-recursive
    — kernel-OPAQUE, the W8.3 trap: decide/rfl over it can never reduce;
    the well-formedness predicate below must decide in the kernel for
    the discharge pins). Registry names are idents — ASCII by
    construction. -/
def SchemaObligation.charToLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- The oracle row REFERENCE's well-formedness — the schema-lang half
    of the oracleSwept discharge (the lightest honest check available
    HERE: this package cannot see wasm-backend's row universe). The
    ref names the oracle fn the sweep replays; "concerns the payload"
    = the fn-name begins with the payload's record's name, ASCII
    case-folded, then `-` (the demo world's export naming convention:
    `user-valid` for `User`). Non-empty + the prefix — nothing more is
    checkable without the oracle's rows; RESOLUTION (an actual row
    replays that fn) is the gates driver's `obligation-check`, and a
    well-formed-but-DANGLING ref that fires here fails THERE (the
    armed-and-FIRED gate). Deliberate exclusion: multi-word record
    names fold WITHOUT word boundaries (`OrderItem` → `orderitem-`),
    so the `order-error-valid`-family exports have no convention yet —
    such refs cannot discharge (loud), the first consumer's to land
    with registration. -/
def SchemaObligation.oracleRefWellFormed (o : SchemaObligation)
    (ref : String) : Bool :=
  ref != "" &&
    ((o.payload.schemaRef.toList.map SchemaObligation.charToLower)
      ++ ['-']).isPrefixOf ref.toList

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
    `decidableClaim` (WIRED — phase 2, the KIT's verdict combinator
    `decideEvidence`); a guestVerified row's evidence
    is the PROVIDED witness, fired ONLY when the certificate's label
    IS the obligation's AND W9.2's checker accepts the certificate at
    its own shipped fuel (W9.3 — the host half; the soundness theorem
    below cites `checkWitnessArtifact_sound`); an oracleSwept row's
    evidence is the PROVIDED row reference, fired ONLY when it is
    well-formed (`oracleRefWellFormed` above — the sweep-evidence
    half; resolution against the oracle's actual rows is the gates
    driver's `obligation-check`). `none` = the loud gap:
    a proved-tier claim with no citation (a hand-set tier, since the
    registration computes it), a FALSE decide verdict, a default-less
    record, an `oracleSwept` claim with NO ref or an ILL-FORMED one
    (empty, or naming a fn the payload's record does not concern — a
    well-formed-but-DANGLING ref fires here and is caught by the
    gates driver's `obligation-check`), a guestVerified row with no
    provided witness / a label mismatch / a REFUSED check (tampered
    certificate, insufficient fuel — exhaustion is refusal, owner
    decision 2) — discharge refuses, it does not fabricate evidence. -/
def SchemaObligation.discharge (o : SchemaObligation)
    (w : Option SchemaObligation.WitnessRef := none)
    (oracleRef : Option String := none) :
    Option CodegenCore.Obligation.Evidence :=
  match o.tier with
  | .provedAtElab => o.payload.proofName.map .citedProof
  | .generatedCheck =>
      some (.generatedCheck (Emit.Invariant.invariantEmitter.outputs.head!)
        (Emit.Invariant.checkFnName o.payload))
  | .decidableNow => CodegenCore.Obligation.decideEvidence o.decidableClaim
  | .oracleSwept =>
      match oracleRef with
      | some ref =>
          if SchemaObligation.oracleRefWellFormed o ref then
            some (.oracleRow ref)
          else none
      | none => none
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
    (ht : o.tier = .guestVerified) (w : Option SchemaObligation.WitnessRef)
    (oracleRef : Option String) :
    o.discharge w oracleRef =
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
    (hcheck : WitnessCheck.checkWitnessArtifact wr.witness wr.ctx = true)
    (oracleRef : Option String) :
    o.discharge (some wr) oracleRef =
      some (.guestWitness wr.artifact wr.witness.label) := by
  rw [o.discharge_guestVerified_eq ht]
  dsimp only
  have hc : (wr.witness.label == o.label &&
      WitnessCheck.checkWitnessArtifact wr.witness wr.ctx) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hlabel, hcheck⟩
  rw [if_pos hc]

/-- The oracleSwept arm, as an equation (the proofs below rewrite
    with it instead of re-splitting the discharge's match; the
    `guestVerified` shape — same discipline). -/
theorem SchemaObligation.discharge_oracleSwept_eq (o : SchemaObligation)
    (ht : o.tier = .oracleSwept) (w : Option SchemaObligation.WitnessRef)
    (oracleRef : Option String) :
    o.discharge w oracleRef =
      (match oracleRef with
       | some ref =>
           if SchemaObligation.oracleRefWellFormed o ref then
             some (.oracleRow ref)
           else none
       | none => none) := by
  unfold SchemaObligation.discharge
  rw [ht]

/-- SOUNDNESS of the oracleSwept backend: a FIRED discharge means the
    reference was WELL-FORMED — non-empty and naming a fn the payload's
    record concerns (`oracleRefWellFormed`, the schema-lang half).
    This is the WHOLE claim the ref supports HERE: an oracle row is
    evidence of a SWEEP, not a proof — the soundness content is that
    discharge never fabricates sweep evidence from a ref the payload
    does not concern. Resolution against the oracle's actual rows is
    the gates driver's `obligation-check` (the cross-package half). -/
theorem SchemaObligation.discharge_oracleSwept_sound (o : SchemaObligation)
    (ref : String) (ht : o.tier = .oracleSwept)
    (h : (o.discharge none (some ref)).isSome = true) :
    (ref != "" &&
      ((o.payload.schemaRef.toList.map SchemaObligation.charToLower)
        ++ ['-']).isPrefixOf ref.toList) = true := by
  rw [o.discharge_oracleSwept_eq ht] at h
  dsimp only at h
  split at h
  · next hwf => exact hwf
  · simp at h

/-- COMPLETENESS of the oracleSwept backend: a well-formed reference
    FIRES the backend (the tier's `isSome` is not vacuous — the same
    obligation that refuses an ill-formed ref accepts this one). -/
theorem SchemaObligation.discharge_oracleSwept_of_ref (o : SchemaObligation)
    (ref : String) (ht : o.tier = .oracleSwept)
    (hw : SchemaObligation.oracleRefWellFormed o ref = true)
    (w : Option SchemaObligation.WitnessRef := none) :
    o.discharge w (some ref) = some (.oracleRow ref) := by
  rw [o.discharge_oracleSwept_eq ht]
  dsimp only
  rw [if_pos hw]

/-- SOUNDNESS of the decidableNow backend: a `.decided true` verdict
    on a decidableNow-tier obligation means the claim HOLDS — the
    kernel's `decide` validated the registered predicate on the
    all-default row (`of_decide_eq_true`; no new trust base, no
    fabricated evidence). Routes through the kit's
    `decideEvidence_sound` — the proof object is shared. -/
theorem SchemaObligation.discharge_decidableNow_sound (o : SchemaObligation)
    (ht : o.tier = .decidableNow)
    (h : o.discharge = some (.decided true)) : o.decidableClaim := by
  unfold SchemaObligation.discharge at h
  rw [ht] at h
  exact CodegenCore.Obligation.decideEvidence_sound h

/-- COMPLETENESS of the decidableNow backend: a true claim discharges
    to the `.decided true` evidence — the backend FIRES on the claims
    it can decide (the tier's `isSome` is not vacuous). -/
theorem SchemaObligation.discharge_decidableNow_of_claim (o : SchemaObligation)
    (ht : o.tier = .decidableNow) (h : o.decidableClaim) :
    o.discharge = some (.decided true) := by
  unfold SchemaObligation.discharge
  rw [ht]
  exact CodegenCore.Obligation.decideEvidence_of_claim h

/-- Computed-tier obligations ALWAYS discharge: a tier computed by
    `tierOf` from the row's own citation can name its evidence; a
    guestVerified row backed by a PROVIDED witness whose label matches
    and whose certificate CHECKS at its shipped fuel fires too (W9.3's
    disjunct — design §3); and (W9.x's disjunct — the last rung) an
    oracleSwept row backed by a well-formed row reference fires too.
    The "armed but unfired" pattern is unrepresentable for registered
    rows with their backends' inputs provided (the `schema_invariant`
    command computes the tier — Reflect.lean; the fifth tier is
    hand-assigned and witness-backed per the middle disjunct; the
    oracle tier is hand-assigned and ref-backed per the last). The
    resolution half — ref ↔ actual oracle row — is deliberately NOT
    here (schema-lang cannot see the row universe; the gates driver's
    `obligation-check` owns it). -/
theorem SchemaObligation.discharge_isSome_of_computed (o : SchemaObligation)
    (w : Option SchemaObligation.WitnessRef) (oracleRef : Option String)
    (h : o.tier = tierOf o.payload.proofName
      ∨ (o.tier = .guestVerified ∧ ∃ wr, w = some wr
          ∧ wr.witness.label = o.label
          ∧ WitnessCheck.checkWitnessArtifact wr.witness wr.ctx = true)
      ∨ (o.tier = .oracleSwept ∧ ∃ ref, oracleRef = some ref
          ∧ SchemaObligation.oracleRefWellFormed o ref = true)) :
    (o.discharge w oracleRef).isSome = true := by
  rcases h with h | h | h
  · cases hp : o.payload.proofName with
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
  · obtain ⟨ht, wr, hw, hlabel, hcheck⟩ := h
    rw [hw, o.discharge_guestVerified_of_accept wr ht hlabel hcheck oracleRef]
    rfl
  · obtain ⟨ht, ref, href, hwf⟩ := h
    rw [href, o.discharge_oracleSwept_of_ref ref ht hwf w]
    rfl

end SchemaLang

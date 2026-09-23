/-
# SchemaLang.WitnessSpec — the guestVerified witness REGISTRY row (W9.4 glue)

The fifth tier's registration data (notes/design-guest-verified.md §4
step 1's input): ONE row per `guestVerified`-tier obligation. The row
carries exactly what witness generation needs and nothing more:

- `label` — the obligation's label (pinned against
  `SchemaObligation.label` at discharge — the mis-wire check);
- `artifact` — the artifact name the discharge's `.guestWitness`
  evidence names (design §3's `Evidence.guestWitness artifact ref`);
- `claim` — the certified proposition in W9.1's mini-language
  (`Witness.WProp` — v1 scope: VExpr-`.bool` invariants + the
  migration-chain rule, owner decision 4);
- `ctx` — the decoded context the claim is certified against (W9.2's
  `RowValsP`: the record's field list + the row + the chain lane's log
  segment at the SAME field list).

This module is deliberately data-only (the codec is W9.1's, the
checker W9.2's, the discharge W9.3's). GENERATION (proof-term
construction, fuel sizing, the emission-time self-check, the byte-tied
artifact) is `SchemaLang.Emit.Witness`. Registration is currently
plain spec-module data (`Demo.demoWitnesses`, the
`registeredMigrations` precedent — the authoring surface carries the
spec rows and the driver reads the module it already imports); an
env-extension lane (`invariantItemExt`'s shape) is the follow-up when
a SECOND package registers witnesses — the GenCtx v2 contract's
dogfood lesson, applied at the first real need rather than before it.

Deliberate exclusions: the guest-side re-check (W9.5/W9.6), the
`Invariant.Tier.guestVerified` rung + `witnessRef` field (W9.3's
recorded deviation — the witness reaches discharge as an explicit
argument), per-event envelopes (design §7.2: v1 is per-SEGMENT).
-/

module

public import SchemaLang.WitnessCheck

@[expose] public section

namespace SchemaLang

/-- One witness registry row (design §4: "for record `R`, migration
    `m`, invariant `inv`" — the record and migration identities enter
    through `ctx.fs`'s surface, which the emitter hashes into the
    envelope fingerprint; the obligation's evidence names `artifact`). -/
structure WitnessSpec where
  /-- The obligation's label (the discharge's label pin). -/
  label : String
  /-- The artifact name the fired `.guestWitness` evidence cites
      (design §4's `witnesses/<record>-v<from>-v<to>.wtn`). -/
  artifact : String
  /-- The claim, in W9.1's mini-language. -/
  claim : Witness.WProp
  /-- The decoded context: the field list, the certified row, the
      chain lane's log segment. -/
  ctx : WitnessCheck.RowValsP

end SchemaLang

end -- @[expose] public section

/-
# TestKit.Obllane — the obligation-lane discharge kit

Every lane's `*_sound` / `*_of_claim` pair repeats ONE proof body: the
discharge is the kit's decidableNow backend at the obligation's tier
(`CodegenCore.Obligation.decideEvidence` after the lane's own
dispatch), so SOUNDNESS = a `.decided true` verdict means the claim
holds, COMPLETENESS = a true claim fires the backend — both PROVED ONCE
in CodegenCore (`decideEvidence_sound` / `decideEvidence_of_claim`).
The lanes' theorem NAMES are the contract (pinned by
Tests/Axioms.lean); the BODIES are routing — unfold the lane's
`discharge`, rewrite the tier, route.

```lean
theorem SchemaObligation.discharge_decidableNow_sound (o : SchemaObligation)
    (ht : o.tier = .decidableNow)
    (h : o.discharge = some (.decided true)) : o.decidableClaim :=
  Obllane.decidableNow_sound (by simp [SchemaObligation.discharge, ht]) h
```

The two builders below ARE the pair body, once: `decidableNow_sound`
(soundness — the body's first half) and `decidableNow_of_claim`
(completeness — the second half). A lane writes its discharge def-eq
(`by simp [Lane.discharge, ht]` — the site-specific part) and its
verdict hypothesis; the proof object is shared, no new trust base.

The tier-GATED lanes (`EntityMachine`, `Keys`, `Update2`, `Refine` —
discharge = `Obligation.decideDischarge claim o`) already route
ONE-LINERS straight into `CodegenCore.Obligation.decideDischarge_sound
_ _ ht h` — the kit offers nothing shorter; those stay untouched (and
`Refine`'s `RangeCheck` routes into `decideEvidence_sound` directly).
The two thesesions of this module: the multi-arm-dispatch lanes whose
bodies needed the unfold+rw dance (SchemaObligation, PrePostObligation,
TableObligation).

Deliberate exclusions: no tactic API (the hygiene trap — quoted tactic
bodies cannot NAME the lane's hypotheses); the builders are THEOREMS,
the lane bodies are sites with literal names. No axiom surface — the
builders route through CodegenCore's proved backend. Owner:
TestKit.Obllane; consumers: the schema-lang obligation lanes.
-/

module

public import Lean
public import CodegenCore.Kit

@[expose] public section

namespace TestKit.Obllane

open CodegenCore

/-- SOUNDNESS of the decidableNow rung, at the lane's own discharge.
    `hdef` is the lane's discharge def-eq at the rung
    (`dim = decideEvidence claim` — the site's `by simp [Lane.discharge,
    ht]` writes it); `hv` the fired `.decided true` verdict. Routes
    through `CodegenCore.Obligation.decideEvidence_sound` — the proof
    object is shared. -/
theorem decidableNow_sound {claim : Prop} [Decidable claim]
    {dim : Option CodegenCore.Obligation.Evidence}
    (hdef : dim = CodegenCore.Obligation.decideEvidence claim)
    (hv : dim = some (CodegenCore.Obligation.Evidence.decided true)) : claim := by
  rw [hdef] at hv
  exact CodegenCore.Obligation.decideEvidence_sound hv

/-- COMPLETENESS of the decidableNow rung, at the lane's own discharge:
    a true claim fires the backend to the `.decided true` evidence
    (the tier's `isSome` is not vacuous). Routes through
    `CodegenCore.Obligation.decideEvidence_of_claim`. -/
theorem decidableNow_of_claim {claim : Prop} [Decidable claim]
    {dim : Option CodegenCore.Obligation.Evidence}
    (hdef : dim = CodegenCore.Obligation.decideEvidence claim) (hc : claim) :
    dim = some (CodegenCore.Obligation.Evidence.decided true) := by
  rw [hdef]
  exact CodegenCore.Obligation.decideEvidence_of_claim hc

end TestKit.Obllane

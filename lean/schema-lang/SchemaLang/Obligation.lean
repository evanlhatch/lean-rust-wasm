/-
# SchemaLang.Obligation — schema-level obligations (W7.1 phase 1)

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
computed-tier obligations always discharge.

Ownership: the obligation lane (this module + CodegenCore.Kit's
Obligation). Deliberate exclusions: assumptions (no consumer — phase
2); the decide backend (no invariant is decide-shaped); the oracle
backend (`Tier.oracleCovered` is a closed ctor until its first
consumer lands); updates/machines as obligations (later phases).
-/

module

public import CodegenCore
public import SchemaLang.Emit.Invariant

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
    source — invariants execute on rows, they are not closed props. -/
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

/-- THE DISCHARGE (phase 1: the invariant lane's two wired backends).
    A proved row's evidence is its citation (resolved at registration
    — `checkCitation?`); a boundary row's evidence is the emitted
    check fn in the emitter's declared output. `none` = the loud gap
    (a proved-tier claim with no citation — a hand-set tier, since the
    registration computes it). `decidableNow`/`oracleSwept` have no
    invariant-lane backend yet: `none`, loudly. -/
def SchemaObligation.discharge (o : SchemaObligation) :
    Option CodegenCore.Obligation.Evidence :=
  match o.tier with
  | .provedAtElab => o.payload.proofName.map .citedProof
  | .generatedCheck =>
      some (.generatedCheck (Emit.Invariant.invariantEmitter.outputs.head!)
        (Emit.Invariant.checkFnName o.payload))
  | .decidableNow => none
  | .oracleSwept => none

/-- Computed-tier obligations ALWAYS discharge: a tier computed by
    `tierOf` from the row's own citation can name its evidence. The
    "armed but unfired" pattern is unrepresentable for registered rows
    (the `schema_invariant` command computes the tier — Reflect.lean). -/
theorem SchemaObligation.discharge_isSome_of_computed (o : SchemaObligation)
    (h : o.tier = (tierOf o.payload.proofName).toObligationTier) :
    o.discharge.isSome = true := by
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

end SchemaLang

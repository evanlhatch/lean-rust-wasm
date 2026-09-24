/- # Kit.Derive.Evidence — the evidence-kind computation (16-surface §3's
# evidence entourage)

Every declaration's evidence cone is GENERATED, and the generator's
first question is "does the type already carry it?" (16-surface §3):

1. in the type (unrepresentable) → NO artifact (construction IS the
   evidence — a generated proof of it is waste: the census finding);
2. decidable over a closed space → the kernel proof (`decide`/`cases`),
   never a sweep;
3. unbounded → the LCG sweep + the mandatory controls + the shrinker;
4. behavioral → the duel rows (tested agreement, tier-honest).

THIS module makes the tier a COMPUTATION, not a label: the kind is
computed from the capability + the carrier's shape, and the tier rides
the kind (`EvidenceKind.tier!`) — the machinery cannot mislabel (a
sweep reports `oracleSwept`, never `provedAtElab`:
`EvidenceKind.tier_ne_provedAtElab`). The entourage's PER-CAPABILITY
emissions are DATA too (`emissions`) — a handler that renders the list
cannot invent an artifact the kind does not demand, and a carried fact
renders `[]` (the census discipline, `emissions_carried`).

The deriving handlers that consume this computation live in
SchemaCore.DeriveMeta (the WireCodec + row_bridge mounts); the lane
substrate's registration hooks (Kit.Lane) fill the ledger's demand face
from the SAME discipline (the lane records the collections it reads).

Core-only (imports Kit.Obligation — the cone rule).

The five questions (notes/v3/01-core.md):
- root: none — the evidence discipline's DATA layer over the deriving
  surface (the entourage's closed vocabulary + the computation).
- carrier grade: the mislabeling is UNREPRESENTABLE — the tier is a
  function of the kind, the emissions a function of the shape; there is
  no tier field to hand-set (a discharge whose evidence's tier differs
  from the computed row tier fails `Discharged`'s construction).
- spine reading: the derivation stage's evidence face — `Descr` →
  capability → emissions (kind-routed).
- ladder rung: rung 1-2 — closed enums + total folds; the honesty
  theorems are `rfl`/cases.
- gate row: KitTests' evidence suite (the computed-kind pins + the
  census + the mislabel controls) + SchemaTests' entourage suite (the
  full cone arriving with a derived capability).
-/

import Kit.Obligation

namespace Kit.Derive.Evidence

/-! ## The closed vocabularies -/

/-- The deriving capabilities the entourage serves (closed — a new
    handler extends this deliberately, the DeriveMeta mount's own
    capability name). -/
inductive DerivCap where
  | wireCodec
  | rowBridge
deriving Repr, BEq, DecidableEq, Inhabited

/-- The capability's rendering (test pins + emitted labels). -/
def DerivCap.render : DerivCap → String
  | .wireCodec => "wire-codec"
  | .rowBridge => "row-bridge"

/-- The carrier's shape, as the generator reads it (the closed four
    the evidence kinds partition). -/
inductive CarrierShape where
  /-- The type's construction guarantees it (the round trips ARE the
      `Kit.Iso` law fields) — the entourage generates NOTHING. -/
  | carried
  /-- Decidable over a closed space — the kernel decides. -/
  | closedFinite
  /-- Unbounded — the LCG sweep's world. -/
  | unbounded
  /-- Behavioral — the duel rows (tested agreement). -/
  | behavioral
deriving Repr, BEq, DecidableEq, Inhabited

/-- THE EVIDENCE KIND (16-surface §3's four answers, closed). -/
inductive EvidenceKind where
  /-- In the type — NO artifact (the census: a generated proof of it
      is waste). -/
  | typeCarried
  /-- The kernel proof over a closed space. -/
  | kernelDecide
  /-- The LCG sweep + the mandatory controls. -/
  | lgcSweep
  /-- The duel rows (tested agreement). -/
  | duel
deriving Repr, BEq, DecidableEq, Inhabited

/-- The kind's tier, as an OPTION: `none` for the type-carried kind —
    there is NO artifact, hence no tier to report (asking for one is
    the census finding, `emissions_tier_exists`'s face). -/
def EvidenceKind.tier : EvidenceKind → Option Kit.Tier
  | .typeCarried => none
  | .kernelDecide => some .decidableNow
  | .lgcSweep => some .oracleSwept
  | .duel => some .generatedCheck

/-- The tier for an EMITTED obligation row: the row exists only where
    the kind demands one (the census refuses the carried kind first),
    so the `typeCarried` arm is UNREACHABLE at every emission site —
    the handler's guard (`emissions_obligation_iff`) is the proof. -/
def EvidenceKind.tier! : EvidenceKind → Kit.Tier
  | .typeCarried => .decidableNow
  | .kernelDecide => .decidableNow
  | .lgcSweep => .oracleSwept
  | .duel => .generatedCheck

/-- The two tier faces AGREE wherever the row exists: for every
    NON-carried kind, `tier!` is exactly the `some` payload of `tier`
    (the emission sites' census guard is what makes this honest). The
    carried kind has NO tier — `tier!` is unreachable there. -/
theorem EvidenceKind.tier_matches (k : EvidenceKind) (h : k ≠ .typeCarried) :
    k.tier = some k.tier! := by
  cases k with
  | typeCarried => exact absurd rfl h
  | kernelDecide => rfl
  | lgcSweep => rfl
  | duel => rfl

/-- THE TIER-HONESTY THEOREM: no evidence kind yields `provedAtElab` —
    a sweep reports `oracleSwept`, never `provedAtElab`; the kernel's
    closed-space face reports `decidableNow`. The machinery CANNOT
    mislabel, because there is no hand-set tier anywhere in the cone. -/
theorem EvidenceKind.tier_ne_provedAtElab (k : EvidenceKind) :
    k.tier ≠ some .provedAtElab := by cases k <;> simp [tier]

/-! ## THE COMPUTATION — kind from capability + carrier shape -/

/-- The shape's kind (the computation's spine — a total fold over the
    closed shape set). -/
def evidenceKindOfShape : CarrierShape → EvidenceKind
  | .carried => .typeCarried
  | .closedFinite => .kernelDecide
  | .unbounded => .lgcSweep
  | .behavioral => .duel

/-- Each capability's own carrier shape — the handler's DECLARED
    reading (the capability refines which shape its claim lives at):
    the wire codec's carrier (the record's values over the wire) is
    UNBOUNDED — the sweep's world; the row bridge's round trips are the
    `Kit.Iso` law FIELDS — type-carried (the census applies). -/
def shapeOf : DerivCap → CarrierShape
  | .wireCodec => .unbounded
  | .rowBridge => .carried

/-- THE COMPUTATION: the evidence kind from the capability + the
    carrier's shape. Total over the closed pair of enums — the honest
    totality is the match's exhaustiveness (the compiler drives it).
    The capability enters through its DECLARED shape reading
    (`shapeOf`) — the composed face is `evidenceKindOf`; this raw face
    keeps the shape argument explicit for the census theorems. -/
def evidenceKind (_cap : DerivCap) (shape : CarrierShape) : EvidenceKind :=
  evidenceKindOfShape shape

/-- The capability's own kind (the composed face the emission sites
    use). -/
def evidenceKindOf (cap : DerivCap) : EvidenceKind :=
  evidenceKind cap (shapeOf cap)

/-- The generator's FIRST QUESTION, answered as data: does the type
    already carry it? -/
def typeCarries (cap : DerivCap) : Bool :=
  shapeOf cap == .carried

/-! ## The emissions — the entourage's per-capability face, as DATA -/

/-- One emission face of the entourage (closed — a new artifact kind
    extends this deliberately, naming its 16-surface §3 slot). -/
inductive Emission where
  /-- The Prop-indexed obligation row, tier COMPUTED from the kind. -/
  | obligationRow
  /-- The LCG sweep + the mechanical controls (the test entourage). -/
  | sweepControls
  /-- The duel rows (the behavioral face). -/
  | duelRows
  /-- The named simp-set registration of the generated laws. -/
  | simpSet
deriving Repr, BEq, DecidableEq, Inhabited

/-- The emission's rendering (test pins + emitted comments). -/
def Emission.render : Emission → String
  | .obligationRow => "obligation-row"
  | .sweepControls => "sweep-controls"
  | .duelRows => "duel-rows"
  | .simpSet => "simp-set"

/-- THE ENTOURAGE, as data: what a handler emits per capability and
    carrier shape. The carried row is EMPTY — a type-carried fact
    generates NOTHING (the census discipline; a generated proof of it
    is the redundancy finding, same as dead code). A handler that
    renders this list cannot invent an artifact the kind does not
    demand. -/
def emissions : DerivCap → CarrierShape → List Emission
  | _, .carried => []
  | _, .closedFinite => [.obligationRow, .simpSet]
  | _, .unbounded => [.obligationRow, .sweepControls, .simpSet]
  | _, .behavioral => [.obligationRow, .duelRows, .simpSet]

/-- The capability's own emissions (the composed face). -/
def emissionsOf (cap : DerivCap) : List Emission :=
  emissions cap (shapeOf cap)

/-- THE CENSUS THEOREM: a carried fact's emission list is empty — the
    entourage's first question is answered by the DATA, and the answer
    is enforced on every handler that renders `emissions`. -/
theorem emissions_carried (cap : DerivCap) :
    emissions cap .carried = [] := rfl

/-- An obligation row is emitted iff the shape is NOT carried — the row
    exists only where a tier exists (a tier over `none` is not a row,
    it is the census finding). -/
theorem emissions_obligation_iff (cap : DerivCap) (shape : CarrierShape) :
    ((emissions cap shape).contains .obligationRow) = (shape != .carried) := by
  cases cap <;> cases shape <;> simp [emissions] <;> rfl

/-- Every emitted obligation's tier EXISTS: where the row is emitted,
    the kind's `tier` is `some` (the census face of the tier honesty —
    the machinery cannot emit a tierless row). -/
theorem emissions_tier_exists (cap : DerivCap) (shape : CarrierShape)
    (h : (emissions cap shape).contains .obligationRow) :
    (evidenceKind cap shape).tier.isSome := by
  cases cap <;> cases shape <;> simp_all [emissions, evidenceKind,
    evidenceKindOfShape, EvidenceKind.tier]

/-! ## The mechanical control shapes -/

/-- The mechanical sabotage-control rows per carrier shape (the
    generated suites' mandatory controls — the suites render THESE
    shapes, never hand-invented placeholders). The codec's
    truncation/empty-tape refusals and the checker's vacuity traps are
    MECHANICAL — a capability's handler renders them; it never invents
    a control shape. -/
def mechanicalControls : CarrierShape → List String
  | .carried => []
  | .closedFinite =>
      ["sabotage: the naming fn drops the name"
      , "sabotage: the entry drifts"]
  | .unbounded =>
      ["sabotage: the decoder accepts the truncated encoding"
      , "sabotage: the decoder accepts the empty tape"]
  | .behavioral =>
      ["sabotage: the duel sides tie on drift"
      , "sabotage: the duel refuses the agreed vector"]

/-- The carried shape's controls are EMPTY — no sweep, no controls, no
    suite rows (the census, at the controls' face). -/
theorem mechanicalControls_carried : mechanicalControls .carried = [] := rfl

/-- The closed-finite shape's control count (the scaffold's suites take
    TWO mandatory controls from this data — the subtype's arithmetic
    rides this pin). -/
theorem mechanicalControls_closedFinite_two :
    (mechanicalControls .closedFinite).length == 2 := rfl

end Kit.Derive.Evidence

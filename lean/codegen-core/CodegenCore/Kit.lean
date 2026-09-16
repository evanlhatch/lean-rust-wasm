/-
# CodegenCore.Kit — the correspondence kit

The agreement-theorem vocabulary (lean-cohesion-plan §0): laws attach to
SHAPES, not instances. Moved from Machines.Foundations (the Dag STAYS there).
-/
module

@[expose] public section

namespace CodegenCore

/-- True bijection. Rare, precious. (`to`/`inv`, not `to`/`from`:
    `from` is a reserved token in Lean 4.) -/
structure Iso (A B : Type) where
  to : A → B
  inv : B → A
  to_inv : ∀ b, to (inv b) = b
  inv_to : ∀ a, inv (to a) = a

/-- Partial correspondence: decode may fail; encode is a section.
    The law is one-ended (`decode∘encode = id`): the wire may have
    non-canonical encodings, but everything we emit decodes back. -/
structure PartialIso (A B : Type) where
  decode : A → Option B
  encode : B → A
  decode_encode : ∀ b, decode (encode b) = some b

/-- Abstraction: the representation determines its semantics (`outParam`).
    No inverse exists; the law lives on operations (`ReprOp`). -/
class Denotes (R : Type) (A : outParam Type) where
  abs : R → A

/-- A representation-respecting operation: the commuting square
    `abs(opR r) = opA (abs r)`. One per operation that moves through
    the representation; each is a theorem shape for primitives and a
    generated differential test for composed paths. -/
structure ReprOp (R A : Type) [Denotes R A] where
  opR : R → R
  opA : A → A
  respects : ∀ r, Denotes.abs (opR r) = opA (Denotes.abs r)

namespace ReprOp

variable [Denotes R A]

/-- Vertical composition of squares: if both commute, the composite commutes. -/
def comp (o₁ o₂ : ReprOp R A) : ReprOp R A where
  opR := o₁.opR ∘ o₂.opR
  opA := o₁.opA ∘ o₂.opA
  respects := fun r => by
    show Denotes.abs (o₁.opR (o₂.opR r)) = o₁.opA (o₂.opA (Denotes.abs r))
    rw [o₁.respects, o₂.respects]

/-- The identity square. -/
def id : ReprOp R A where
  opR := _root_.id; opA := _root_.id
  respects := fun _ => rfl

end ReprOp

/-- The completeness half of a `CheckedProp`, as DATA. `missing` is the
    loud, greppable declaration "this gate is one-directional — the checker
    may reject valid inputs". (The `Option (complete proof)` shape was the
    first design; `Option : Type → Type` cannot carry a Prop without a
    `PLift` wrapper, and that noise at every construction site is worse
    than a two-constructor inductive.) -/
inductive CheckedProp.Completeness {α : Type} (P : α → Prop) (check : α → Bool) : Type where
  | missing : Completeness P check
  | proved : (∀ a, P a → check a = true) → Completeness P check

/-- A proposition with an executable checker. Soundness is mandatory — a
    `true` verdict is a proof. Completeness is a constructor choice with NO
    default: every construction must write `.proved h` or `.missing`, so a
    one-directional gate is declared, never implied. `ofComplete` is the
    both-ways constructor; `isComplete` is the loud flag. -/
structure CheckedProp (α : Type) where
  P : α → Prop
  check : α → Bool
  sound : ∀ a, check a = true → P a
  complete? : CheckedProp.Completeness P check

namespace CheckedProp

/-- Both-ways construction: the common case. -/
def ofComplete (P : α → Prop) (check : α → Bool)
    (sound : ∀ a, check a = true → P a) (complete : ∀ a, P a → check a = true) :
    CheckedProp α :=
  ⟨P, check, sound, .proved complete⟩

/-- The verdict decides the proposition when completeness is present. -/
theorem check_iff (c : CheckedProp α) (h : ∀ a, c.P a → c.check a = true) (a : α) :
    c.check a = true ↔ c.P a :=
  ⟨c.sound a, h a⟩

/-- Loud completeness flag: `false` means soundness-only. -/
def isComplete (c : CheckedProp α) : Bool :=
  match c.complete? with
  | .missing => false
  | .proved _ => true

end CheckedProp

/-! ## Obligation — every checkable fact as data (the canon row)

The Strata pattern: obligations are RECORDED as data; pluggable
backends discharge them. The tier is a BACKEND ASSIGNMENT, not a
property of the fact (lean-doctrine: kernel proof / decide / generated
runtime check / oracle sweep). Replaces: hand-wired per-lane checks,
"armed but unfired" registrations (an obligation whose discharge is
`none` is the gap, as data), ad-hoc diag renderings. Deliberately OUT
(phase 1): assumptions (no consumer yet). Core-only: `Name`/`String`
are prelude types — nothing schema-shaped crosses this line. -/

/-- The discharge tier: WHICH backend discharges the obligation.
    Generalizes schema-lang's `Invariant.Tier` ladder
    (`boundaryCheck`/`proved`/`oracleCovered` → `generatedCheck`/
    `provedAtElab`/`oracleSwept`) and adds the `decidableNow` rung the
    doctrine row names (a decide/grind discharge at elaboration or CI). -/
inductive Obligation.Tier where
  | provedAtElab
  | decidableNow
  | generatedCheck
  | oracleSwept
deriving Repr, BEq, DecidableEq, Inhabited

/-- The tier's rendering (emitted doc comments + test pins). -/
def Obligation.Tier.render : Obligation.Tier → String
  | .provedAtElab => "proved-at-elab"
  | .decidableNow => "decidable-now"
  | .generatedCheck => "generated-check"
  | .oracleSwept => "oracle-swept"

instance : ToString Obligation.Tier := ⟨Obligation.Tier.render⟩

/-- The discharge's EVIDENCE: which backend artifact carries it — a
    cited kernel theorem, a decide result, a generated check fn (at an
    artifact path), an oracle row reference. -/
inductive Obligation.Evidence where
  | citedProof (thm : Lean.Name)
  | decided (result : Bool)
  | generatedCheck (artifact fn : String)
  | oracleRow (ref : String)
deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString Obligation.Evidence := ⟨reprStr⟩

/-- The evidence's tier: every evidence shape belongs to exactly one
    backend. A discharge whose evidence's `.tier` differs from the
    obligation's tier is mis-wired — checkable as data. -/
def Obligation.Evidence.tier : Obligation.Evidence → Obligation.Tier
  | .citedProof _ => .provedAtElab
  | .decided _ => .decidableNow
  | .generatedCheck _ _ => .generatedCheck
  | .oracleRow _ => .oracleSwept

/-- A checkable fact as data: the label, the computed discharge tier,
    the lane's own payload row, and the declaring declaration.
    Registration COMPUTES the tier; backends READ it. -/
structure Obligation (α : Type) where
  label : String
  tier : Obligation.Tier
  payload : α
  provenance : Lean.Name
deriving Inhabited

end CodegenCore

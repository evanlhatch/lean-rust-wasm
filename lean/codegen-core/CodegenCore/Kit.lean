/-
# CodegenCore.Kit — the correspondence kit

The agreement-theorem vocabulary (lean-cohesion-plan §0): laws attach to
SHAPES, not instances. Moved from Machines.Foundations.
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

/-! ## The Iso graduations (review-2026-09-16: Iso is the load-bearing
    correspondence type) — each constructor below landed WITH its
    consumer; do not grow this section without one. -/

/-- The image decoder: total on the image — a member's witness makes
    `decode` fire, and the one-ended law pins WHICH witness. -/
def PartialIso.decodeImage (p : PartialIso A B)
    (x : {a : A // ∃ b, p.encode b = a}) : B :=
  Option.get (p.decode x.1) (by
    obtain ⟨b, hb⟩ := x.2
    rw [← hb, p.decode_encode]
    rfl)

/-- Every `PartialIso` restricts to a TRUE `Iso` on its image: the
    subtype of encodings that are `encode` of something. `to` =
    `decodeImage`; `inv` re-encodes. The image round trips BOTH ways:
    `to_inv` transports `decode_encode`, and `inv_to` upgrades it —
    re-encoding the decode of a canonical encoding reproduces the bytes
    exactly (the direction the one-ended law alone cannot give). First
    consumer: `SchemaLang.Witness` (W9.1's `witnessIso`). -/
def PartialIso.toImageIso (p : PartialIso A B) :
    Iso {a : A // ∃ b, p.encode b = a} B where
  to := p.decodeImage
  inv b := ⟨p.encode b, b, rfl⟩
  to_inv b := by
    show p.decodeImage (⟨p.encode b, b, rfl⟩ : {a : A // ∃ c, p.encode c = a}) = b
    simp only [decodeImage, p.decode_encode]
    rfl
  inv_to x := by
    obtain ⟨b, hb⟩ := x.2
    have hd : p.decode x.1 = some b := by rw [← hb]; exact p.decode_encode b
    have hto : p.decodeImage x = b :=
      Option.get_of_eq_some (by rw [hd]; exact Option.isSome_some) hd
    refine Subtype.ext ?_
    show p.encode (p.decodeImage x) = x.1
    rw [hto, hb]

/-- The canonical round trip at the value level: re-encoding the decode
    of an image member reproduces its bytes exactly. -/
theorem PartialIso.encode_decodeImage (p : PartialIso A B)
    (x : {a : A // ∃ b, p.encode b = a}) : p.encode (p.decodeImage x) = x.1 := by
  obtain ⟨b, hb⟩ := x.2
  have hd : p.decode x.1 = some b := by rw [← hb]; exact p.decode_encode b
  have hto : p.decodeImage x = b :=
    Option.get_of_eq_some (by rw [hd]; exact Option.isSome_some) hd
  rw [hto, hb]

/-- A nodup name list IS an indexed space: position `i` ↦ the name at
    `i`, name ↦ its unique position. (`Fin n`/name-subtype reading of
    the field-name lists the RowVals lane projects by — schema-lang's
    `RowVals.project?` cites this as what a name-keyed walk DOES.) -/
def nodupNamesIso {names : List String} (hnd : names.Nodup) :
    Iso (Fin names.length) {n : String // n ∈ names} where
  to i := ⟨names[i.1]'i.2, List.getElem_mem i.2⟩
  inv n := ⟨names.idxOf n.1, List.idxOf_lt_length_of_mem n.2⟩
  to_inv n := Subtype.ext (List.getElem_idxOf (List.idxOf_lt_length_of_mem n.2))
  inv_to i := Fin.ext (by
    have hj := List.getElem_idxOf (List.idxOf_lt_length_of_mem (List.getElem_mem i.2))
    exact (List.getElem_inj hnd).mp hj)

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
    `provedAtElab`/`oracleSwept`), adds the `decidableNow` rung the
    doctrine row names (a decide/grind discharge at elaboration or CI),
    and adds the `guestVerified` rung (W9.3,
    notes/design-guest-verified.md §3): a guest-checked witness — the
    host ships a serialized certificate, the guest re-checks it at the
    point of use. -/
inductive Obligation.Tier where
  | provedAtElab
  | decidableNow
  | generatedCheck
  | oracleSwept
  | guestVerified
deriving Repr, BEq, DecidableEq, Inhabited

/-- The tier's rendering (emitted doc comments + test pins). -/
def Obligation.Tier.render : Obligation.Tier → String
  | .provedAtElab => "proved-at-elab"
  | .decidableNow => "decidable-now"
  | .generatedCheck => "generated-check"
  | .oracleSwept => "oracle-swept"
  | .guestVerified => "guest-verified"

instance : ToString Obligation.Tier := ⟨Obligation.Tier.render⟩

/-- The discharge's EVIDENCE: which backend artifact carries it — a
    cited kernel theorem, a decide result, a generated check fn (at an
    artifact path), an oracle row reference. -/
inductive Obligation.Evidence where
  | citedProof (thm : Lean.Name)
  | decided (result : Bool)
  | generatedCheck (artifact fn : String)
  | oracleRow (ref : String)
  /-- W9.3: `artifact` = the byte-tied witness file; `ref` = the
      obligation's label inside it (the certificate certifies THAT
      obligation). -/
  | guestWitness (artifact ref : String)
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
  | .guestWitness _ _ => .guestVerified

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

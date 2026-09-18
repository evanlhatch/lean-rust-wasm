/-
# SchemaLang.Witness — the guest-checked witness: data + codec (W9.1)

The fifth obligation tier's certificate (notes/design-guest-verified.md
§1): a witness is `label + claim + proof + fuel`, serialized host-side
over the Codec.lean combinators, decoded guest-side, re-checked by
W9.2's fuel-bounded checker. This module owns the DATA and the WIRE:

- `WU64`/`WBoolExpr`/`WProp` — the claim language (design §2.1): a
  first-order mirror of the `VExpr` `.bool` fragment. v1 scope (design
  decision 4): VExpr-.bool invariants + the migration-chain rule ONLY —
  `WProp` is exactly three ctors wide.
- `WProof` — the proof-term syntax (design §2.2): the calculus W9.2's
  `checkWitness` checks. This module does NOT build the checker.
- `Witness` — the certificate structure (design §1).
- The codec: one tag per ctor in DECLARATION ORDER via
  `Codec.encEnum`/`Codec.decEnum?` (the EnumWire wire-breaking rule),
  children via the append-form combinators, the round-trip law proved
  per family and assembled once at `decWitness?_encWitness`.
- `witnessIso` — the assembled codec as `CodegenCore.PartialIso
  (List UInt8) Witness` (design §1's kit instance; RoundTripSpec's
  first production inhabitant — the review-2026-09-16 F3 graduation).
- Field resolution (design §2.1): `col`/`strlenCol` names must resolve
  against the record's `List Field` at the consumer's decode — a
  misspelled (or wrongly-typed) field is `none`, LOUD.

Deviations from the design doc (both forced by provability, both
approved-shaped per the order's "stated reason" rule):

1. **The label/string atom is a char list, not `encBytes
   label.toUTF8`.** Core v4.33.0 ships no `fromUTF8? ∘ toUTF8`
   round-trip lemma (the gap Codec.lean's header documents), and the
   kit's `decode_encode` law is a THEOREM — so the string atom is
   `encList` of `Char.toNat` varints (Codec.encString), proved via
   `String.ofList_toList` + `Char.ofNat_toNat`. Byte cost: no UTF-8
   packing on labels/names (constant per witness; §7.2's size budget
   is driven by the per-step proofs, not the label). W9.4 may revisit
   if a size finding lands.
2. **`witnessVersion`/`witnessFingerprint` are codec PARAMETERS, not
   constants.** The doc derives them from the schema fingerprint pair
   of the record the claim ranges over — this module is
   record-agnostic, so the pair is supplied by the caller (W9.4's
   emitter). The format's own wire-stability (WProp/WProof ctor order)
   is pinned by the RoundTripSpec GOLDEN in Tests — a reordered ctor
   changes the golden and fails the tie (the `just breaking` gate).

Decoder architecture (the honest note): the tree grammars
(`WBoolExpr.and`/`.not`, `WProof.steps`) are prefix-free but not
byte-structural, so their decoders carry an explicit DEPTH CAP (fuel)
with entry fuel `bytes.length + 1` — one byte per node minimum
(`Codec.length_encVarNat_pos`) makes the cap sufficient. A 0-fuel
decode is `none`, never a trap (the `Sem.exec` discipline). The laws
are proved at depth (`decWF_encW_append`, `depth ≤ fuel`) and at the
entry point.

W9.6 decode lane: the DECODE half of the codec joins the guest
(the design §4 step 3 flow: the guest decodes the witness bytes
before checking). The decode fns + the tag `ofNat?` dispatchers are
`@[guest_std]` — the bounded-Nat rationale lives in Codec.lean's
`decVarNat` mark (the varint reassembly is the only Nat arithmetic in
the lane; the depth-cap fuel is match-only). The ENCODE half stays
host-side: the host emits the witness, the guest only reads it.

Deliberate exclusions: the checker + soundness (`WHolds`,
`checkWitness`, the CheckedProp — W9.2); witness GENERATION (W9.4)
— the encoders stay unmarked.
-/

module

public import SchemaLang.Codec
public import SchemaLang.Item
public import CodegenCore.Kit

@[expose] public section

namespace SchemaLang.Witness

/-! ## The claim language (design §2.1 — the first-order VExpr mirror) -/

/-- The `.u64` fragment as data — VExpr's u64-valued leaves: literal,
    column reference (resolved against the record's fields at the
    consumer's decode — `resolve?`), and `strlen` of a string column
    (the only `.string` shape, VExpr's rule). -/
inductive WU64 where
  | lit (v : UInt64)
  | col (name : String)
  | strlenCol (name : String)
deriving Repr, BEq, DecidableEq

/-- The `.bool` fragment as data — exactly VExpr's four `.bool` ctors
    (`gt`/`eq`/`and`/`not`) over `WU64`. VExpr's `col` is
    ty-polymorphic, so in the mirror columns live at the `WU64` level;
    `WBoolExpr` is one-for-one with `VExpr s .bool`. -/
inductive WBoolExpr where
  | gt (a b : WU64)
  | eq (a b : WU64)
  | and (a b : WBoolExpr)
  | not (a : WBoolExpr)
deriving Repr, BEq, DecidableEq

/-- One chain step: the journal OFFSET of the event whose
    invariant-preservation this step certifies (design §7.2: claims
    reference events by offset, never by copy — the guest already holds
    the log). -/
structure WStep where
  offset : Nat
deriving Repr, BEq, DecidableEq

/-- The claim language (design §2.1). v1 scope is exactly these three
    ctors: `valid` (a VExpr-.bool invariant holds of the row), `eqU`
    (raw u64 equality), `chain` (per-event invariant preservation over
    a log fold — the migration rule, §4). Anything wider is a new
    calculus RULE with its own soundness proof (design decision 4). -/
inductive WProp where
  | valid (e : WBoolExpr)
  | eqU (a b : WU64)
  | chain (steps : List WStep) (inv : WBoolExpr)
deriving Repr, BEq, DecidableEq

/-- The proof-term syntax (design §2.2) — the calculus W9.2's checker
    interprets: `byEval` (both `eqU` sides reduce to `expected`),
    `byValidEval` (the row fold evaluates to 1), `steps` (one proof per
    chain step). The codec is rule-agnostic; the judgment
    (`checkWitness`) is W9.2.

    No `DecidableEq` — the nested `List WProof` defeats the handler;
    `BEq` suffices for the codec laws and the sweeps. -/
inductive WProof where
  | byEval (expected : UInt64)
  | byValidEval
  | steps (perStep : List WProof)
deriving Repr, BEq

/-- The certificate (design §1): the obligation's label, the claim in
    the mini-language, the proof term, and the checker's step cap
    (fuel — part of the artifact, §7.3). -/
structure Witness where
  label : String
  claim : WProp
  proof : WProof
  fuel : Nat
deriving Repr, BEq

/-! ## The wire tags (ctor order — the EnumWire wire-breaking rule) -/

/-- `WU64` ctor tags, in declaration order. Reordering is a
    wire-breaking change (the Tests golden is the tie). -/
inductive WU64Tag where
  | lit | col | strlenCol
deriving Repr, BEq, DecidableEq

def WU64Tag.toNat : WU64Tag → Nat
  | .lit => 0 | .col => 1 | .strlenCol => 2

-- NOT marked: the decode lane's INTERNAL tag dispatcher — the wasm-gen
-- closure fixpoint compiles it (the List-helper precedent) WITHOUT
-- exporting; a mark here made it a core EXPORT target, and four
-- same-named `of-nat?` exports failed the module encode.
def WU64Tag.ofNat? : Nat → Option WU64Tag
  | 0 => some .lit | 1 => some .col | 2 => some .strlenCol | _ => none

theorem WU64Tag.ofNat?_toNat (t : WU64Tag) : WU64Tag.ofNat? t.toNat = some t := by
  cases t <;> rfl

/-- `WBoolExpr` ctor tags, in declaration order. -/
inductive WBoolExprTag where
  | gt | eq | and | not
deriving Repr, BEq, DecidableEq

def WBoolExprTag.toNat : WBoolExprTag → Nat
  | .gt => 0 | .eq => 1 | .and => 2 | .not => 3

-- NOT marked: the decode lane's INTERNAL tag dispatcher — the wasm-gen
-- closure fixpoint compiles it (the List-helper precedent) WITHOUT
-- exporting; a mark here made it a core EXPORT target, and four
-- same-named `of-nat?` exports failed the module encode.
def WBoolExprTag.ofNat? : Nat → Option WBoolExprTag
  | 0 => some .gt | 1 => some .eq | 2 => some .and | 3 => some .not | _ => none

theorem WBoolExprTag.ofNat?_toNat (t : WBoolExprTag) :
    WBoolExprTag.ofNat? t.toNat = some t := by
  cases t <;> rfl

/-- `WProp` ctor tags, in declaration order. -/
inductive WPropTag where
  | valid | eqU | chain
deriving Repr, BEq, DecidableEq

def WPropTag.toNat : WPropTag → Nat
  | .valid => 0 | .eqU => 1 | .chain => 2

-- NOT marked: the decode lane's INTERNAL tag dispatcher — the wasm-gen
-- closure fixpoint compiles it (the List-helper precedent) WITHOUT
-- exporting; a mark here made it a core EXPORT target, and four
-- same-named `of-nat?` exports failed the module encode.
def WPropTag.ofNat? : Nat → Option WPropTag
  | 0 => some .valid | 1 => some .eqU | 2 => some .chain | _ => none

theorem WPropTag.ofNat?_toNat (t : WPropTag) : WPropTag.ofNat? t.toNat = some t := by
  cases t <;> rfl

/-- `WProof` ctor tags, in declaration order. -/
inductive WProofTag where
  | byEval | byValidEval | steps
deriving Repr, BEq, DecidableEq

def WProofTag.toNat : WProofTag → Nat
  | .byEval => 0 | .byValidEval => 1 | .steps => 2

-- NOT marked: the decode lane's INTERNAL tag dispatcher — the wasm-gen
-- closure fixpoint compiles it (the List-helper precedent) WITHOUT
-- exporting; a mark here made it a core EXPORT target, and four
-- same-named `of-nat?` exports failed the module encode.
def WProofTag.ofNat? : Nat → Option WProofTag
  | 0 => some .byEval | 1 => some .byValidEval | 2 => some .steps | _ => none

theorem WProofTag.ofNat?_toNat (t : WProofTag) : WProofTag.ofNat? t.toNat = some t := by
  cases t <;> rfl

/-! ## Encoders (structural on the data) -/

def encWU64 : WU64 → List UInt8
  | .lit v => Codec.encEnum WU64Tag.lit.toNat ++ Codec.encU64 v
  | .col n => Codec.encEnum WU64Tag.col.toNat ++ Codec.encString n
  | .strlenCol n => Codec.encEnum WU64Tag.strlenCol.toNat ++ Codec.encString n

def encWBoolExpr : WBoolExpr → List UInt8
  | .gt a b => Codec.encEnum WBoolExprTag.gt.toNat ++ encWU64 a ++ encWU64 b
  | .eq a b => Codec.encEnum WBoolExprTag.eq.toNat ++ encWU64 a ++ encWU64 b
  | .and a b => Codec.encEnum WBoolExprTag.and.toNat ++ encWBoolExpr a ++ encWBoolExpr b
  | .not a => Codec.encEnum WBoolExprTag.not.toNat ++ encWBoolExpr a

def encWStep (s : WStep) : List UInt8 := Codec.encVarNat s.offset

@[guest_std]
def decWStep? (bs : List UInt8) : Option (WStep × List UInt8) :=
  (Codec.decNat? bs).map fun (n, r) => (⟨n⟩, r)

def encWProp : WProp → List UInt8
  | .valid e => Codec.encEnum WPropTag.valid.toNat ++ encWBoolExpr e
  | .eqU a b => Codec.encEnum WPropTag.eqU.toNat ++ encWU64 a ++ encWU64 b
  | .chain steps inv =>
      Codec.encEnum WPropTag.chain.toNat ++ Codec.encList encWStep steps ++ encWBoolExpr inv

-- The proof-term encoder, as a mutual pair: `steps`' children
-- recurse through `List`, so the list half is its own structural
-- function. `encWProofs_flatten` re-joins it to `Codec.encList`'s
-- shape for the round-trip laws.
mutual
def encWProof : WProof → List UInt8
  | .byEval v => Codec.encEnum WProofTag.byEval.toNat ++ Codec.encU64 v
  | .byValidEval => Codec.encEnum WProofTag.byValidEval.toNat
  | .steps ps => Codec.encEnum WProofTag.steps.toNat ++ Codec.encVarNat ps.length
      ++ encWProofs ps

def encWProofs : List WProof → List UInt8
  | [] => []
  | p :: ps => encWProof p ++ encWProofs ps
end

/-- The list half IS `encList`'s flattened map — the bridge the
    `steps` round trip rewrites through. -/
theorem encWProofs_flatten (ps : List WProof) :
    encWProofs ps = (ps.map encWProof).flatten := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [encWProofs, ih]

/-- `encWProof` at `steps`, restated in `encList` shape. -/
theorem encWProof_steps (ps : List WProof) :
    encWProof (.steps ps) =
      Codec.encEnum WProofTag.steps.toNat ++ Codec.encList encWProof ps := by
  simp [encWProof, Codec.encList, encWProofs_flatten]

/-! ## The flat decoders (WU64, WStep) -/

/-- Decode a `WU64`: tag dispatch (`Codec.decEnum?`), payload per ctor;
    unknown tags and truncation reject. -/
@[guest_std]
def decWU64? (bs : List UInt8) : Option (WU64 × List UInt8) :=
  match Codec.decEnum? WU64Tag.ofNat? bs with
  | some (.lit, rest) => (Codec.decU64? rest).map fun (v, r) => (.lit v, r)
  | some (.col, rest) => (Codec.decString? rest).map fun (n, r) => (.col n, r)
  | some (.strlenCol, rest) => (Codec.decString? rest).map fun (n, r) => (.strlenCol n, r)
  | _ => none

/-- THE `WU64` ROUND TRIP, append form. -/
theorem decWU64_encWU64_append (u : WU64) (rest : List UInt8) :
    decWU64? (encWU64 u ++ rest) = some (u, rest) := by
  cases u with
  | lit v =>
      simp only [encWU64, List.append_assoc, decWU64?,
        Codec.decEnum_encEnum_append _ _ WU64Tag.ofNat?_toNat,
        Codec.decU64_encU64_append, Option.map_some]
  | col n =>
      simp only [encWU64, List.append_assoc, decWU64?,
        Codec.decEnum_encEnum_append _ _ WU64Tag.ofNat?_toNat,
        Codec.decString_encString_append, Option.map_some]
  | strlenCol n =>
      simp only [encWU64, List.append_assoc, decWU64?,
        Codec.decEnum_encEnum_append _ _ WU64Tag.ofNat?_toNat,
        Codec.decString_encString_append, Option.map_some]

/-- THE `WStep` ROUND TRIP, append form. -/
theorem decWStep_encWStep_append (s : WStep) (rest : List UInt8) :
    decWStep? (encWStep s ++ rest) = some (s, rest) := by
  obtain ⟨n⟩ := s
  simp [encWStep, decWStep?]

/-! ## The tree decoders (depth-capped — see the module header) -/

/-- Node depth of a `WBoolExpr` (the decode-fuel need: one fuel unit
    per node). -/
def WBoolExpr.depth : WBoolExpr → Nat
  | .gt _ _ | .eq _ _ => 1
  | .and a b => max a.depth b.depth + 1
  | .not a => a.depth + 1

/-- The depth-capped `WBoolExpr` decoder. Fuel 0 is `none` — loud,
    never a trap. Entry point: `decWBoolExpr?`. -/
@[guest_std]
def decWBoolExprF? : (fuel : Nat) → List UInt8 → Option (WBoolExpr × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
      match Codec.decEnum? WBoolExprTag.ofNat? bs with
      | some (.gt, rest) =>
          (decWU64? rest).bind fun (a, r1) =>
          (decWU64? r1).map fun (b, r2) => (.gt a b, r2)
      | some (.eq, rest) =>
          (decWU64? rest).bind fun (a, r1) =>
          (decWU64? r1).map fun (b, r2) => (.eq a b, r2)
      | some (.and, rest) =>
          (decWBoolExprF? fuel rest).bind fun (a, r1) =>
          (decWBoolExprF? fuel r1).map fun (b, r2) => (.and a b, r2)
      | some (.not, rest) =>
          (decWBoolExprF? fuel rest).map fun (a, r) => (.not a, r)
      | _ => none

/-- The entry-point decoder: fuel = bytes + 1 suffices (one byte per
    node minimum — `depth_le_length_encWBoolExpr`). -/
-- `bs.length + 1`: the entry fuel — `List.length`'s Nat result + the
-- sanctioned `Nat.add` (the length-walk counter's increment, the
-- backend's inlineNatFap surface).
@[guest_std]
def decWBoolExpr? (bs : List UInt8) : Option (WBoolExpr × List UInt8) :=
  decWBoolExprF? (bs.length + 1) bs

/-- THE `WBoolExpr` ROUND TRIP at depth, append form. -/
theorem decWBoolExprF_encWBoolExpr_append (e : WBoolExpr) :
    ∀ (rest : List UInt8) (fuel : Nat), e.depth ≤ fuel →
      decWBoolExprF? fuel (encWBoolExpr e ++ rest) = some (e, rest) := by
  induction e with
  | gt a b =>
      intro rest fuel h
      simp only [WBoolExpr.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encWBoolExpr, List.append_assoc, decWBoolExprF?,
        Codec.decEnum_encEnum_append _ _ WBoolExprTag.ofNat?_toNat,
        decWU64_encWU64_append, Option.bind_some, Option.map_some]
  | eq a b =>
      intro rest fuel h
      simp only [WBoolExpr.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encWBoolExpr, List.append_assoc, decWBoolExprF?,
        Codec.decEnum_encEnum_append _ _ WBoolExprTag.ofNat?_toNat,
        decWU64_encWU64_append, Option.bind_some, Option.map_some]
  | and a b iha ihb =>
      intro rest fuel h
      simp only [WBoolExpr.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have ha : a.depth ≤ f := by omega
      have hb : b.depth ≤ f := by omega
      simp only [encWBoolExpr, List.append_assoc, decWBoolExprF?,
        Codec.decEnum_encEnum_append _ _ WBoolExprTag.ofNat?_toNat]
      rw [iha (encWBoolExpr b ++ rest) f ha]
      simp only [Option.bind_some]
      rw [ihb rest f hb]
      simp
  | not a iha =>
      intro rest fuel h
      simp only [WBoolExpr.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have ha : a.depth ≤ f := by omega
      simp only [encWBoolExpr, List.append_assoc, decWBoolExprF?,
        Codec.decEnum_encEnum_append _ _ WBoolExprTag.ofNat?_toNat]
      rw [iha rest f ha]
      simp

/-- Every node emits at least one byte (its tag), so the entry fuel
    `bytes + 1` always covers the depth. -/
theorem WBoolExpr.depth_le_length_enc (e : WBoolExpr) :
    e.depth ≤ (encWBoolExpr e).length := by
  induction e with
  | gt a b =>
      have h0 := Codec.length_encVarNat_pos (WBoolExprTag.gt.toNat)
      simp [encWBoolExpr, Codec.encEnum, List.length_append, WBoolExpr.depth] at h0 ⊢; omega
  | eq a b =>
      have h0 := Codec.length_encVarNat_pos (WBoolExprTag.eq.toNat)
      simp [encWBoolExpr, Codec.encEnum, List.length_append, WBoolExpr.depth] at h0 ⊢; omega
  | and a b iha ihb =>
      have h0 := Codec.length_encVarNat_pos (WBoolExprTag.and.toNat)
      simp [encWBoolExpr, Codec.encEnum, List.length_append, WBoolExpr.depth] at h0 ⊢
      omega
  | not a iha =>
      have h0 := Codec.length_encVarNat_pos (WBoolExprTag.not.toNat)
      simp [encWBoolExpr, Codec.encEnum, List.length_append, WBoolExpr.depth] at h0 ⊢
      omega

/-- THE `WBoolExpr` ROUND TRIP at the entry point, append form. -/
theorem decWBoolExpr_encWBoolExpr_append (e : WBoolExpr) (rest : List UInt8) :
    decWBoolExpr? (encWBoolExpr e ++ rest) = some (e, rest) := by
  show decWBoolExprF? ((encWBoolExpr e ++ rest).length + 1) _ = _
  apply decWBoolExprF_encWBoolExpr_append
  have h := e.depth_le_length_enc
  simp [List.length_append]; omega

/-! ## The proof-term decoder -/

/-- The induction principle for the nested `WProof`: the stock
    recursor's second motive is over `List WProof`; this re-packs it
    as a per-element hypothesis (v4.33.0's `induction` tactic rejects
    nested inductives — `WProof.rec`'s two motives do the work). -/
theorem WProof.rec' {motive : WProof → Prop}
    (byEval : ∀ v, motive (.byEval v))
    (byValidEval : motive .byValidEval)
    (steps : ∀ ps, (∀ q ∈ ps, motive q) → motive (.steps ps)) :
    ∀ p, motive p :=
  fun p =>
    WProof.rec (motive_2 := fun ps => ∀ q ∈ ps, motive q)
      byEval byValidEval (fun ps ih => steps ps ih)
      (fun q hq => by cases hq)
      (fun head tail ihh iht q hq => by
        cases hq with
        | head => exact ihh
        | tail _ h => exact iht q h)
      p

/-- Node depth of a `WProof` (`steps` takes the children's max). -/
def WProof.depth : WProof → Nat
  | .byEval _ => 1
  | .byValidEval => 1
  | .steps ps => ps.foldl (fun m p => max m p.depth) 0 + 1

/-- The fold is monotone in the accumulator. -/
theorem WProof.le_foldl_depth (ps : List WProof) (n : Nat) :
    n ≤ ps.foldl (fun m p => max m p.depth) n := by
  induction ps generalizing n with
  | nil => exact Nat.le_refl n
  | cons p ps ih => exact Nat.le_trans (Nat.le_max_left n p.depth) (ih _)

/-- Every member's depth is below the fold. -/
theorem WProof.depth_le_foldl (ps : List WProof) (acc : Nat) :
    ∀ q ∈ ps, q.depth ≤ ps.foldl (fun m p => max m p.depth) acc := by
  induction ps generalizing acc with
  | nil => intro q h; cases h
  | cons p ps ih =>
      intro q hq
      cases hq with
      | head =>
          exact Nat.le_trans (Nat.le_max_right acc p.depth) (WProof.le_foldl_depth ps _)
      | tail _ hq' => exact ih _ q hq'

/-- The depth-capped `WProof` decoder. Entry point: `decWProof?`. -/
@[guest_std]
def decWProofF? : (fuel : Nat) → List UInt8 → Option (WProof × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
      match Codec.decEnum? WProofTag.ofNat? bs with
      | some (.byEval, rest) => (Codec.decU64? rest).map fun (v, r) => (.byEval v, r)
      | some (.byValidEval, rest) => some (.byValidEval, rest)
      | some (.steps, rest) =>
          (Codec.decList? (decWProofF? fuel) rest).map fun (ps, r) => (.steps ps, r)
      | _ => none

/-- The entry-point decoder (fuel = bytes + 1; see the header note). -/
@[guest_std]
def decWProof? (bs : List UInt8) : Option (WProof × List UInt8) :=
  decWProofF? (bs.length + 1) bs

/-- THE `WProof` ROUND TRIP at depth, append form. The `steps` case
    rides the membership-restricted list law (the per-element depth
    bound comes from the fold). -/
theorem decWProofF_encWProof_append (p : WProof) :
    ∀ (rest : List UInt8) (fuel : Nat), p.depth ≤ fuel →
      decWProofF? fuel (encWProof p ++ rest) = some (p, rest) := by
  induction p using WProof.rec' with
  | byEval v =>
      intro rest fuel h
      simp only [WProof.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encWProof, List.append_assoc, decWProofF?,
        Codec.decEnum_encEnum_append _ _ WProofTag.ofNat?_toNat,
        Codec.decU64_encU64_append, Option.map_some]
  | byValidEval =>
      intro rest fuel h
      simp only [WProof.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp [encWProof, decWProofF?,
        Codec.decEnum_encEnum_append _ _ WProofTag.ofNat?_toNat]
  | steps ps ih =>
      intro rest fuel h
      have h1 : 1 ≤ fuel := by
        have := h; simp only [WProof.depth] at this; omega
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hfold : ps.foldl (fun m p => max m p.depth) 0 ≤ f := by
        simp only [WProof.depth] at h; omega
      rw [encWProof_steps, List.append_assoc]
      simp only [decWProofF?,
        Codec.decEnum_encEnum_append _ _ WProofTag.ofNat?_toNat]
      rw [Codec.decList_encList_append_of_mem encWProof (decWProofF? f) ps
        (fun q hq r => ih q hq r f
          (Nat.le_trans (WProof.depth_le_foldl ps 0 q hq) hfold)) rest]
      simp

/-- The `steps` depth fold is bounded by the children's encoded
    bytes (each child contributes its whole encoding, and the encoding
    is at least its depth). -/
theorem WProof.foldl_depth_le_length_flatten (ps : List WProof)
    (h : ∀ q ∈ ps, q.depth ≤ (encWProof q).length) :
    ∀ (acc : Nat), ps.foldl (fun m q => max m q.depth) acc ≤
      acc + ((ps.map encWProof).flatten).length := by
  induction ps with
  | nil => intro acc; simp
  | cons r rs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.flatten_cons, List.length_append]
      have hr : r.depth ≤ (encWProof r).length := h r List.mem_cons_self
      have hmem : ∀ q ∈ rs, q.depth ≤ (encWProof q).length :=
        fun q hq => h q (List.mem_cons_of_mem r hq)
      have hacc := ih hmem (max acc r.depth)
      omega

/-- Every proof node emits at least one byte; the `steps` children's
    encodings sum over the list — so the entry fuel covers the depth. -/
theorem WProof.depth_le_length_enc (p : WProof) :
    p.depth ≤ (encWProof p).length := by
  induction p using WProof.rec' with
  | byEval v =>
      have h0 := Codec.length_encVarNat_pos (WProofTag.byEval.toNat)
      simp [encWProof, Codec.encEnum, List.length_append, WProof.depth] at h0 ⊢; omega
  | byValidEval =>
      have h0 := Codec.length_encVarNat_pos (WProofTag.byValidEval.toNat)
      simp [encWProof, Codec.encEnum, WProof.depth] at h0 ⊢; omega
  | steps ps ih =>
      rw [encWProof_steps]
      have h0 := Codec.length_encVarNat_pos (WProofTag.steps.toNat)
      have h1 := Codec.length_encVarNat_pos ps.length
      have hf := WProof.foldl_depth_le_length_flatten ps ih 0
      simp [WProof.depth, Codec.encEnum, Codec.encList, List.length_append] at h0 h1 hf ⊢
      omega

/-- THE `WProof` ROUND TRIP at the entry point, append form. -/
theorem decWProof_encWProof_append (p : WProof) (rest : List UInt8) :
    decWProof? (encWProof p ++ rest) = some (p, rest) := by
  show decWProofF? ((encWProof p ++ rest).length + 1) _ = _
  apply decWProofF_encWProof_append
  have h := p.depth_le_length_enc
  simp [List.length_append]; omega

/-! ## The claim decoder -/

/-- Decode a `WProp`: tag dispatch, then the children (the `WBoolExpr`
    halves ride their entry-point decoder). -/
@[guest_std]
def decWProp? (bs : List UInt8) : Option (WProp × List UInt8) :=
  match Codec.decEnum? WPropTag.ofNat? bs with
  | some (.valid, rest) => (decWBoolExpr? rest).map fun (e, r) => (.valid e, r)
  | some (.eqU, rest) =>
      (decWU64? rest).bind fun (a, r1) =>
      (decWU64? r1).map fun (b, r2) => (.eqU a b, r2)
  | some (.chain, rest) =>
      (Codec.decList? decWStep? rest).bind fun (steps, r1) =>
      (decWBoolExpr? r1).map fun (inv, r2) => (.chain steps inv, r2)
  | _ => none

/-- THE `WProp` ROUND TRIP, append form. -/
theorem decWProp_encWProp_append (p : WProp) (rest : List UInt8) :
    decWProp? (encWProp p ++ rest) = some (p, rest) := by
  cases p with
  | valid e =>
      simp only [encWProp, List.append_assoc, decWProp?,
        Codec.decEnum_encEnum_append _ _ WPropTag.ofNat?_toNat,
        decWBoolExpr_encWBoolExpr_append, Option.map_some]
  | eqU a b =>
      simp only [encWProp, List.append_assoc, decWProp?,
        Codec.decEnum_encEnum_append _ _ WPropTag.ofNat?_toNat,
        decWU64_encWU64_append, Option.bind_some, Option.map_some]
  | chain steps inv =>
      simp only [encWProp, List.append_assoc, decWProp?,
        Codec.decEnum_encEnum_append _ _ WPropTag.ofNat?_toNat]
      rw [Codec.decList_encList_append encWStep decWStep? decWStep_encWStep_append steps
        (encWBoolExpr inv ++ rest)]
      simp [decWBoolExpr_encWBoolExpr_append]

/-! ## The witness wire (design §1: envelope + label + claim + proof + fuel) -/

/-- The witness encoding (design §1, modulo the header's two stated
    deviations): the versioned envelope over
    `label ++ claim ++ proof ++ fuel`. The envelope pair is the
    caller's (W9.4 derives it from the record's schema fingerprints);
    the guest rejects a version mismatch before touching the payload
    (`Codec.decEnvelope?_wrong_version`). -/
def encWitness (version fingerprint : Nat) (w : Witness) : List UInt8 :=
  Codec.encEnvelope version fingerprint (
    Codec.encString w.label ++ encWProp w.claim ++ encWProof w.proof ++
      Codec.encVarNat w.fuel)

/-- Decode the envelope payload: label, claim, proof, fuel — trailing
    bytes reject (the envelope already bounds the payload). -/
@[guest_std]
def decWitnessPayload? (bs : List UInt8) : Option Witness := do
  let (label, r1) ← Codec.decString? bs
  let (claim, r2) ← decWProp? r1
  let (proof, r3) ← decWProof? r2
  let (fuel, r4) ← Codec.decNat? r3
  match r4 with
  | [] => some ⟨label, claim, proof, fuel⟩
  | _ :: _ => none

/-- The whole-form decode: version-checked envelope, then the payload. -/
@[guest_std]
def decWitness? (expectedVersion : Nat) (bs : List UInt8) : Option Witness := do
  let env ← Codec.decEnvelope? expectedVersion bs
  decWitnessPayload? env.payload

/-- THE WITNESS ROUND TRIP (design §1's assembled law): every field's
    append-form lemma composed once. -/
theorem decWitness?_encWitness (version fingerprint : Nat) (w : Witness) :
    decWitness? version (encWitness version fingerprint w) = some w := by
  obtain ⟨label, claim, proof, fuel⟩ := w
  simp [encWitness, decWitness?, decWitnessPayload?, Codec.decEnvelope_encEnvelope,
    List.append_assoc, Codec.decString_encString_append, decWProp_encWProp_append,
    decWProof_encWProof_append, Codec.decNat?, Codec.decVarNat_encVarNat]

/-- THE ASSEMBLED CODEC (design §1): `Kit.PartialIso (List UInt8)
    Witness` at a caller-supplied envelope pair — the RoundTripSpec
    `iso` field's first production inhabitant (the review-2026-09-16
    F3 graduation: tested-only → production-consumed). -/
def witnessIso (version fingerprint : Nat) :
    CodegenCore.PartialIso (List UInt8) Witness where
  decode := decWitness? version
  encode := encWitness version fingerprint
  decode_encode := decWitness?_encWitness version fingerprint

/-- The image Iso (W-iso batch piece 1, consumed on the REAL codec):
    `witnessIso`'s canonical image is a TRUE `Kit.Iso` — `to` decodes
    (total on the image), `inv` re-encodes; both round trips hold. -/
def witnessImageIso (version fingerprint : Nat) :
    CodegenCore.Iso
      { bytes : List UInt8 // ∃ w, (witnessIso version fingerprint).encode w = bytes }
      Witness :=
  (witnessIso version fingerprint).toImageIso

/-- The canonical-image round trip: re-encoding the decode of a
    canonical byte string reproduces the bytes EXACTLY (the both-ways
    direction the one-ended `decode_encode` law alone cannot give). -/
theorem witnessImageIso_to_inv (version fingerprint : Nat)
    (b : { bytes : List UInt8 // ∃ w, (witnessIso version fingerprint).encode w = bytes }) :
    (witnessIso version fingerprint).encode
      ((witnessImageIso version fingerprint).to b) = b.1 :=
  (witnessIso version fingerprint).encode_decodeImage b

/-! ## Field resolution (design §2.1): names checked against the record -/

/-- A `col` name must name a `.u64` field; a `strlenCol` name a
    `.string` field. A miss is `none` — a misspelled (or wrongly-typed)
    witness field is a DECODE failure, loud. -/
def WU64.resolve? (fields : List Field) : WU64 → Option Unit
  | .lit _ => some ()
  | .col n => if fields.any (fun f => f.name == n && f.ty == .u64) then some () else none
  | .strlenCol n =>
      if fields.any (fun f => f.name == n && f.ty == .string) then some () else none

/-- Structural resolution over the boolean fragment. -/
def WBoolExpr.resolve? (fields : List Field) : WBoolExpr → Option Unit
  | .gt a b | .eq a b => do
      WU64.resolve? fields a; WU64.resolve? fields b
  | .and a b => do a.resolve? fields; b.resolve? fields
  | .not a => a.resolve? fields

/-- Claim-level resolution: every field name the claim mentions must
    resolve (`chain`'s steps are journal OFFSETS — no names to check). -/
def WProp.resolve? (fields : List Field) : WProp → Option Unit
  | .valid e => e.resolve? fields
  | .eqU a b => do WU64.resolve? fields a; WU64.resolve? fields b
  | .chain _ inv => inv.resolve? fields

/-- The record-aware decode: bytes → witness, then the claim's field
    names checked against the record's fields (design §2.1: the
    consumer's decode builds the resolution against the record's
    `List Field`; a misspelled field is `none`, loud). The full
    `ColPath` construction is W9.2's (the checker needs the path, the
    codec needs only the verdict). -/
def decWitnessFor? (fields : List Field) (expectedVersion : Nat)
    (bs : List UInt8) : Option Witness := do
  let w ← decWitness? expectedVersion bs
  w.claim.resolve? fields
  return w

end SchemaLang.Witness

end -- @[expose] public section

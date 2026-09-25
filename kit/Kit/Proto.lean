/-
# Kit.Proto — the format-generic protobuf primitives (the tag/field layer)

The promotion of the proto primitives out of the substrait lane
(substrait/Substrait/ProtoBuf.lean's original home): the tag/wire-type
discipline, the length-delimited fields, the un-counted repeated field
riding Kit.Varint, the signed int32/int64 face, the ASCII string face,
and the message-combinator layer the message decoders compose (the
oneof wrapper, the message-field face, the string/bool/enum field
faces, the fueled full face, the clean-suffix discipline) — every piece
FORMAT-GENERIC (no substrait type appears in any signature). The
substrait message layer (Substrait.Wire) is now the promotion's FIRST
consumer; the vortex DType proto face (Vortex.DTypeProto) is the
SECOND — the leftover rule's second-consumer promotion, the same move
Kit.Varint itself made (the WasmCore/SchemaCore twin precedent).

THE LAW (15-patterns #2, the append-form codec law): every primitive's
round trip is `dec (enc a ++ rest) = some (a, rest)` — the appended
`rest` is the composition discipline: fields compose under sequencing
BECAUSE the laws are append-form. Every law here is UNCONDITIONAL
except the signed varint's (the 64-bit two's-complement range — the
off-domain truncation is the pinned loss, SubstraitTests) and the
string field's (the ASCII fragment — the full UTF-8 face rides
TextKit's char level, the char level is TextKit's alone — the
doctrine's text-proof discipline).

THE REPEAT: protobuf's repeated fields have no count prefix — the
extent is "repeat until a different tag". The decoder is fuel-bounded
(`decRep?`), and the generic law carries the fuel bound as a statement
side-condition (`|enc xs ++ rest| + 1 ≤ fuel`) discharged by the
callers' length bookkeeping. The `Step` outcome separates the three
faces a repeat needs: `more` (an element + the rest), `stop` (a
different tag — the list ends; the input returned UNCHANGED), and the
plain `none` (malformed — no silent divergence).

THE WIRETARGET ROW (the design-forward-surface §2 checklist, as data):
`WireTarget` — the carrier + the law + the inDomain gate + the
off-domain controls + the grade + the entourage — promoted here so a
wire format lands as a ROW in any lane (the scanable checklist); the
substrait plan row (`planWireTarget`) and the vortex dtype row
(`dtypeWireTarget`) are its consumers. The canonical-order choices and
the honest conditional grades are per-row data, never machinery.

Core-only (imports Kit.Varint — the cone rule).

The five questions (notes/v3/01-core.md):
- root: Crossing (the wire) — the proto message bytes ↔ the field
  values.
- carrier grade: the append-form laws (pattern #2) — one per
  primitive, each a one-line chain through `Kit.Varint`'s law.
- spine reading: n/a — the shared byte substrate the C1 message
  layers compose.
- ladder rung: hand theorems of the small kind (structural induction +
  the varint law).
- gate row: the axiom report (Kit is gated); KitTests carries the law
  pins, the consumers' suites (SubstraitTests + VortexTests) the
  sweeps + the negative controls.
-/

import Kit.Varint

namespace Kit.Proto

open Kit.Varint (encVarNat encVarNatGo decVarNat? decVarNat?_encVarNat_append)

/-! ## the step outcome (the repeat's three faces) -/

/-- One field-parse outcome: `more` = the field's value + the rest;
    `stop` = a different tag (the list ends — the input returned
    UNCHANGED, the non-consuming discipline); the plain `none` =
    malformed (no silent divergence). -/
inductive Step (α : Type) where
  | more (a : α) (rest : List UInt8)
  | stop (rest : List UInt8)

/-! ## the tag layer -/

/-- Wire type 0: the varint face (ints, enums, bools). -/
def wtVarint : Nat := 0

/-- Wire type 2: the length-delimited face (strings, bytes, messages). -/
def wtLen : Nat := 2

/-- The field tag: `field * 8 + wire_type`, varint-encoded. -/
def encTag (f wt : Nat) : List UInt8 := encVarNat (f * 8 + wt)

/-- Read a tag: the field number, the wire type, the rest. -/
def decTag? (bs : List UInt8) : Option (Nat × Nat × List UInt8) :=
  (decVarNat? bs).map fun (v, rest) => (v / 8, v % 8, rest)

/-- PATTERN #2 — the tag's append-form law (a one-line chain through
    the varint's; the wire type is a VALID tag discriminant — the
    3-bit field the tag format defines). -/
theorem decTag?_encTag_append (f wt : Nat) (hwt : wt < 8) (rest : List UInt8) :
    decTag? (encTag f wt ++ rest) = some (f, wt, rest) := by
  simp only [encTag, decTag?]
  rw [decVarNat?_encVarNat_append]
  simp only [Option.map_some, Option.some.injEq]
  rw [Nat.mul_comm f 8, Nat.mul_add_div (show (8:Nat) > 0 by decide),
    Nat.div_eq_of_lt (by omega), Nat.mul_add_mod 8 f wt, Nat.mod_eq_of_lt hwt]
  simp

/-! ## the varint field face -/

/-- Write a varint field: tag + payload. -/
def encVarField (f v : Nat) : List UInt8 := encTag f wtVarint ++ encVarNat v

/-- Read a varint field numbered `f`; a different tag is the `stop`
    face (non-consuming), a malformed tag is `none`. -/
def decVarField? (f : Nat) (bs : List UInt8) : Option (Step Nat) :=
  match decTag? bs with
  | none => none
  | some (f', wt', rest) =>
      if f' == f && wt' == wtVarint then
        (decVarNat? rest).map fun (v, rest') => Step.more v rest'
      else some (.stop bs)

/-- PATTERN #2 — the varint field's append-form law. -/
theorem decVarField?_encVarField_append (f v : Nat) (rest : List UInt8) :
    decVarField? f (encVarField f v ++ rest) = some (.more v rest) := by
  have hsplit : encVarField f v ++ rest
      = encTag f wtVarint ++ (encVarNat v ++ rest) := by
    simp only [encVarField, List.append_assoc]
  rw [hsplit]
  simp only [decVarField?]
  rw [decTag?_encTag_append f wtVarint (by unfold wtVarint; decide)]
  simp [decVarNat?_encVarNat_append]

/-- The other-tag stop face: a varint field of a DIFFERENT number ends
    the parse (the varint-rep termination face's engine). -/
theorem decVarField?_other_stop (f f' v : Nat) (rest : List UInt8) (hne : f ≠ f') :
    decVarField? f (encVarField f' v ++ rest)
      = some (Step.stop (encVarField f' v ++ rest)) := by
  have hsplit : encVarField f' v ++ rest
      = encTag f' wtVarint ++ (encVarNat v ++ rest) := by
    simp only [encVarField, List.append_assoc]
  rw [hsplit]
  simp only [decVarField?]
  rw [decTag?_encTag_append f' wtVarint (by unfold wtVarint; decide)]
  simp [Ne.symm hne]

/-! ## the length-delimited field face -/

/-- Write a length-delimited field: tag + length varint + payload. -/
def encLenBytes (f : Nat) (payload : List UInt8) : List UInt8 :=
  encTag f wtLen ++ encVarNat payload.length ++ payload

/-- Take exactly `n` bytes (refusing a short input — the truncation
    control's refusal face). -/
def takeBytes? : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, bs => some ([], bs)
  | _ + 1, [] => none
  | n + 1, b :: rest => (takeBytes? n rest).map fun p => (b :: p.1, p.2)

/-- PATTERN #2 — the take's append-form law. -/
theorem takeBytes?_append : ∀ (bs rest : List UInt8),
    takeBytes? bs.length (bs ++ rest) = some (bs, rest) := by
  intro bs
  induction bs with
  | nil => intro rest; rfl
  | cons b tl ih =>
      intro rest
      simp only [List.length_cons, List.cons_append, takeBytes?]
      exact congrArg _ (ih rest)

/-- Read a length-delimited field numbered `f`; a different tag is the
    `stop` face; the EMPTY input is the stop face too (the repeat's
    termination face — a field requires a tag, so nothing follows). -/
def decLenField? (f : Nat) (bs : List UInt8) : Option (Step (List UInt8)) :=
  match decTag? bs with
  | none => if bs = [] then some (Step.stop []) else none
  | some (f', wt', rest) =>
      if f' == f && wt' == wtLen then
        match decVarNat? rest with
        | none => none
        | some (len, rest') =>
            (takeBytes? len rest').map fun p => Step.more p.1 p.2
      else some (.stop bs)

/-- PATTERN #2 — the length-delimited field's append-form law. -/
theorem decLenField?_encLenBytes_append (f : Nat) (payload rest : List UInt8) :
    decLenField? f (encLenBytes f payload ++ rest) = some (.more payload rest) := by
  have hsplit : encLenBytes f payload ++ rest
      = encTag f wtLen ++ (encVarNat payload.length ++ (payload ++ rest)) := by
    simp only [encLenBytes, List.append_assoc]
  rw [hsplit]
  simp only [decLenField?]
  rw [decTag?_encTag_append f wtLen (by unfold wtLen; decide)]
  simp [takeBytes?_append, decVarNat?_encVarNat_append]

/-! ## the repeat face (the un-counted repeated field) -/

/-- Encode a repeated field's elements back-to-back (each element
    carries its own tag — the wire's discipline). -/
def encRep (encElem : α → List UInt8) : List α → List UInt8
  | [] => []
  | x :: xs => encElem x ++ encRep encElem xs

/-- Read a repeated field: elements until a different tag. Fuel-bounded
    (the generic law bounds the fuel below: the input's length + 1
    suffices because every element parse consumes its ≥1-byte tag). -/
def decRep? (elem : List UInt8 → Option (Step α)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
      match elem bs with
      | none => none
      | some (Step.stop _) => some ([], bs)
      | some (Step.more a rest) =>
          match decRep? elem k rest with
          | some (as, rest') => some (a :: as, rest')
          | none => none

/-- PATTERN #2 — the repeat's append-form law, on the ADMISSIBLE
    element subdomain `P` (pattern #18's inDomain discipline at the
    repeat's level): with the element face's own law on the subdomain
    (`helem`), the tag discipline's stop face at the end (`hend`), and
    every element encoding non-empty (`hpos` — the fuel bound's engine:
    the fuel walks the bytes the elements consumed), the repeat decodes
    exactly the encoded list plus any suffix, at any fuel above the
    encoded size. The unconditional face is `P := fun _ => True`. -/
theorem decRep?_encRep_append (elem : List UInt8 → Option (Step α))
    (encElem : α → List UInt8) (P : α → Prop)
    (helem : ∀ (x : α) (r : List UInt8), P x →
      elem (encElem x ++ r) = some (Step.more x r))
    (hpos : ∀ (x : α), 0 < (encElem x).length) :
    ∀ (rest : List UInt8), elem rest = some (Step.stop rest) →
      ∀ (fuel : Nat) (xs : List α), (∀ x ∈ xs, P x) →
      (encRep encElem xs ++ rest).length + 1 ≤ fuel →
      decRep? elem fuel (encRep encElem xs ++ rest) = some (xs, rest) := by
  intro rest hend
  intro fuel
  induction fuel with
  | zero =>
      intro xs _ hfuel
      exact absurd hfuel (by omega)
  | succ k ih =>
      intro xs hall hfuel
      cases xs with
      | nil =>
          simp only [encRep, List.nil_append, decRep?]
          rw [hend]
      | cons x xs' =>
          simp only [encRep, List.append_assoc, decRep?]
          rw [helem x (encRep encElem xs' ++ rest) (hall x (by simp))]
          dsimp only
          rw [ih xs' (fun u hu => hall u (by simp [hu])) (by
            have h1 : (encRep encElem (x :: xs') ++ rest).length + 1 ≤ k + 1 := hfuel
            have hx := hpos x
            simp only [encRep, List.append_assoc, List.length_append] at h1 ⊢
            omega)]

/-- The rep encoding's per-element bound (the fuel bookkeeping's
    helper). -/
theorem encRep_mem_le (encElem : α → List UInt8) : ∀ (xs : List α) (x : α), x ∈ xs →
    (encElem x).length ≤ (encRep encElem xs).length := by
  intro xs
  induction xs with
  | nil => intro x h; cases h
  | cons y tl ih =>
      intro x h
      simp only [encRep, List.length_append]
      rcases List.mem_cons.mp h with rfl | htl
      · omega
      · have hle := ih x htl
        omega

/-! ## the non-emptiness face (the repeat law's fuel engine) -/

/-- Every varint encoding is non-empty (the fuel `n + 1` always spends
    at least one byte). -/
theorem encVarNat_pos (n : Nat) : 0 < (encVarNat n).length := by
  show 0 < (encVarNatGo (n + 1) n).length
  simp only [encVarNatGo]
  split
  · simp
  · simp

/-- Every varint FIELD encoding is non-empty (tag + payload). -/
theorem encVarField_pos (f v : Nat) : 0 < (encVarField f v).length := by
  simp only [encVarField, encTag, wtVarint, List.length_append]
  have h1 := encVarNat_pos (f * 8 + 0)
  have h2 := encVarNat_pos v
  omega

/-- Every length-delimited field encoding is non-empty (tag + length
    prefix, even for the empty payload). -/
theorem encLenBytes_pos (f : Nat) (p : List UInt8) : 0 < (encLenBytes f p).length := by
  simp only [encLenBytes, encTag, wtLen, List.length_append]
  have h1 := encVarNat_pos (f * 8 + 2)
  have h2 := encVarNat_pos p.length
  omega

/-- A varint field spends at least TWO bytes (the tag + the payload
    varint). -/
theorem encVarField_ge (f v : Nat) : 2 ≤ (encVarField f v).length := by
  simp only [encVarField, encTag, wtVarint, List.length_append]
  have h1 := encVarNat_pos (f * 8 + 0)
  have h2 := encVarNat_pos v
  omega

/-- The length-delimited wrap's cost: a length-delimited field spends
    at least TWO bytes (the tag + the length varint) over its payload —
    the nesting discipline the message laws' fuel bounds walk. -/
theorem encLenBytes_ge (f : Nat) (p : List UInt8) :
    p.length + 2 ≤ (encLenBytes f p).length := by
  simp only [encLenBytes, encTag, wtLen, List.length_append]
  have h1 := encVarNat_pos (f * 8 + 2)
  have h2 := encVarNat_pos p.length
  omega

/-! ## the fuel-bound split (the message laws' bookkeeping, ONCE) -/

/-- THE FUEL-BOUND SPLIT (the sharp core): bytes that fit at `n` with a
    len-delimited wrap of `ws` inside — under any left context `pre`,
    with any tail riding after — leave `ws` TWO bytes of budget (the
    wrap's ≥ 2-byte cost is `encLenBytes_ge`; the arithmetic is
    length-level, so the context's shape is irrelevant). The message
    laws' repeated `have hbound … omega` blocks are this family's
    one-line citations. -/
theorem encLenBytes_fuel_budget (n : Nat) {M : Nat} {pre ws tail : List UInt8}
    (h : (pre ++ encLenBytes M ws ++ tail).length + 1 ≤ n) :
    ws.length + 2 ≤ n := by
  have hw := encLenBytes_ge M ws
  simp only [List.length_append] at h ⊢
  omega

/-- The fuel-inductive laws' face: a wrapped body that fits at fuel
    `f + 1` has its inner body fit at `f` (one wrap spends the
    decrement). -/
theorem encLenBytes_fuel_split {f M : Nat} {pre inner tail : List UInt8}
    (h : (pre ++ encLenBytes M inner ++ tail).length + 1 ≤ f + 1) :
    inner.length + 1 ≤ f :=
  Nat.le_of_succ_le_succ (encLenBytes_fuel_budget (f + 1) h)

/-- The same-fuel budget face (the element laws: the element's own
    size + 1 bounds the decode — no decrement to spend). -/
theorem encLenBytes_fuel_budget_at (f : Nat) (M : Nat) (ws : List UInt8)
    (h : (encLenBytes M ws).length + 1 ≤ f) : ws.length + 2 ≤ f := by
  have hw := encLenBytes_ge M ws
  omega

/-- The same-fuel face (the element laws: the element's own size + 1
    bounds the decode — no decrement to spend). -/
theorem encLenBytes_fuel_split_at {f M : Nat} {pre inner tail : List UInt8}
    (h : (pre ++ encLenBytes M inner ++ tail).length + 1 ≤ f) :
    inner.length + 1 ≤ f :=
  Nat.le_of_succ_le (encLenBytes_fuel_budget f h)

/-- The two-wrap face (the message-field face: a frame's wrap around
    the inner body's own wrap) at the decremented fuel. -/
theorem encLenBytes_fuel_split_wrap {f N M : Nat} {pre inner tail rest : List UInt8}
    (h : (encLenBytes N (pre ++ encLenBytes M inner ++ tail) ++ rest).length + 1 ≤ f + 1) :
    inner.length + 1 ≤ f :=
  encLenBytes_fuel_split (f := f) (M := M) (pre := pre) (inner := inner)
    (tail := tail) (by
      have h1 := encLenBytes_fuel_budget (f + 1) (M := N) (pre := [])
        (ws := pre ++ encLenBytes M inner ++ tail) (tail := rest) h
      simp only [List.length_append] at h1 ⊢
      omega)

/-- The two-wrap face at the same fuel (the element laws' frames). -/
theorem encLenBytes_fuel_split_wrap_at {f N M : Nat} {pre inner tail rest : List UInt8}
    (h : (encLenBytes N (pre ++ encLenBytes M inner ++ tail) ++ rest).length + 1 ≤ f) :
    inner.length + 1 ≤ f :=
  encLenBytes_fuel_split_at (f := f) (M := M) (pre := pre) (inner := inner)
    (tail := tail) (by
      have h1 := encLenBytes_fuel_budget f (M := N) (pre := [])
        (ws := pre ++ encLenBytes M inner ++ tail) (tail := rest) h
      simp only [List.length_append] at h1 ⊢
      omega)

/-! ## the signed varint face (the int32/int64 wire rule) -/

/-- The two's-complement 64-bit face of a signed value (the proto
    int32/int64 rule: negatives ride the full 10-byte varint of
    `v + 2^64`). Off-domain values (outside [-2^64, 2^64)) truncate —
    the pinned loss. -/
def twoComp (v : Int) : Nat := ((v + 18446744073709551616) % 18446744073709551616).toNat

/-- The signed read-back: the 64-bit two's-complement interpretation. -/
def signOfNat (v : Nat) : Int :=
  if v < 9223372036854775808 then (v : Int) else (v : Int) - 18446744073709551616

/-- Write a signed varint (the int32/int64 wire rule). -/
def encI64 (v : Int) : List UInt8 := encVarNat (twoComp v)

/-- Read a signed varint. -/
def decI64? (bs : List UInt8) : Option (Int × List UInt8) :=
  (decVarNat? bs).map fun (v, rest) => (signOfNat v, rest)

/-- The nil-suffix corollaries (the full face at rest = []; stated in
    the SELF form because `simp` normalizes `X ++ []` away — the append
    laws' shapes must survive it). -/
theorem decVarField?_encVarField (f v : Nat) :
    decVarField? f (encVarField f v) = some (.more v []) := by
  rw [← List.append_nil (encVarField f v), decVarField?_encVarField_append]

theorem decLenField?_encLenBytes (f : Nat) (payload : List UInt8) :
    decLenField? f (encLenBytes f payload) = some (.more payload []) := by
  rw [← List.append_nil (encLenBytes f payload), decLenField?_encLenBytes_append]

/-- PATTERN #2 — the signed varint's append-form law ON THE ADMISSIBLE
    64-BIT RANGE (pattern #18's conditional form: the off-domain
    truncation is the pinned loss, SubstraitTests). -/
theorem decI64?_encI64_append : ∀ (v : Int), -9223372036854775808 ≤ v →
    v < 9223372036854775808 → ∀ (rest : List UInt8),
    decI64? (encI64 v ++ rest) = some (v, rest) := by
  intro v hlo hhi rest
  simp only [encI64, decI64?]
  by_cases hneg : v < 0
  · -- negative: the two's complement is `v + 2^64` (the 10-byte form),
    -- whose unsigned value lands in [2^63, 2^64) — the subtract branch
    have h2c : twoComp v = (v + 18446744073709551616).toNat := by
      unfold twoComp
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
    have hbig : ¬((v + 18446744073709551616).toNat < 9223372036854775808) := by
      have hmax := Int.toNat_eq_max (v + 18446744073709551616)
      omega
    rw [h2c, decVarNat?_encVarNat_append]
    simp only [Option.map_some, Option.some.injEq]
    unfold signOfNat
    rw [if_neg hbig, Int.toNat_of_nonneg (show 0 ≤ v + 18446744073709551616 by omega)]
    rw [show (v + 18446744073709551616 - 18446744073709551616 : Int) = v from by omega]
  · -- non-negative: the two's complement is the value itself
    have h2c : twoComp v = v.toNat := by
      unfold twoComp
      rw [Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    have hsmall : v.toNat < 9223372036854775808 := by
      have hmax := Int.toNat_eq_max v
      have hle : 0 ≤ v := by omega
      omega
    rw [h2c, decVarNat?_encVarNat_append]
    simp only [Option.map_some, Option.some.injEq]
    unfold signOfNat
    rw [if_pos hsmall, Int.toNat_of_nonneg (show 0 ≤ v by omega)]

/-- The signed varint's NIL face (the self form). -/
theorem decI64?_encI64 : ∀ (v : Int), -9223372036854775808 ≤ v →
    v < 9223372036854775808 → decI64? (encI64 v) = some (v, []) := by
  intro v hlo hhi
  rw [← List.append_nil (encI64 v), decI64?_encI64_append v hlo hhi]

/-! ## the string face (the ASCII fragment) -/

/-- The string face's char byte: the codepoint's low byte — EXACT on
    the ASCII fragment (the inDomain gate), truncating off it (the
    pinned loss, SubstraitTests). The full UTF-8 face rides TextKit's
    char level — the named follow-up. -/
def charByte (c : Char) : UInt8 := (c.toNat % 256).toUInt8

/-- The byte's char read-back (total: every byte is a codepoint). -/
def byteChar (b : UInt8) : Char := Char.ofNat b.toNat

/-- The wire's string bytes (total; exact on the ASCII fragment). -/
def encStr (s : String) : List UInt8 := s.toList.map charByte

/-- The string read-back: the ASCII gate's face — a byte ≥ 128 is the
    off-domain REFUSAL (a typed none, never a silent misparse). -/
def bytesToStr? : List UInt8 → Option String
  | [] => some ""
  | b :: rest =>
      if b.toNat < 128 then
        match bytesToStr? rest with
        | some s => some (String.ofList (Char.ofNat b.toNat :: s.toList))
        | none => none
      else none

/-- The byte round trip is the char identity on the ASCII fragment. -/
theorem byteChar_charByte (c : Char) (h : c.toNat < 128) :
    byteChar (charByte c) = c := by
  have hbyte : (charByte c).toNat = c.toNat := by
    show ((c.toNat % 256).toUInt8).toNat = c.toNat
    rw [UInt8.toNat_ofNat_of_lt' (show c.toNat % 256 < 256 by omega)]
    omega
  simp [byteChar, hbyte]

/-- The char-list face of the round trip (the induction's carrier). -/
theorem bytesToStr?_ofChars : ∀ (cs : List Char), (∀ c ∈ cs, c.toNat < 128) →
    bytesToStr? (cs.map charByte) = some (String.ofList cs) := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c tl ih =>
      intro h
      have hc : c.toNat < 128 := h c (by simp)
      have hbyte : (charByte c).toNat = c.toNat := by
        show (((c.toNat % 256 : Nat)).toUInt8).toNat = c.toNat
        rw [UInt8.toNat_ofNat_of_lt' (show c.toNat % 256 < 256 by omega)]
        omega
      simp only [List.map_cons, bytesToStr?, hbyte]
      rw [if_pos hc]
      rw [ih (fun u hu => h u (by simp [hu]))]
      simp

/-- PATTERN #2 — the string face's round trip, EXACT on the ASCII
    fragment (the off-domain face — refusal for a high byte, corruption
    for a codepoint above 255 — is the pinned control,
    SubstraitTests). -/
theorem bytesToStr?_encStr (s : String)
    (h : s.toList.all (fun c => c.toNat < 128)) :
    bytesToStr? (encStr s) = some s := by
  have hall : ∀ c ∈ s.toList, c.toNat < 128 :=
    fun c hc => of_decide_eq_true (List.all_eq_true.mp h c hc)
  have hofl : s = String.ofList s.toList := by simp
  show bytesToStr? (s.toList.map charByte) = some s
  rw [bytesToStr?_ofChars s.toList hall, String.ofList_toList, hofl]

/-- The ASCII gate (the string fields' admissible subdomain — shared
    by every lane's inDomain face). -/
def inDomainStr (s : String) : Bool := s.toList.all (fun c => c.toNat < 128)

/-- The ASCII list gate. -/
def inDomainStrs : List String → Bool
  | [] => true
  | s :: ss => inDomainStr s && inDomainStrs ss

/-- The list gate's per-element face (the walk's read-back). -/
theorem inDomainStrs_self : ∀ (xs : List String) (s : String), s ∈ xs →
    inDomainStrs xs = true → inDomainStr s = true := by
  intro xs
  induction xs with
  | nil => intro s h; cases h
  | cons y tl ih =>
      intro s h htrue
      simp only [inDomainStrs, Bool.and_eq_true] at htrue
      rcases List.mem_cons.mp h with rfl | htl
      · exact htrue.1
      · exact ih s htl htrue.2

/-! ## the message-combinator layer (the message decoders' shared faces) -/

/-- The oneof wrapper: a tag + its length-delimited payload + the rest
    (every oneof-bearing body decoder's first step). Empty/malformed
    input is `none` (a oneof REQUIRES a tag). -/
def decOneof? (bs : List UInt8) : Option (Nat × List UInt8 × List UInt8) :=
  match decTag? bs with
  | none => none
  | some (f, w, rest) =>
      if w = 2 then
        match decVarNat? rest with
        | none => none
        | some (len, rest') =>
            match takeBytes? len rest' with
            | some (payload, rest'') => some (f, payload, rest'')
            | none => none
      else none

/-- PATTERN #2 — the oneof wrapper's append-form law. -/
theorem decOneof?_encLenBytes_append (f : Nat) (payload rest : List UInt8) :
    decOneof? (encLenBytes f payload ++ rest) = some (f, payload, rest) := by
  have hsplit : encLenBytes f payload ++ rest
      = encTag f wtLen ++ (encVarNat payload.length ++ (payload ++ rest)) := by
    simp only [encLenBytes, List.append_assoc]
  rw [hsplit]
  simp only [decOneof?]
  rw [decTag?_encTag_append f wtLen (by unfold wtLen; decide)]
  simp only [wtLen]
  simp [decVarNat?_encVarNat_append, takeBytes?_append]

/-- The oneof wrapper's NIL form (the self form — the payload fully
    consumed). -/
theorem decOneof?_encLenBytes (f : Nat) (payload : List UInt8) :
    decOneof? (encLenBytes f payload) = some (f, payload, []) := by
  rw [← List.append_nil (encLenBytes f payload), decOneof?_encLenBytes_append]

/-- The message-field face: a length-delimited field whose payload is a
    fully-consumed message body (the dec face is the UNIFORM fueled
    step-decoder form — the recursive bodies self-call at `fuel`). -/
def decField? (field : Nat) (dec : Nat → List UInt8 → Option (Step α)) (fuel : Nat)
    (bs : List UInt8) : Option (Step α) :=
  match decLenField? field bs with
  | some (Step.more payload rest) =>
      match dec fuel payload with
      | some (Step.more a []) => some (Step.more a rest)
      | _ => none
  | some (Step.stop rest) => some (Step.stop rest)
  | none => none

/-- PATTERN #2 — the message-field face's append-form law. NOTE: this
    face is for the NON-RECURSIVE bodies only — a recursive body's
    decoder cannot appear as a first-class value here (the partial
    application breaks the structural-recursion check); the recursive
    arms INLINE this face's body and call the recursive decoder
    directly on the extracted payload (the fuel stays the structural
    argument). -/
theorem decField?_encLenBytes_append (field : Nat) (enc : α → List UInt8)
    (dec : Nat → List UInt8 → Option (Step α)) (fuel : Nat)
    (h : ∀ (a : α) (rest : List UInt8), (enc a ++ rest).length + 1 ≤ fuel →
      dec fuel (enc a ++ rest) = some (Step.more a rest))
    (a : α) (hbound : (enc a).length + 1 ≤ fuel) (rest : List UInt8) :
    decField? field dec fuel (encLenBytes field (enc a) ++ rest) = some (Step.more a rest) := by
  simp only [decField?]
  rw [decLenField?_encLenBytes_append]
  dsimp only
  rw [← List.append_nil (enc a), h a [] (by simpa using hbound)]

/-- The full face: a body decoder run on its EXACT bytes (full
    consumption — trailing bytes are malformed). The top-level faces'
    shape. -/
def decFull? (dec : Nat → List UInt8 → Option (Step α)) (fuel : Nat)
    (payload : List UInt8) : Option α :=
  match dec fuel payload with
  | some (Step.more a []) => some a
  | _ => none

/-- The full face's law. -/
theorem decFull?_law (dec : Nat → List UInt8 → Option (Step α)) (enc : α → List UInt8)
    (fuel : Nat)
    (h : ∀ (a : α) (rest : List UInt8), (enc a ++ rest).length + 1 ≤ fuel →
      dec fuel (enc a ++ rest) = some (Step.more a rest))
    (a : α) (hbound : (enc a).length + 1 ≤ fuel) :
    decFull? dec fuel (enc a) = some a := by
  simp only [decFull?]
  rw [← List.append_nil (enc a), h a [] (by simpa using hbound)]

/-- The string-field face: a length-delimited field whose payload is an
    ASCII string (a non-ASCII payload is the off-domain REFUSAL). -/
def decFieldStr? (field : Nat) (bs : List UInt8) : Option (Step String) :=
  match decLenField? field bs with
  | some (Step.more payload rest) =>
      match bytesToStr? payload with
      | some s => some (Step.more s rest)
      | none => none
  | some (Step.stop rest) => some (Step.stop rest)
  | none => none

/-- PATTERN #2 — the string-field face's append-form law ON THE ASCII
    FRAGMENT (the inDomain gate; the off-domain refusal is the pinned
    control). -/
theorem decFieldStr?_encLenBytes_append (field : Nat) (s : String) (rest : List UInt8)
    (h : s.toList.all (fun c => c.toNat < 128)) :
    decFieldStr? field (encLenBytes field (encStr s) ++ rest) = some (Step.more s rest) := by
  simp only [decFieldStr?]
  rw [decLenField?_encLenBytes_append]
  dsimp only
  rw [bytesToStr?_encStr s h]

/-- The string-field face's NIL form. -/
theorem decFieldStr?_encStr (field : Nat) (s : String)
    (h : s.toList.all (fun c => c.toNat < 128)) :
    decFieldStr? field (encLenBytes field (encStr s)) = some (Step.more s []) := by
  rw [← List.append_nil (encLenBytes field (encStr s)),
    decFieldStr?_encLenBytes_append field s [] h]

/-- The bool-field face: a varint field whose payload is 0/1 (anything
    else is malformed — the canonical dialect). -/
def decBoolField? (field : Nat) (bs : List UInt8) : Option (Step Bool) :=
  match decVarField? field bs with
  | some (Step.more v rest) =>
      if v = 1 then some (Step.more true rest)
      else if v = 0 then some (Step.more false rest)
      else none
  | some (Step.stop rest) => some (Step.stop rest)
  | none => none

/-- PATTERN #2 — the bool-field face's append-form law. -/
theorem decBoolField?_encVarField_append (field : Nat) (b : Bool) (rest : List UInt8) :
    decBoolField? field (encVarField field (if b then 1 else 0) ++ rest)
      = some (Step.more b rest) := by
  cases b <;> simp [decBoolField?, decVarField?_encVarField_append]

/-- The bool-field face's NIL form (the self form — the
    `simp`-normalization note at the nil corollaries). -/
theorem decBoolField?_encVarField (field : Nat) (b : Bool) :
    decBoolField? field (encVarField field (if b then 1 else 0))
      = some (Step.more b []) := by
  rw [← List.append_nil (encVarField field (if b then 1 else 0)),
    decBoolField?_encVarField_append]

/-- The enum-field face: a varint field read through a number table. -/
def decEnumField? (field : Nat) (ofNum : Nat → Option α) (bs : List UInt8) : Option (Step α) :=
  match decVarField? field bs with
  | some (Step.more v rest) => (ofNum v).map fun n => Step.more n rest
  | some (Step.stop rest) => some (Step.stop rest)
  | none => none

/-- PATTERN #2 — the enum-field face's append-form law. -/
theorem decEnumField?_encVarField_append (field : Nat) (ofNum : Nat → Option α) (num : α → Nat)
    (hnum : ∀ n, ofNum (num n) = some n) (n : α) (rest : List UInt8) :
    decEnumField? field ofNum (encVarField field (num n) ++ rest) = some (Step.more n rest) := by
  simp only [decEnumField?]
  rw [decVarField?_encVarField_append]
  simp [hnum n]

/-- The enum-field face's NIL form (the self form — see the
    nil-corollaries note). -/
theorem decEnumField?_encVarField (field : Nat) (ofNum : Nat → Option α) (num : α → Nat)
    (hnum : ∀ n, ofNum (num n) = some n) (n : α) :
    decEnumField? field ofNum (encVarField field (num n)) = some (Step.more n []) := by
  rw [← List.append_nil (encVarField field (num n)),
    decEnumField?_encVarField_append field ofNum num hnum n []]

/-- The stop-face lemma for a length-delimited field: the input's tag
    is either absent (empty input — the one empty face) or names a
    DIFFERENT field/wire type. -/
theorem decLenField?_stop (field : Nat) (bs : List UInt8)
    (h0 : decTag? bs = none → bs = [])
    (h : ∀ (f' w' : Nat) (r : List UInt8), decTag? bs = some (f', w', r) →
      ¬(f' = field ∧ w' = wtLen)) :
    decLenField? field bs = some (Step.stop bs) := by
  cases htag : decTag? bs with
  | none =>
      have hnil : bs = [] := h0 htag
      subst hnil
      simp only [decLenField?, htag]
      simp
  | some t =>
      obtain ⟨f', w', r⟩ := t
      have hd := h f' w' r htag
      have hcond : (f' == field && w' == wtLen) = false := by
        cases hbeq : f' == field with
        | false => rfl
        | true =>
            have hf : f' = field := beq_iff_eq.mp hbeq
            cases hweq : w' == wtLen with
            | false => rfl
            | true => exact absurd ⟨hf, beq_iff_eq.mp hweq⟩ hd
      simp only [decLenField?, htag]
      simp [hcond]

/-- The message-field face's stop face (the same discrimination). -/
theorem decField?_stop (field : Nat) (dec : Nat → List UInt8 → Option (Step α)) (fuel : Nat)
    (bs : List UInt8)
    (h0 : decTag? bs = none → bs = [])
    (h : ∀ (f' w' : Nat) (r : List UInt8), decTag? bs = some (f', w', r) →
      ¬(f' = field ∧ w' = wtLen)) :
    decField? field dec fuel bs = some (Step.stop bs) := by
  simp only [decField?, decLenField?_stop field bs h0 h]

/-- The string-field face's stop face (the same discrimination). -/
theorem decFieldStr?_stop (field : Nat) (bs : List UInt8)
    (h0 : decTag? bs = none → bs = [])
    (h : ∀ (f' w' : Nat) (r : List UInt8), decTag? bs = some (f', w', r) →
      ¬(f' = field ∧ w' = wtLen)) :
    decFieldStr? field bs = some (Step.stop bs) := by
  simp only [decFieldStr?, decLenField?_stop field bs h0 h]

/-- The other-tag stop face: a length-delimited field of a DIFFERENT
    number ends the parse (the optional-field face's engine — the tag
    discrimination via `decTag?_encTag_append`'s injective verdict). -/
theorem decLenField?_other_stop (field field' : Nat) (payload rest : List UInt8)
    (hne : field ≠ field') :
    decLenField? field (encLenBytes field' payload ++ rest)
      = some (Step.stop (encLenBytes field' payload ++ rest)) := by
  apply decLenField?_stop
  · intro hh
    rw [show encLenBytes field' payload ++ rest
          = encTag field' wtLen
            ++ (encVarNat payload.length ++ (payload ++ rest)) from by
          simp only [encLenBytes, List.append_assoc]] at hh
    rw [decTag?_encTag_append field' wtLen (by unfold wtLen; decide)] at hh
    exact absurd hh (by simp)
  · intro f' w' r htag
    rw [show encLenBytes field' payload ++ rest
          = encTag field' wtLen
            ++ (encVarNat payload.length ++ (payload ++ rest)) from by
          simp only [encLenBytes, List.append_assoc]] at htag
    rw [decTag?_encTag_append field' wtLen (by unfold wtLen; decide)] at htag
    have h1 : field' = f' :=
      congrArg (fun t : Nat × Nat × List UInt8 => t.1) (Option.some.inj htag)
    exact fun hh => hne (h1.trans hh.left).symm

/-- The length-delimited scan over a VARINT-tagged stream: a varint
    field's tag has wire type 0 — never the length-delimited face — so
    the scan stops there (the optional-field face at a varint tag,
    e.g. an optional metadata field absent before a trailing flag). -/
theorem decLenField?_varint_stop (f f' v : Nat) (rest : List UInt8) (_hne : f ≠ f') :
    decLenField? f (encVarField f' v ++ rest)
      = some (Step.stop (encVarField f' v ++ rest)) := by
  apply decLenField?_stop
  · intro hh
    rw [show encVarField f' v ++ rest
          = encTag f' wtVarint ++ (encVarNat v ++ rest) from by
          simp only [encVarField, List.append_assoc]] at hh
    rw [decTag?_encTag_append f' wtVarint (by unfold wtVarint; decide)] at hh
    exact absurd hh (by simp)
  · intro g w' r htag
    rw [show encVarField f' v ++ rest
          = encTag f' wtVarint ++ (encVarNat v ++ rest) from by
          simp only [encVarField, List.append_assoc]] at htag
    rw [decTag?_encTag_append f' wtVarint (by unfold wtVarint; decide)] at htag
    have h1 : wtVarint = w' :=
      congrArg (fun t : Nat × Nat × List UInt8 => t.2.1) (Option.some.inj htag)
    intro hh
    have h2 : wtLen = wtVarint := hh.2 ▸ h1.symm
    unfold wtLen wtVarint at h2
    exact absurd h2 (by decide)

/-- The other-tag stop face's NIL form (the optional-field face's
    read-back at the payload's end). -/
theorem decLenField?_other_stop_nil (field field' : Nat) (payload : List UInt8)
    (hne : field ≠ field') :
    decLenField? field (encLenBytes field' payload)
      = some (Step.stop (encLenBytes field' payload)) := by
  simpa using decLenField?_other_stop field field' payload [] hne

/-! ## the clean-suffix discipline (the rep-terminated streams' face) -/

/-- A CLEAN SUFFIX: the bytes' next tag is NOT a length-delimited field
    (or the bytes end) — every length-delimited rep terminates there,
    whatever field number it scans for. The append-form laws' suffix
    face wherever a repeated field ends the message (the clean-suffix
    discipline; Substrait.Text's FollowClean is the text twin). -/
def CleanBytes (rest : List UInt8) : Prop :=
  match decTag? rest with
  | none => rest = []
  | some (_, w, _) => w ≠ wtLen

theorem CleanBytes.nil : CleanBytes [] := rfl

/-- A varint field's bytes are a clean suffix (its wire type is 0 —
    the rep-termination face at a trailing varint field, e.g. a
    nullability flag ending a message body). -/
theorem cleanVarField (f v : Nat) : CleanBytes (encVarField f v) := by
  have htag : decTag? (encVarField f v) = some (f, wtVarint, encVarNat v) := by
    rw [show encVarField f v = encTag f wtVarint ++ encVarNat v from rfl,
        decTag?_encTag_append f wtVarint (by unfold wtVarint; decide)]
  rw [CleanBytes, htag]
  intro h
  unfold wtVarint wtLen at h
  exact absurd h (by decide)

/-- The clean suffix's read: the length-delimited parse STOPS there. -/
theorem decLenField?_clean (f : Nat) : ∀ rest : List UInt8, CleanBytes rest →
    decLenField? f rest = some (Step.stop rest) := by
  intro rest hc
  match htag : decTag? rest with
  | none =>
      have hnil : rest = [] := by
        unfold CleanBytes at hc
        rw [htag] at hc
        exact hc
      subst hnil
      rfl
  | some (f', w', r) =>
      have hwne : w' ≠ wtLen := by
        unfold CleanBytes at hc
        rw [htag] at hc
        exact hc
      have hcond : ¬ (f' == f && w' == wtLen) = true := by
        intro hcon
        simp only [Bool.and_eq_true] at hcon
        exact hwne (beq_iff_eq.mp hcon.2)
      simp only [decLenField?, htag]
      rw [if_neg hcond]

/-- The rep's stop face at a clean suffix (the rep laws' `hend`), for
    any element decoder that passes `decLenField? n`'s stop through. -/
theorem decElem?_clean {α : Type} (elem : List UInt8 → Option (Step α)) (n : Nat)
    (hshape : ∀ (bs : List UInt8), decLenField? n bs = some (Step.stop bs) →
      elem bs = some (Step.stop bs))
    (rest : List UInt8) (hc : CleanBytes rest) :
    elem rest = some (Step.stop rest) :=
  hshape rest (decLenField?_clean n rest hc)

/-- The string-field face's clean stop face (the rep-element reading
    of the clean-suffix discipline). -/
theorem decFieldStr?_clean (field : Nat) (rest : List UInt8) (hc : CleanBytes rest) :
    decFieldStr? field rest = some (Step.stop rest) :=
  decElem?_clean (decFieldStr? field) field
    (fun bs h => by simp only [decFieldStr?, h]) rest hc

/-! ## the WireTarget row (the design-forward-surface §2 checklist, as data) -/

/-- The correspondence grade, as data — the Kit.Correspondence
    vocabulary's names cited by name (the wire's cone imports no
    Kit.Correspondence; the grades' definitions live there:
    `Iso` > `Codec` > `Retraction`). `conditionalRetraction` = the
    honest CONDITIONAL face: the law holds on the inDomain subdomain
    (the emission boundary's gate) — never a fake full Codec. -/
inductive WireGrade where
  | iso | codec | retraction
  | conditionalRetraction (why : String)
deriving Repr, BEq, Inhabited

/-- The evidence entourage, as data (16 §3's computed tiers, the wire
    face): the vectors' lane, the goldens channel, the negative
    controls' row, the 13-interfaces row id. -/
structure WireEntourage where
  vectors : Bool
  goldens : Bool
  controls : Bool
  ifaceRow : String
deriving Repr, BEq, Inhabited

/-- ONE wire format (the byte carrier): the encoder + the fueled body
    decoder + THE LAW (the append-form round trip on the admissible
    subdomain, with the format's clean-suffix discipline) + the gate +
    the off-domain controls + the grade + the entourage. The
    design-forward-surface §2 checklist, SCANABLE: a format lands as a
    row; its evidence tier is read off the row; the 07-recipe row and
    the 13-interfaces row are generated from it (the docs-check reads
    it). The byte carrier is the proven one here (the grammar carrier
    rides TextKit.Grammar's own laws — Substrait.Text's round-trip law
    is that face's precedent; a grammar-carrier row is the named
    follow-up). No new law machinery, no new gate, no new vector
    convention. -/
structure WireTarget (A : Type) where
  /-- the bytes -/
  enc : A → List UInt8
  /-- the fueled body decoder (the Step face carries the rest) -/
  dec : Nat → List UInt8 → Option (Step A)
  /-- the admissible subdomain (the emission boundary's gate) -/
  inDomain : A → Bool
  /-- the clean-suffix discipline (the rep-terminated streams' face) -/
  clean : List UInt8 → Prop
  /-- THE LAW: the append-form round trip, inDomain- +
      clean-conditional; a format whose law is deferred carries the
      DEFERRED ROW here (Substrait.Text's list arm is the precedent) —
      never a missing field. -/
  law : ∀ (fuel : Nat) (a : A) (rest : List UInt8), inDomain a = true →
    (enc a ++ rest).length + 1 ≤ fuel → clean rest →
    dec fuel (enc a ++ rest) = some (Step.more a rest)
  /-- the off-domain controls: values OUTSIDE the subdomain — the
      off-domain face is PINNED (pattern #5), never a silent law gap -/
  offDomain : List A
  offDomainProof : ∀ a ∈ offDomain, inDomain a = false
  grade : WireGrade
  entourage : WireEntourage

end Kit.Proto

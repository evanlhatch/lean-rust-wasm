/-
# SchemaLang.Codec — kernel-checked round-trip laws (the linen pattern)

Linen's JSON module proves `decode ∘ encode = id` instead of asserting
it; flatland's `ExtMetadata` applies the same law to its metadata
shapes. This module starts OUR codec layer with the trivially-provable
subset (Bool, UInt8): the law shape is the deliverable — string
codecs (UTF-8) hit the core-lemma gap flatland documented and get
executable witnesses in Tests instead.

Encoding: one byte per value, little alphabet. Decoding rejects
everything else (wrong length, out of domain) — the failure cases are
exactly the Rust-side checks when the schema compiler emits codecs.

The rest of the module is the binary combinator layer (refactor-guide
5.5.1 + 5.5.7, ported from the flatland lineage — RecipeWire/Lifecycle
— with all game content stripped):

- `encVarNat`/`decVarNat`: the LEB128 varint base, self-delimiting;
- generic combinators `encOpt/decOpt?`, `encProd/decProd?`,
  `encList/decList?` (length-prefixed), `encEnum/decEnum?`,
  `encBytes/decBytes?` (length-prefixed byte strings);
- every lemma is stated in the APPEND form
  `decX? (encX a ++ rest) = some (a, rest)` so per-field lemmas compose
  into whole-structure round-trips by `simp` alone;
- `encEnvelope`/`decEnvelope?`: the versioned-envelope convention
  (version + fingerprint as the first wire fields, payload length-
  prefixed), with the round-trip and wrong-version rejection proved.
- `LawfulCodec`: the SAME append-form law surface re-shaped once as a
  TYPE CLASS (`enc`/`dec`/`roundtrip`) — the instances are the existing
  append-form theorems restated as instance fields (nothing re-proved),
  so instance search and the theorem surface are one law system.

Decode is PARTIAL at the combinator level (`Option`) — malformed bytes
decode to `none`. `decVarNat` itself is total (empty input decodes to
`(0, [])`); truncation REJECTION comes from the combinators layered on
top (tag mismatch, length-prefix overrun, trailing-garbage check).
-/

module

public import SchemaLang.Ty
public import CodegenCore.GuestGate

@[expose] public section

namespace SchemaLang.Codec

/-! ## Bool -/

def encodeBool : Bool → List UInt8
  | .false => [0]
  | .true => [1]

def decodeBool : List UInt8 → Option Bool
  | [0] => some false
  | [1] => some true
  | _ => none

theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = some b := by
  cases b <;> rfl

/-! ## UInt8 -/

def encodeU8 : UInt8 → List UInt8
  | v => [v]

def decodeU8 : List UInt8 → Option UInt8
  | [v] => some v
  | _ => none

/-- Round-trip by exhaustive enumeration — 256 cases, closed domain
    (the flatland exhaustive-byte-sweep doctrine, as a theorem). -/
theorem decode_encodeU8 (v : UInt8) : decodeU8 (encodeU8 v) = some v := by
  cases v <;> rfl

/-! ## Append-form atoms

The whole-list atoms above get self-delimiting companions returning the
value AND the remaining bytes — the shape the combinators consume. -/

/-- Bool, append-form: decode one tag byte, pass the rest through. -/
def decBool? : List UInt8 → Option (Bool × List UInt8)
  | 0 :: rest => some (false, rest)
  | 1 :: rest => some (true, rest)
  | _ => none

@[simp] theorem decBool_encodeBool_append (b : Bool) (rest : List UInt8) :
    decBool? (encodeBool b ++ rest) = some (b, rest) := by
  cases b <;> rfl

/-- UInt8, append-form: consume one byte. -/
def decU8? : List UInt8 → Option (UInt8 × List UInt8)
  | b :: rest => some (b, rest)
  | [] => none

@[simp] theorem decU8_encodeU8_append (v : UInt8) (rest : List UInt8) :
    decU8? (encodeU8 v ++ rest) = some (v, rest) := rfl

/-! ## Varint base (LEB128) -/

/-- Variable-length base-128 digits, little-endian; every digit but the
    last carries the continuation (0x80) bit — self-delimiting, so a
    length-prefixed field's end is known and the following field starts
    immediately after. -/
def encVarNat : Nat → List UInt8
  | n => if n < 128 then [UInt8.ofNat n]
    else UInt8.ofNat (128 + n % 128) :: encVarNat (n / 128)
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by decide : 1 < 128)

/-- Decode a varint prefix: returns (value, remaining bytes). The high
    bit is the continuation; the DECODER stops at the first low-bit
    digit, which is exactly the last digit — the following bytes remain
    untouched (see `decVarNat_append`). Total: empty input is `(0, [])`. -/
def decVarNat : List UInt8 → Nat × List UInt8
  | [] => (0, [])
  | b :: rest =>
      if _ : b.toNat < 128 then (b.toNat, rest)
      else
        let p := decVarNat rest
        (b.toNat - 128 + 128 * p.1, p.2)

 -- THE GUEST MARK (W9.6's decode lane — the bounded-Nat decision
 -- extends to the varint reassembly): the decode surface is
 -- `Nat.decLt` (the digit-domain test) + `Nat.sub`/`Nat.add`/`Nat.mul`
 -- (the reassembly `b.toNat - 128 + 128 * p.1`) — ALL bounded by
 -- construction: a digit is < 128, the reassembly's value is the
 -- encoded Nat (the encoded length IS the bound), and the backend's
 -- pinned 2^62 cap + `encVarNat`'s own wire make overflow a design
 -- error, exactly as for the fuel countdown. `decVarNat` is
 -- wf-recursive (`termination_by`): the kernel never unfolds it (the
 -- known trap) — the round-trip laws cite `decVarNat.eq_def`-based
 -- rewrites, and the GUEST compiles the wf fixpoint through the
 -- closure machinery (verified: the wasm-gen lane + the duel rows).
 -- Every other decoder below inherits this mark's rationale through
 -- composition — the marks are per-decl for the manifest fold's
 -- granularity, the bounded-Nat note lives HERE.
attribute [guest_std] decVarNat

@[simp] theorem UInt8.ofNat_toNat_of_lt (n : Nat) (h : n < 256) :
    (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- The varint is self-delimiting: decoding `encVarNat n ++ rest`
    consumes exactly the digits of n and returns the rest untouched. -/
theorem decVarNat_append (n : Nat) (rest : List UInt8) :
    decVarNat (encVarNat n ++ rest) = (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hlt : n < 128
      · -- single byte: `encVarNat n = [UInt8.ofNat n]`
        have hn8 : n < 256 := by omega
        have hb : (UInt8.ofNat n).toNat = n := UInt8.ofNat_toNat_of_lt n hn8
        rw [encVarNat]
        rw [if_pos hlt]
        rw [decVarNat.eq_def]
        simp [hb, hlt]
      · -- continuation byte + recursion
        have hge : 128 ≤ n := by omega
        have hmod : n % 128 < 128 := Nat.mod_lt n (by decide : 0 < 128)
        have hb : (UInt8.ofNat (128 + n % 128)).toNat = 128 + n % 128 := by
          apply UInt8.ofNat_toNat_of_lt
          omega
        have hncont : ¬ 128 + n % 128 < 128 := by omega
        have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by decide : 1 < 128)
        have hdm : n % 128 + 128 * (n / 128) = n := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using (Nat.div_add_mod n 128)
        have hm256 : (128 + n % 128) % 256 = 128 + n % 128 :=
          Nat.mod_eq_of_lt (by omega)
        rw [encVarNat]
        rw [if_neg hlt]
        rw [decVarNat.eq_def]
        simp [hm256, hncont, ih (n / 128) hdiv, hdm]

/-- The plain round trip (no trailing bytes). -/
theorem decVarNat_encVarNat (n : Nat) : decVarNat (encVarNat n) = (n, []) := by
  simpa using (decVarNat_append n ([] : List UInt8))

/-- Nat element over the varint, wrapped into the `Option` element-
    decoder shape the generic combinators consume. -/
@[guest_std]
def decNat? (bs : List UInt8) : Option (Nat × List UInt8) := some (decVarNat bs)

@[simp] theorem decNat_encVarNat_append (n : Nat) (rest : List UInt8) :
    decNat? (encVarNat n ++ rest) = some (n, rest) := by
  simp [decNat?, decVarNat_append]

/-- A varint is never the empty byte string (every Nat emits at least
    one digit) — the bound the fueled tree decoders' entry fuel
    (`bytes + 1`) rides: one byte per tree node at minimum. -/
theorem length_encVarNat_pos (n : Nat) : 0 < (encVarNat n).length := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [encVarNat]
      split
      · simp
      · rename_i hlt
        have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by decide : 1 < 128)
        have := ih (n / 128) hdiv
        simp only [List.length_cons]
        omega

/-! ## Generic combinators -/

/-- `Option`: tag byte 0 = none, 1 = some followed by the element. -/
def encOpt (enc : α → List UInt8) : Option α → List UInt8
  | none => [0]
  | some a => 1 :: enc a

@[guest_std]
def decOpt? (dec : List UInt8 → Option (α × List UInt8)) :
    List UInt8 → Option (Option α × List UInt8)
  | 0 :: rest => some (none, rest)
  | 1 :: rest => (dec rest).map fun (a, r) => (some a, r)
  | _ => none

theorem decOpt_encOpt_append (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (h : ∀ (a : α) (rest : List UInt8), dec (enc a ++ rest) = some (a, rest))
    (a : Option α) (rest : List UInt8) :
    decOpt? dec (encOpt enc a ++ rest) = some (a, rest) := by
  cases a with
  | none => simp [encOpt, decOpt?]
  | some v => simp [encOpt, decOpt?, List.cons_append, h v rest]

/-- Pair: `encA p.1 ++ encB p.2` (both self-delimiting). -/
def encProd (encA : α → List UInt8) (encB : β → List UInt8) (p : α × β) :
    List UInt8 := encA p.1 ++ encB p.2

def decProd? (decA : List UInt8 → Option (α × List UInt8))
    (decB : List UInt8 → Option (β × List UInt8)) (bs : List UInt8) :
    Option ((α × β) × List UInt8) :=
  (decA bs).bind fun (a, r1) => (decB r1).map fun (b, r2) => ((a, b), r2)

theorem decProd_encProd_append (encA : α → List UInt8) (encB : β → List UInt8)
    (decA : List UInt8 → Option (α × List UInt8))
    (decB : List UInt8 → Option (β × List UInt8))
    (hA : ∀ (a : α) (rest : List UInt8), decA (encA a ++ rest) = some (a, rest))
    (hB : ∀ (b : β) (rest : List UInt8), decB (encB b ++ rest) = some (b, rest))
    (p : α × β) (rest : List UInt8) :
    decProd? decA decB (encProd encA encB p ++ rest) = some (p, rest) := by
  obtain ⟨a, b⟩ := p
  simp [encProd, decProd?, hA a (encB b ++ rest), hB b rest]

/-- Length-prefixed list of self-delimiting elements. -/
def encList (enc : α → List UInt8) (as : List α) : List UInt8 :=
  encVarNat as.length ++ (as.map enc).flatten

/-- Decode `m` self-delimiting elements. -/
@[guest_std]
def decManyBind? (dec : List UInt8 → Option (α × List UInt8)) :
    (m : Nat) → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | m + 1, bs =>
      match dec bs with
      | none => none
      | some (a, rest) =>
          match decManyBind? dec m rest with
          | none => none
          | some (as, rest') => some (a :: as, rest')

@[guest_std]
def decList? (dec : List UInt8 → Option (α × List UInt8)) (bs : List UInt8) :
    Option (List α × List UInt8) :=
  decManyBind? dec (decVarNat bs).1 (decVarNat bs).2

theorem decManyBind_enc_append (dec : List UInt8 → Option (α × List UInt8))
    (enc : α → List UInt8)
    (h : ∀ (a : α) (rest : List UInt8), dec (enc a ++ rest) = some (a, rest))
    (as : List α) (rest : List UInt8) :
    decManyBind? dec as.length ((as.map enc).flatten ++ rest) = some (as, rest) := by
  induction as generalizing rest with
  | nil => simp [decManyBind?]
  | cons a as ih =>
      simp only [decManyBind?, List.length_cons, List.map_cons, List.flatten_cons,
        List.append_assoc]
      rw [h a ((as.map enc).flatten ++ rest)]
      simp [ih rest]

theorem decList_encList_append (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (h : ∀ (a : α) (rest : List UInt8), dec (enc a ++ rest) = some (a, rest))
    (as : List α) (rest : List UInt8) :
    decList? dec (encList enc as ++ rest) = some (as, rest) := by
  show decManyBind? dec (decVarNat (encList enc as ++ rest)).1
      (decVarNat (encList enc as ++ rest)).2 = some (as, rest)
  rw [show encList enc as = encVarNat as.length ++ (as.map enc).flatten from rfl,
    List.append_assoc, decVarNat_append]
  exact decManyBind_enc_append dec enc h as rest

/-- Enum tag as a varint; the closed `ofTag?` rejects out-of-range tags. -/
def encEnum (t : Nat) : List UInt8 := encVarNat t

@[guest_std]
def decEnum? (ofTag? : Nat → Option α) (bs : List UInt8) : Option (α × List UInt8) :=
  match decVarNat bs with
  | (n, rest) =>
      match ofTag? n with
      | none => none
      | some v => some (v, rest)

theorem decEnum_encEnum_append (tag : α → Nat) (ofTag? : Nat → Option α)
    (h : ∀ a, ofTag? (tag a) = some a) (a : α) (rest : List UInt8) :
    decEnum? ofTag? (encEnum (tag a) ++ rest) = some (a, rest) := by
  simp [encEnum, decEnum?, decVarNat_append, h a]

/-- Length-prefixed byte string (`encVarNat len ++ bs`). -/
def encBytes (bs : List UInt8) : List UInt8 :=
  encVarNat bs.length ++ bs

/-- THE GUEST-COMPILABLE TAKE (the W9.6 decode lane's one Codec body
    change, beyond the marks — flagged): core's `List.take` specializes
    to `takeTR.go`, whose accumulator is an ARRAY (`Array.mkEmpty` — an
    `@[extern]` decl the backend compiles as an unreachable stub: the
    guest has no Array lane). `takeB` is the structural cons-walk —
    order-preserving, no accumulator — over the same semantics: the
    caller's `n ≤ length` gate makes the short-list case dead.
    (`List.drop` stays core: its impl is a plain Nat/List walk.) -/
def takeB : (n : Nat) → List UInt8 → List UInt8
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, b :: bs => b :: takeB n bs

theorem takeB_append (bs rest : List UInt8) :
    takeB bs.length (bs ++ rest) = bs := by
  induction bs generalizing rest with
  | nil => simp [takeB]
  | cons b bs ih => simp [List.length_cons, List.cons_append, takeB, ih]

theorem drop_length_append (bs rest : List UInt8) :
    List.drop bs.length (bs ++ rest) = rest := by
  rw [List.drop_append, Nat.sub_self]
  simp [List.drop_eq_nil_of_le (Nat.le_refl bs)]

/-- Decode one length-prefixed byte field: the next `n` bytes (n read
    from the varint) plus the trailing remainder. Truncation REJECTS:
    fewer than `n` bytes available is `none`. -/
@[guest_std]
def decBytes? (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let (n, rest) := decVarNat bs
  if _ : n ≤ rest.length then some (takeB n rest, rest.drop n) else none

@[simp] theorem decBytes_encBytes_append (bs rest : List UInt8) :
    decBytes? (encBytes bs ++ rest) = some (bs, rest) := by
  unfold decBytes? encBytes
  rw [List.append_assoc, decVarNat_append bs.length (bs ++ rest)]
  have hle : bs.length ≤ (bs ++ rest).length := by
    simp [List.length_append]
  -- the match/dif reduce with the length gate decided; the take/drop
  -- laws deliver the fields
  simp only [hle, takeB_append, drop_length_append, dite_true]

/-- The plain round trip (no trailing bytes). -/
theorem decBytes_encBytes (bs : List UInt8) :
    decBytes? (encBytes bs) = some (bs, []) := by
  simpa using decBytes_encBytes_append bs []

/-! ## UInt64 + String atoms (W9.1 — the witness lane's scalars)

UInt64 rides its `toNat` varint (canonical on encode; decode accepts —
and wraps — any varint; the law is decode∘encode). Strings are
length-prefixed CHAR LISTS, not UTF-8 bytes: core ships no
`fromUTF8? ∘ toUTF8` round-trip lemma (the gap this module's header
documents), so the provable atom is `encList` of `Char.toNat` varints
and the law rides `String.ofList_toList` + `Char.ofNat_toNat`. -/

/-- UInt64 as its `toNat` varint. -/
def encU64 (v : UInt64) : List UInt8 := encVarNat v.toNat

/-- Decode a UInt64 varint (accepts any varint, wrapping — the
    encoder's range is always in-domain). -/
-- `UInt64.ofNat` in the guest int model: the boxed-Nat payload →
-- the raw u64 (wrapping) — the backend's conversion lowering, total.
@[guest_std]
def decU64? (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  (decNat? bs).map fun (n, r) => (UInt64.ofNat n, r)

@[simp] theorem decU64_encU64_append (v : UInt64) (rest : List UInt8) :
    decU64? (encU64 v ++ rest) = some (v, rest) := by
  simp [encU64, decU64?, UInt64.ofNat_toNat]

/-- Char as its `toNat` varint. -/
def encChar (c : Char) : List UInt8 := encVarNat c.toNat

/-- Decode a char varint (`Char.ofNat` is total; the law needs only
    the encoder's range). -/
@[guest_std]
def decChar? (bs : List UInt8) : Option (Char × List UInt8) :=
  (decNat? bs).map fun (n, r) => (Char.ofNat n, r)

@[simp] theorem decChar_encChar_append (c : Char) (rest : List UInt8) :
    decChar? (encChar c ++ rest) = some (c, rest) := by
  simp [encChar, decChar?, Char.ofNat_toNat]

/-- String as a length-prefixed char list (see the section note). -/
def encString (s : String) : List UInt8 := encList encChar s.toList

/-- Decode a char-list string. -/
-- `String.ofList` in the guest: the RUNTIME primitive `$string_oflist`
-- (the StrOps recipe: `GuestlangStd.Intrinsic.strof` maps the name; the
-- guest's string object is built from the char codes' UTF-8 bytes —
-- the ASCII stance of `$string_len` mirrors here as ASCII-only
-- round-trips).
@[guest_std]
def decString? (bs : List UInt8) : Option (String × List UInt8) :=
  (decList? decChar? bs).map fun (cs, r) => (String.ofList cs, r)

@[simp] theorem decString_encString_append (s : String) (rest : List UInt8) :
    decString? (encString s ++ rest) = some (s, rest) := by
  simp [encString, decString?,
    decList_encList_append encChar decChar? (fun c r => decChar_encChar_append c r),
    String.ofList_toList]

/-! ## LawfulCodec: the law-carrying codec class (additive)

The append-form law surface above is re-shaped once here as a TYPE
CLASS. The instances below are the EXISTING append-form theorems
restated as instance fields — each cites the theorem it was proved as
(the rule: cite, don't re-prove). The class is ADDITIVE: the
combinators and theorems above remain the law surface of record; the
instances are an instance-search-able reading of the SAME laws.

Instance coverage notes (the deliberate shape):
- The atoms: Bool, UInt8, Nat (varint), UInt64, Char, String, Bytes.
- The composites compose the element/half laws: Option, Prod, List.
  The tagged-sum instance (`Sum`) lives in SchemaLang.CodecValue (the
  `encSum`/`decSum?` combinators' home).
- `List UInt8` (bytes) is registered BEFORE the generic `List α` so
  the byte-string codec (`encBytes`/`decBytes?`) wins that head. On
  `List UInt8` the two codecs are EXTENSIONALLY the same wire
  (`encU8 = singleton`, so `encList encU8` flattens to the raw bytes)
  — the overlap is behavior-innocuous, but the byte-string reading is
  the honest one, hence the order.
- The membership-restricted laws (below) stay hypothesis-shaped (the
  element law holds only for list MEMBERS) — instance-shaped they have
  no honest home, so the class does not cover recursive wires.
-/

/-- The law-carrying codec class: an append-form
    `decode (encode a ++ rest) = some (a, rest)` round trip, stated on
    the codec pair itself — the class-shaped twin of the combinator
    laws above. -/
class LawfulCodec (α : Type) where
  enc : α → List UInt8
  dec : List UInt8 → Option (α × List UInt8)
  /-- THE LAW: decode (encode a ++ rest) returns the value and the
      untouched remainder. -/
  roundtrip : ∀ (a : α) (rest : List UInt8), dec (enc a ++ rest) = some (a, rest)

/-- Bool: `encodeBool`/`decBool?` — the `decBool_encodeBool_append`
    law. -/
instance lawfulCodecBool : LawfulCodec Bool where
  enc := encodeBool
  dec := decBool?
  roundtrip := decBool_encodeBool_append

/-- UInt8: `encodeU8`/`decU8?` — the `decU8_encodeU8_append` law. -/
instance lawfulCodecU8 : LawfulCodec UInt8 where
  enc := encodeU8
  dec := decU8?
  roundtrip := decU8_encodeU8_append

/-- Nat: the LEB128 varint `encVarNat`/`decNat?` — the
    `decNat_encVarNat_append` law. -/
instance lawfulCodecNat : LawfulCodec Nat where
  enc := encVarNat
  dec := decNat?
  roundtrip := decNat_encVarNat_append

/-- UInt64: `encU64`/`decU64?` — the `decU64_encU64_append` law. -/
instance lawfulCodecU64 : LawfulCodec UInt64 where
  enc := encU64
  dec := decU64?
  roundtrip := decU64_encU64_append

/-- Char: `encChar`/`decChar?` — the `decChar_encChar_append` law. -/
instance lawfulCodecChar : LawfulCodec Char where
  enc := encChar
  dec := decChar?
  roundtrip := decChar_encChar_append

/-- String: `encString`/`decString?` — the
    `decString_encString_append` law. -/
instance lawfulCodecString : LawfulCodec String where
  enc := encString
  dec := decString?
  roundtrip := decString_encString_append

/-- Bytes (`List UInt8`): `encBytes`/`decBytes?` — the
    `decBytes_encBytes_append` law. Registered BEFORE the generic
    `List` instance so byte-strings win the `List UInt8` head (the
    two wires coincide on `List UInt8` — the section note). -/
instance lawfulCodecBytes : LawfulCodec (List UInt8) where
  enc := encBytes
  dec := decBytes?
  roundtrip := decBytes_encBytes_append

/-- Option: `encOpt`/`decOpt?` — composes the element law
    (`decOpt_encOpt_append`). -/
instance lawfulCodecOption [LawfulCodec α] : LawfulCodec (Option α) where
  enc := encOpt (LawfulCodec.enc (α := α))
  dec := decOpt? (LawfulCodec.dec (α := α))
  roundtrip := decOpt_encOpt_append (LawfulCodec.enc (α := α))
    (LawfulCodec.dec (α := α)) (LawfulCodec.roundtrip (α := α))

/-- Prod: `encProd`/`decProd?` — composes the two halves' laws
    (`decProd_encProd_append`). -/
instance lawfulCodecProd [LawfulCodec α] [LawfulCodec β] : LawfulCodec (α × β) where
  enc := encProd (LawfulCodec.enc (α := α)) (LawfulCodec.enc (α := β))
  dec := decProd? (LawfulCodec.dec (α := α)) (LawfulCodec.dec (α := β))
  roundtrip := decProd_encProd_append (LawfulCodec.enc (α := α))
    (LawfulCodec.enc (α := β)) (LawfulCodec.dec (α := α))
    (LawfulCodec.dec (α := β)) (LawfulCodec.roundtrip (α := α))
    (LawfulCodec.roundtrip (α := β))

/-- List: `encList`/`decList?` — composes the element law
    (`decList_encList_append`). `List UInt8` resolves to the Bytes
    instance above (registered first). -/
instance lawfulCodecList [LawfulCodec α] : LawfulCodec (List α) where
  enc := encList (LawfulCodec.enc (α := α))
  dec := decList? (LawfulCodec.dec (α := α))
  roundtrip := decList_encList_append (LawfulCodec.enc (α := α))
    (LawfulCodec.dec (α := α)) (LawfulCodec.roundtrip (α := α))

/-! ## Membership-restricted element laws (W9.1)

`decManyBind_enc_append`/`decList_encList_append` demand the element
law for EVERY `a : α`. A recursive wire (a node whose children decode
under a depth cap) has the element law only for list MEMBERS (the
depth bound holds per element, not universally). These variants
restrict the hypothesis accordingly — same proofs, `mem`-guarded. -/

theorem decManyBind_enc_append_of_mem (dec : List UInt8 → Option (α × List UInt8))
    (enc : α → List UInt8) (as : List α)
    (h : ∀ a ∈ as, ∀ (rest : List UInt8), dec (enc a ++ rest) = some (a, rest))
    (rest : List UInt8) :
    decManyBind? dec as.length ((as.map enc).flatten ++ rest) = some (as, rest) := by
  induction as generalizing rest with
  | nil => simp [decManyBind?]
  | cons a as ih =>
      simp only [decManyBind?, List.length_cons, List.map_cons, List.flatten_cons,
        List.append_assoc]
      rw [h a List.mem_cons_self ((as.map enc).flatten ++ rest)]
      simp [ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem decList_encList_append_of_mem (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8)) (as : List α)
    (h : ∀ a ∈ as, ∀ (rest : List UInt8), dec (enc a ++ rest) = some (a, rest))
    (rest : List UInt8) :
    decList? dec (encList enc as ++ rest) = some (as, rest) := by
  show decManyBind? dec (decVarNat (encList enc as ++ rest)).1
      (decVarNat (encList enc as ++ rest)).2 = some (as, rest)
  rw [show encList enc as = encVarNat as.length ++ (as.map enc).flatten from rfl,
    List.append_assoc, decVarNat_append]
  exact decManyBind_enc_append_of_mem dec enc as h rest

/-! ## The versioned envelope (5.5.7)

The wire convention: `version` and `fingerprint` are the first two wire
fields (varints), then the length-prefixed payload. The decoder takes
the EXPECTED version and rejects a mismatch before touching the rest —
the failure the Rust-side runtime surfaces as a schema-version error. -/

/-- The decoded envelope: version + schema fingerprint + payload bytes. -/
structure Envelope where
  version : Nat
  fingerprint : Nat
  payload : List UInt8
deriving Repr, BEq, DecidableEq

def encEnvelope (version fingerprint : Nat) (payload : List UInt8) : List UInt8 :=
  encVarNat version ++ encVarNat fingerprint ++ encBytes payload

/-- Decode an envelope, rejecting a wrong version and any trailing
    garbage after the payload. -/
@[guest_std]
def decEnvelope? (expectedVersion : Nat) (bs : List UInt8) : Option Envelope :=
  let (version, r1) := decVarNat bs
  if _ : version = expectedVersion then
    let (fingerprint, r2) := decVarNat r1
    match decBytes? r2 with
    | some (payload, []) => some ⟨version, fingerprint, payload⟩
    | _ => none
  else none

/-- The envelope round trip. -/
theorem decEnvelope_encEnvelope (version fingerprint : Nat) (payload : List UInt8) :
    decEnvelope? version (encEnvelope version fingerprint payload)
      = some ⟨version, fingerprint, payload⟩ := by
  simp [encEnvelope, decEnvelope?, List.append_assoc, decVarNat_append,
    decBytes_encBytes]

/-- Wrong-version rejection: an envelope written at any other version
    decodes to `none`, proved — not just tested. -/
theorem decEnvelope_wrong_version (expected version fingerprint : Nat)
    (payload : List UInt8) (h : version ≠ expected) :
    decEnvelope? expected (encEnvelope version fingerprint payload) = none := by
  simp [encEnvelope, decEnvelope?, List.append_assoc, decVarNat_append, h]

end SchemaLang.Codec

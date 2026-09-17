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

Decode is PARTIAL at the combinator level (`Option`) — malformed bytes
decode to `none`. `decVarNat` itself is total (empty input decodes to
`(0, [])`); truncation REJECTION comes from the combinators layered on
top (tag mismatch, length-prefix overrun, trailing-garbage check).
-/

module

public import SchemaLang.Ty

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

/-- Decode one length-prefixed byte field: the next `n` bytes (n read
    from the varint) plus the trailing remainder. Truncation REJECTS:
    fewer than `n` bytes available is `none`. -/
def decBytes? (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let (n, rest) := decVarNat bs
  if _ : n ≤ rest.length then some (rest.take n, rest.drop n) else none

@[simp] theorem decBytes_encBytes_append (bs rest : List UInt8) :
    decBytes? (encBytes bs ++ rest) = some (bs, rest) := by
  unfold decBytes? encBytes
  rw [List.append_assoc, decVarNat_append bs.length (bs ++ rest)]
  simp +arith +decide

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
def decU64? (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  (decNat? bs).map fun (n, r) => (UInt64.ofNat n, r)

@[simp] theorem decU64_encU64_append (v : UInt64) (rest : List UInt8) :
    decU64? (encU64 v ++ rest) = some (v, rest) := by
  simp [encU64, decU64?, UInt64.ofNat_toNat]

/-- Char as its `toNat` varint. -/
def encChar (c : Char) : List UInt8 := encVarNat c.toNat

/-- Decode a char varint (`Char.ofNat` is total; the law needs only
    the encoder's range). -/
def decChar? (bs : List UInt8) : Option (Char × List UInt8) :=
  (decNat? bs).map fun (n, r) => (Char.ofNat n, r)

@[simp] theorem decChar_encChar_append (c : Char) (rest : List UInt8) :
    decChar? (encChar c ++ rest) = some (c, rest) := by
  simp [encChar, decChar?, Char.ofNat_toNat]

/-- String as a length-prefixed char list (see the section note). -/
def encString (s : String) : List UInt8 := encList encChar s.toList

/-- Decode a char-list string. -/
def decString? (bs : List UInt8) : Option (String × List UInt8) :=
  (decList? decChar? bs).map fun (cs, r) => (String.ofList cs, r)

@[simp] theorem decString_encString_append (s : String) (rest : List UInt8) :
    decString? (encString s ++ rest) = some (s, rest) := by
  simp [encString, decString?,
    decList_encList_append encChar decChar? (fun c r => decChar_encChar_append c r),
    String.ofList_toList]

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

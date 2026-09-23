/- # SchemaCore.Codec — the binary value codec over the closed `Ty` universe

Owner: the SchemaCore codec lane (the macht tree, `schemacore/`).
Driving decisions: notes/v3/15-patterns.md #2 (THE append-form codec law:
`dec (enc a ++ rest) = some (a, rest)` — codecs compose under bind BECAUSE
the law is append-form); notes/v3/13-interfaces.md (the atoms row: the
append-form law per codec); notes/v3/12-construction.md §4 (the codec
recipe); notes/v3/01-core.md §4 (the `Kit.Codec` grade — the
accepted-byte policy explicit, here as the EXACT IMAGE of the encoder).

THE WIRE (one line per shape, tags are data):

- `bool`     — one byte, `0` = false, `1` = true (any other byte refuses);
- `u64`      — the LEB128 varint of `v.toNat` (canonical: minimal);
- `i64`      — the varint of `zigzag v.toInt` (zigzag: 0→0, -1→1, 1→2, …);
- `string`   — varint length + one varint code point per `Char` (NOT
  UTF-8: core ships no `fromUTF8? ∘ toUTF8` round-trip lemma — the
  legacy-documented gap; the char-varint wire is the provable atom);
- `option`   — tag `0` = none, `1` = some + the element;
- `result`   — tag `0` = ok + payload, `1` = err + payload;
- `list`/`set` — varint count + the elements in payload order;
- `map`      — varint count + the key/value entries in payload order.

THE MAP-CANONICALITY NOTE (13-interfaces says "maps are canonical
key-sorted"): THIS lane is order-preserving, deliberately. The
append-form law `decVal t (encVal t v ++ rest) = some (v, rest)` is
NON-NEGOTIABLE (15-patterns #2), and a canonicalizing encoder breaks it:
an unsorted `Value.map` would decode to the sorted map, not to `v`. The
canonical key-sorted wire form is a `Kit.Normalization`-grade claim over
this lane's image, and lands with the first byte-tie consumer that needs
deterministic map bytes — not smuggled into an encoder whose law forbids
it. The slice's `Value.map` payload is insertion-ordered with order as
payload data (SchemaCore.Value's own discipline), and the wire agrees.

THE VARINT: `Kit.Varint` is the ONE LEB128 copy (the C0 shared home —
the twin that lived here, byte-for-byte with `WasmCore.Encode`'s, was
consolidated down into the kit when this lane became its second
consumer). This module consumes `encVarNat`/`decVarNat?` directly; its
own atom interface (bool/char/u64/i64/string) rides the shared varint.

The accepted-byte policy: EVERY decoder refuses out-of-policy bytes —
truncated varints, unknown tags, cap-violating bounded values,
out-of-range code points, oversized varints for `i64` — and the refusal
is THEOREM-backed (`encVal_decVal_eq`: a successful decode's input is
exactly an encoding plus a suffix), never a silent misparse.

The five questions (notes/v3/01-core.md): root = Crossing (the wire —
`Value t` into the byte grammar); carrier = `Kit.Codec` (the wire grade,
`valCodec`); spine reading = an interpretation of the closed universe
into bytes, consumed by the guest-relevant lanes later; ladder rung =
hand theorems of the small named kind (the append law + the inversion),
`rfl`-reducible on concrete values (all recursion structural); gate row =
SchemaTests' codec suite (the golden pins + the LCG round-trip sweep +
the refusal matrix) + the axiom report.

Core-only (imports SchemaCore.Value only — the cone rule).
-/

import SchemaCore.Value
import Kit.Varint

namespace SchemaCore

open Kit.Varint

/-! ## Zigzag — signed integers over the varint base (mined content) -/

/-- Map `ℤ` onto `ℕ`: nonnegative `i` to `2*i`, negative `i` to
    `2*(-i) - 1` (0 → 0, -1 → 1, 1 → 2, -2 → 3, …). -/
def zigzag (i : Int) : Nat :=
  if 0 ≤ i then (2 * i).toNat else (2 * (-i) - 1).toNat

/-- The inverse map: even `n` is a nonnegative value, odd a negative one. -/
def unzigzag (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else -(Int.ofNat (n / 2) + 1)

/-- `Int.ofNat` of a `toNat` in range is the value. -/
theorem ofNat_toNat_pos (i : Int) (h : 0 ≤ i) : Int.ofNat i.toNat = i := by
  rw [show Int.ofNat i.toNat = max i 0 from Int.ofNat_toNat i]
  omega

/-- Zigzag round trip: decode (encode i) = i. -/
theorem unzigzag_zigzag (i : Int) : unzigzag (zigzag i) = i := by
  by_cases h : 0 ≤ i
  · have h1 : ((2 * i).toNat : Int) = 2 * i := Int.toNat_of_nonneg (by omega)
    have e1 : (2 * i).toNat = 2 * i.toNat := by
      refine Int.ofNat_inj.mp ?_
      push_cast
      omega
    have p1 : 2 * i.toNat % 2 = 0 := by omega
    have p2 : 2 * i.toNat / 2 = i.toNat := by omega
    simp only [zigzag, if_pos h, unzigzag, e1, if_pos p1, p2, ofNat_toNat_pos i h]
  · have h1 : ((2 * (-i) - 1).toNat : Int) = 2 * (-i) - 1 :=
      Int.toNat_of_nonneg (by omega)
    have e1 : (2 * (-i) - 1).toNat = 2 * (-i).toNat - 1 := by
      refine Int.ofNat_inj.mp ?_
      push_cast
      omega
    have p1 : (2 * (-i) - 1).toNat % 2 = 1 := by omega
    have p2 : (2 * (-i) - 1).toNat / 2 = (-i).toNat - 1 := by omega
    have h4 : Int.ofNat ((-i).toNat - 1) = Int.ofNat (-i).toNat - 1 :=
      Int.ofNat_sub (show (1 : Nat) ≤ (-i).toNat by omega)
    rw [ofNat_toNat_pos (-i) (by omega)] at h4
    simp only [zigzag, if_neg h, unzigzag,
      if_neg (show ¬ ((2 * (-i) - 1).toNat % 2 = 0) by omega), p2, h4]
    omega

/-- The `Int64` reassembly is faithful on the type's own range: the
    `Int64` re-read of its `Int` image does not wrap. -/
theorem int64_ofInt_toInt (v : Int64) : (Int64.ofInt v.toInt).toInt = v.toInt := by
  simp

/-! ## The byte reader + the scalar atoms (bool, char) -/

/-- Read one byte off the front (the tag/atom reader every if-style
    decoder dispatches through — its inversion is trivial, which is the
    point: no matcher opacity in the refusals' proofs). -/
def decByte? : List UInt8 → Option (UInt8 × List UInt8)
  | b :: rest => some (b, rest)
  | [] => none

theorem decByte?_cons (b : UInt8) (rest : List UInt8) :
    decByte? (b :: rest) = some (b, rest) := rfl

/-- The byte reader's inversion: a successful read consumed exactly
    one byte. -/
theorem decByte?_eq : ∀ (bs : List UInt8) (b : UInt8) (rest : List UInt8),
    decByte? bs = some (b, rest) → bs = b :: rest := by
  intro bs
  cases bs with
  | nil => intro b rest h; simp [decByte?] at h
  | cons b0 bs' =>
      intro b rest h
      simp only [decByte?, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- Bool: one byte, `0` = false, `1` = true. -/
def encBool : Bool → List UInt8
  | .false => [0]
  | .true => [1]

/-- Bool, append-form: read the tag byte, pass the rest through.
    Any other head byte refuses (never a silent misparse). -/
def decBool? (bs : List UInt8) : Option (Bool × List UInt8) :=
  match decByte? bs with
  | some (b0, r) =>
      if b0 = 0 then some (false, r)
      else if b0 = 1 then some (true, r)
      else none
  | none => none

/-- PATTERN #2 — the bool atom's append-form law. -/
theorem decBool?_encBool_append (b : Bool) (rest : List UInt8) :
    decBool? (encBool b ++ rest) = some (b, rest) := by
  cases b <;> simp [encBool, decBool?, decByte?_cons]

/-- The bool atom's exact-image inversion. -/
theorem encBool_decBool?_eq : ∀ (bs : List UInt8) (b : Bool) (rest : List UInt8),
    decBool? bs = some (b, rest) → bs = encBool b ++ rest := by
  intro bs b rest h
  simp only [decBool?] at h
  split at h
  · next b0 hb0 hdisc =>
      split at h
      · next hb =>
          obtain ⟨rfl, rfl⟩ := Option.some.inj h
          rw [decByte?_eq bs b0 rest hdisc]
          simp [encBool, hb]
      · next _ =>
          split at h
          · next hb =>
              obtain ⟨rfl, rfl⟩ := Option.some.inj h
              rw [decByte?_eq bs b0 rest hdisc]
              simp [encBool, hb]
          · simp at h
  · simp at h

/-- Char as its code point's varint. The decoder VALIDATES: a code
    point whose `Char.ofNat` does not re-read to itself (the wrapping
    regime) refuses — the accepted bytes are exactly the encoder's
    image, never a silently wrapped char. -/
def encChar (c : Char) : List UInt8 := encVarNat c.toNat

/-- Char, append-form decode (with the validity gate above). -/
def decChar? (bs : List UInt8) : Option (Char × List UInt8) :=
  match decVarNat? bs with
  | some (n, r) => if (Char.ofNat n).toNat = n then some (Char.ofNat n, r) else none
  | none => none

/-- PATTERN #2 — the char atom's append-form law. -/
theorem decChar?_encChar_append (c : Char) (rest : List UInt8) :
    decChar? (encChar c ++ rest) = some (c, rest) := by
  simp [encChar, decChar?, decVarNat?_encVarNat_append]

/-- The char atom's exact-image inversion. -/
theorem encChar_decChar?_eq : ∀ (bs : List UInt8) (c : Char) (rest : List UInt8),
    decChar? bs = some (c, rest) → bs = encChar c ++ rest := by
  intro bs c rest h
  simp only [decChar?] at h
  split at h
  · next n r hdisc =>
      split at h
      · next hv =>
          obtain ⟨rfl, rfl⟩ := Option.some.inj h
          rw [decVarNat?_encVarNat_eq bs n rest hdisc]
          simp [encChar, hv]
      · simp at h
  · simp at h

/-! ## The generic list/pair combinators (the containers' shared shape) -/

/-- Length-prefixed list: `varint len ++ each element's bytes` — the
    elements are SELF-DELIMITING (every atom/codec here is append-form),
    so the count is the only framing needed. -/
def encList (enc : α → List UInt8) (as : List α) : List UInt8 :=
  encVarNat as.length ++ (as.map enc).flatten

/-- Decode `m` self-delimiting elements. Truncation refuses (the
    element decoder's `none` propagates) — never a silent short list. -/
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

/-- PATTERN #2 — the many-elements combinator's append-form law: it
    composes the ELEMENT law (the hypothesis) over the list. -/
theorem decManyBind?_enc_append (dec : List UInt8 → Option (α × List UInt8))
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

/-- The many-elements combinator's exact-image inversion: what it
    accepts is exactly `as.length` elements in encoder form — composes
    the element inversion (the hypothesis). NOTE: no encoder
    injectivity is needed anywhere — the decoded list IS the witness. -/
theorem decManyBind?_eq (enc : α → List UInt8)
    (hInv : ∀ (bs : List UInt8) (a : α) (rest : List UInt8),
      dec bs = some (a, rest) → bs = enc a ++ rest) :
    ∀ (m : Nat) (bs : List UInt8) (as : List α) (rest : List UInt8),
      decManyBind? dec m bs = some (as, rest) →
        as.length = m ∧ bs = (as.map enc).flatten ++ rest := by
  intro m
  induction m with
  | zero =>
      intro bs as rest h
      simp only [decManyBind?] at h
      cases as with
      | nil =>
          obtain ⟨rfl⟩ := Option.some.inj h
          exact ⟨rfl, rfl⟩
      | cons a as' => exact absurd h (by simp)
  | succ m ih =>
      intro bs as rest h
      unfold decManyBind? at h
      cases as with
      | nil =>
          split at h
          · next hdisc => simp at h
          · next a' r1 hdisc =>
              split at h
              · next _ _ _ => simp at h
              · simp at h
      | cons a as' =>
          split at h
          · next hdisc => simp at h
          · next a'' r1 hdisc =>
              split at h
              · next _ _ => simp at h
              · next as'' rest' hdisc2 =>
                  simp only [Option.some.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨hlen, hbs⟩ := ih r1 as' rest hdisc2
                  refine ⟨by simp [hlen], ?_⟩
                  rw [hInv bs a r1 hdisc, hbs]
                  simp

/-- The pair entry: `encA p.1 ++ encB p.2` (the map entries' shape). -/
def encPair (encA : α → List UInt8) (encB : β → List UInt8) (p : α × β) :
    List UInt8 := encA p.1 ++ encB p.2

/-- The pair decoder: element A, then element B off its remainder. -/
def decPair? (decA : List UInt8 → Option (α × List UInt8))
    (decB : List UInt8 → Option (β × List UInt8)) (bs : List UInt8) :
    Option ((α × β) × List UInt8) :=
  match decA bs with
  | some (a, r1) =>
      match decB r1 with
      | some (b, r2) => some ((a, b), r2)
      | none => none
  | none => none

/-- PATTERN #2 — the pair combinator's append-form law: composes the
    two halves' laws (the hypotheses). -/
theorem decPair?_encPair_append (encA : α → List UInt8) (encB : β → List UInt8)
    (decA : List UInt8 → Option (α × List UInt8))
    (decB : List UInt8 → Option (β × List UInt8))
    (hA : ∀ (a : α) (rest : List UInt8), decA (encA a ++ rest) = some (a, rest))
    (hB : ∀ (b : β) (rest : List UInt8), decB (encB b ++ rest) = some (b, rest))
    (p : α × β) (rest : List UInt8) :
    decPair? decA decB (encPair encA encB p ++ rest) = some (p, rest) := by
  obtain ⟨a, b⟩ := p
  simp [encPair, decPair?, hA a (encB b ++ rest), hB b rest]

/-- The pair combinator's exact-image inversion: composes the two
    halves' inversions (the hypotheses). -/
theorem decPair?_eq (encA : α → List UInt8) (encB : β → List UInt8)
    (decA : List UInt8 → Option (α × List UInt8))
    (decB : List UInt8 → Option (β × List UInt8))
    (hA : ∀ (bs : List UInt8) (a : α) (rest : List UInt8),
      decA bs = some (a, rest) → bs = encA a ++ rest)
    (hB : ∀ (bs : List UInt8) (b : β) (rest : List UInt8),
      decB bs = some (b, rest) → bs = encB b ++ rest)
    (bs : List UInt8) (p : α × β) (rest : List UInt8) :
    decPair? decA decB bs = some (p, rest) →
      bs = encPair encA encB p ++ rest := by
  obtain ⟨a, b⟩ := p
  intro h
  simp only [decPair?] at h
  split at h
  · next a' r1 hdisc =>
      split at h
      · next b' r2 hdisc2 =>
          simp only [Option.some.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [hA bs a r1 hdisc, hB r1 b rest hdisc2]
          simp [encPair]
      · simp at h
  · simp at h

/-! ## The VList/VMap erase + rebuild adapters (plain functions — the
     GADT sibling rule bans nested `List (Value t)` DATA, not this pair) -/

/-- Erase a `VList` to a plain list of values. -/
def vListToList : {t : Ty} → VList t → List (Value t)
  | _, .nil => []
  | _, .cons v vl => v :: vListToList vl

/-- Rebuild a `VList` from a plain list. -/
def listToVList : {t : Ty} → List (Value t) → VList t
  | _, [] => .nil
  | _, v :: vs => .cons v (listToVList vs)

/-- The erase/rebuild round trip (rebuild side). -/
theorem listToVList_vListToList :
    ∀ {t : Ty} (vl : VList t), listToVList (vListToList vl) = vl
  | _, .nil => by simp [vListToList, listToVList]
  | _, .cons v vl => by
      simp only [vListToList, listToVList]
      rw [listToVList_vListToList vl]

/-- The erase/rebuild round trip (erase side). -/
theorem vListToList_listToVList :
    ∀ {t : Ty} (xs : List (Value t)), vListToList (listToVList xs) = xs := by
  intro t xs
  induction xs with
  | nil => simp [vListToList, listToVList]
  | cons v vs ih => simp only [listToVList, vListToList, ih]

/-- Erase a `VMap` to a plain association list. -/
def vMapToList : {k : KeyTy} → {v : Ty} → VMap k v → List (Value k.toTy × Value v)
  | _, _, .nil => []
  | _, _, .cons kv vv m => (kv, vv) :: vMapToList m

/-- Rebuild a `VMap` from a plain association list (no nested pair
    pattern — the equation lemma must fire under simp). -/
def listToVMap : {k : KeyTy} → {v : Ty} →
    List (Value k.toTy × Value v) → VMap k v
  | _, _, [] => .nil
  | _, _, p :: kvs => .cons p.1 p.2 (listToVMap kvs)

/-- The erase/rebuild round trip (rebuild side). -/
theorem listToVMap_vMapToList :
    ∀ {k : KeyTy} {v : Ty} (m : VMap k v), listToVMap (vMapToList m) = m
  | _, _, .nil => by simp [vMapToList, listToVMap]
  | _, _, .cons kv vv m => by
      simp only [vMapToList, listToVMap]
      rw [listToVMap_vMapToList m]

/-- The erase/rebuild round trip (erase side). -/
theorem vMapToList_listToVMap :
    ∀ {k : KeyTy} {v : Ty} (kvs : List (Value k.toTy × Value v)),
      vMapToList (listToVMap kvs) = kvs := by
  intro k v kvs
  induction kvs with
  | nil => simp [vMapToList, listToVMap]
  | cons e rest ih => simp [listToVMap, vMapToList, ih]

/-! ## The scalar decode halves (shared by the key and value codecs) -/

/-- UInt64 as its `toNat` varint; decode RANGE-CHECKS (a varint at or
    over `2^64` refuses — never a silent wrap). -/
def decU64raw? (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  match decVarNat? bs with
  | some (n, r) => if n < 2 ^ 64 then some (UInt64.ofNat n, r) else none
  | none => none

/-- Int64 as the zigzag varint; decode re-checks the zigzag round trip
    (a varint outside the `Int64` range refuses — never a silent wrap). -/
def decI64raw? (bs : List UInt8) : Option (Int64 × List UInt8) :=
  match decVarNat? bs with
  | some (n, r) =>
      if zigzag (Int64.ofInt (unzigzag n)).toInt = n
      then some (Int64.ofInt (unzigzag n), r) else none
  | none => none

/-- String as a varint length + one varint code point per `Char`
    (see the header's UTF-8 note); the char decoder's validity gate
    applies per code point. -/
def decStringraw? (bs : List UInt8) : Option (String × List UInt8) :=
  match decVarNat? bs with
  | some (n, r) =>
      (decManyBind? decChar? n r).map fun (cs, r') => (String.ofList cs, r')
  | none => none

/-- PATTERN #2 — the u64 atom's append-form law. -/
theorem decU64raw?_append (v : UInt64) (rest : List UInt8) :
    decU64raw? (encVarNat v.toNat ++ rest) = some (v, rest) := by
  have hlt : v.toNat < 2 ^ 64 := v.toNat_lt
  simp [decU64raw?, decVarNat?_encVarNat_append, hlt]

/-- The u64 atom's exact-image inversion. -/
theorem decU64raw?_eq : ∀ (bs : List UInt8) (v : UInt64) (rest : List UInt8),
    decU64raw? bs = some (v, rest) → bs = encVarNat v.toNat ++ rest := by
  intro bs v rest h
  simp only [decU64raw?] at h
  split at h
  · next n r hdisc =>
      split at h
      · next hn =>
          obtain ⟨rfl, rfl⟩ := Option.some.inj h
          rw [decVarNat?_encVarNat_eq bs n rest hdisc]
          simp [Nat.mod_eq_of_lt hn]
      · simp at h
  · simp at h

/-- PATTERN #2 — the i64 atom's append-form law. -/
theorem decI64raw?_append (v : Int64) (rest : List UInt8) :
    decI64raw? (encVarNat (zigzag v.toInt) ++ rest) = some (v, rest) := by
  simp [decI64raw?, decVarNat?_encVarNat_append, unzigzag_zigzag]

/-- The i64 atom's exact-image inversion. -/
theorem decI64raw?_eq : ∀ (bs : List UInt8) (v : Int64) (rest : List UInt8),
    decI64raw? bs = some (v, rest) → bs = encVarNat (zigzag v.toInt) ++ rest := by
  intro bs v rest h
  simp only [decI64raw?] at h
  split at h
  · next n r hdisc =>
      split at h
      · next hchk =>
          obtain ⟨rfl, rfl⟩ := Option.some.inj h
          rw [decVarNat?_encVarNat_eq bs n rest hdisc, hchk]
      · simp at h
  · simp at h

/-- PATTERN #2 — the string atom's append-form law (composes the char
    law over the length-prefixed list). -/
theorem decStringraw?_append (s : String) (rest : List UInt8) :
    decStringraw? (encList encChar s.toList ++ rest) = some (s, rest) := by
  simp [decStringraw?, encList, List.append_assoc, decVarNat?_encVarNat_append,
    decManyBind?_enc_append decChar? encChar decChar?_encChar_append,
    String.ofList_toList]

/-- The string atom's exact-image inversion (composes the varint and
    char inversions over the list). -/
theorem decStringraw?_eq : ∀ (bs : List UInt8) (s : String) (rest : List UInt8),
    decStringraw? bs = some (s, rest) → bs = encList encChar s.toList ++ rest := by
  intro bs s rest h
  simp only [decStringraw?] at h
  split at h
  · next n r hdisc =>
      cases hd2 : decManyBind? decChar? n r with
      | none => rw [hd2] at h; simp at h
      | some q =>
          obtain ⟨cs, r'⟩ := q
          rw [hd2] at h
          simp only [Option.map_some, Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hlen, hbs⟩ :=
            decManyBind?_eq encChar encChar_decChar?_eq n r cs rest hd2
          rw [decVarNat?_encVarNat_eq bs n r hdisc, hbs]
          simp [encList, ← hlen]
  · simp at h

/-! ## The wrapped-decode inversion (the shared helper)

Every decode arm of the form `(atom bs).map wrap` inverts through ONE
lemma: a successful wrapped decode hands back the atom's own witness
pair (the `d bs = some (x, r)` discharge), plus the two equalities the
wrapper forces. Written once at the structure (15-patterns), cited by
every wrapped arm of the key and value codecs' inversions below. -/

/-- The wrapped-decode inversion: if `(d bs).map (fun p => (wrap p.1,
    p.2))` succeeds, the underlying decode succeeded on some `(x, r)`,
    the result is `wrap x`, and the remainder is `r`. -/
theorem mapWrap_some_inv {α β : Type}
    {d : List UInt8 → Option (α × List UInt8)} {bs : List UInt8}
    {wrap : α → β} {v : β} {rest : List UInt8}
    (h : (d bs).map (fun p => (wrap p.1, p.2)) = some (v, rest)) :
    ∃ x r, d bs = some (x, r) ∧ v = wrap x ∧ rest = r := by
  cases hd : d bs with
  | none => rw [hd] at h; simp at h
  | some p =>
      obtain ⟨x, r⟩ := p
      rw [hd] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact ⟨x, r, rfl, h1.symm, h2.symm⟩

/-! ## The key codec (the map/set key positions ride the scalar
     sub-universe DIRECTLY — the `toTy` indirection would break the
     value codec's structural recursion, the legacy lesson) -/

/-- Encode a key payload (the scalar encode arms, direct). -/
def encKey : (k : KeyTy) → Value k.toTy → List UInt8
  | .bool, .bool b => encBool b
  | .u64, .u64 n => encVarNat n.toNat
  | .i64, .i64 n => encVarNat (zigzag n.toInt)
  | .string, .string s => encList encChar s.toList

/-- Decode a key payload (the scalar decode arms, direct). -/
def decKey? : (k : KeyTy) → List UInt8 → Option (Value k.toTy × List UInt8)
  | .bool, bs => (decBool? bs).map fun (b, r) => (.bool b, r)
  | .u64, bs => (decU64raw? bs).map fun (n, r) => (.u64 n, r)
  | .i64, bs => (decI64raw? bs).map fun (n, r) => (.i64 n, r)
  | .string, bs => (decStringraw? bs).map fun (s, r) => (.string s, r)

/-- PATTERN #2 — the key codec's append-form law (per-key case split,
    each arm citing its scalar atom's law). -/
theorem decKey?_encKey_append : ∀ (k : KeyTy) (v : Value k.toTy) (rest : List UInt8),
    decKey? k (encKey k v ++ rest) = some (v, rest)
  | .bool, .bool b, rest => by
      simp only [decKey?, encKey, decBool?_encBool_append, Option.map_some]
  | .u64, .u64 n, rest => by
      simp only [decKey?, encKey, decU64raw?_append, Option.map_some]
  | .i64, .i64 n, rest => by
      simp only [decKey?, encKey, decI64raw?_append, Option.map_some]
  | .string, .string s, rest => by
      simp only [decKey?, encKey, decStringraw?_append, Option.map_some]

/-- The key codec's exact-image inversion (per-key case split, each arm
    citing its scalar atom's inversion). -/
theorem encKey_decKey?_eq : ∀ (k : KeyTy) (bs : List UInt8) (v : Value k.toTy)
    (rest : List UInt8), decKey? k bs = some (v, rest) → bs = encKey k v ++ rest
  | .bool, bs, v, rest, h => by
      simp only [decKey?] at h
      obtain ⟨b, r, hd, hv, hr⟩ :=
        mapWrap_some_inv (d := decBool?) (wrap := Value.bool) h
      subst hv
      subst hr
      simp only [encKey]
      exact encBool_decBool?_eq bs b _ hd
  | .u64, bs, v, rest, h => by
      simp only [decKey?] at h
      obtain ⟨n, r, hd, hv, hr⟩ :=
        mapWrap_some_inv (d := decU64raw?) (wrap := Value.u64) h
      subst hv
      subst hr
      simp only [encKey]
      exact decU64raw?_eq bs n _ hd
  | .i64, bs, v, rest, h => by
      simp only [decKey?] at h
      obtain ⟨n, r, hd, hv, hr⟩ :=
        mapWrap_some_inv (d := decI64raw?) (wrap := Value.i64) h
      subst hv
      subst hr
      simp only [encKey]
      exact decI64raw?_eq bs n _ hd
  | .string, bs, v, rest, h => by
      simp only [decKey?] at h
      obtain ⟨s, r, hd, hv, hr⟩ :=
        mapWrap_some_inv (d := decStringraw?) (wrap := Value.string) h
      subst hv
      subst hr
      simp only [encKey]
      exact decStringraw?_eq bs s _ hd

/-! ## The value codec over the CLOSED universe -/

/-- Encode a schema-typed value. Composite arms reuse the combinators;
    the key positions ride `encKey` directly (the `toTy` indirection
    would break the structural recursion — the legacy lesson). -/
def encVal : (t : Ty) → Value t → List UInt8
  | .bool, .bool b => encBool b
  | .u64, .u64 n => encVarNat n.toNat
  | .i64, .i64 n => encVarNat (zigzag n.toInt)
  | .string, .string s => encList encChar s.toList
  | .option _, .none => [0]
  | .option t, .some v => 1 :: encVal t v
  | .result ok _, .ok v => 0 :: encVal ok v
  | .result _ err, .err v => 1 :: encVal err v
  | .list t, .list vl => encList (encVal t) (vListToList vl)
  | .map k v, .map m => encList (encPair (encKey k) (encVal v)) (vMapToList m)
  | .set k, .set vl => encList (encKey k) (vListToList vl)
  | .bounded _, .bounded f => encVarNat f.val

/-- The append-form decoder: returns the value AND the remaining bytes.
    Every out-of-policy shape refuses (`none`), never a silent misparse:
    truncated varints, unknown tags, out-of-range code points, varints
    at/over `2^64` for u64, out-of-range zigzags for i64, cap-violating
    bounded values. -/
def decVal : (t : Ty) → List UInt8 → Option (Value t × List UInt8)
  | .bool, bs => (decBool? bs).map fun (b, r) => (.bool b, r)
  | .u64, bs => (decU64raw? bs).map fun (n, r) => (.u64 n, r)
  | .i64, bs => (decI64raw? bs).map fun (n, r) => (.i64 n, r)
  | .string, bs => (decStringraw? bs).map fun (s, r) => (.string s, r)
  | .option t, bs =>
      match decByte? bs with
      | some (b0, r) =>
          if b0 = 0 then some (.none, r)
          else if b0 = 1 then (decVal t r).map fun (v, r') => (.some v, r')
          else none
      | none => none
  | .result ok err, bs =>
      match decByte? bs with
      | some (b0, r) =>
          if b0 = 0 then (decVal ok r).map fun (v, r') => (.ok v, r')
          else if b0 = 1 then (decVal err r).map fun (v, r') => (.err v, r')
          else none
      | none => none
  | .list t, bs =>
      match decVarNat? bs with
      | some (n, r) =>
          match decManyBind? (decVal t) n r with
          | some (xs, r') => some (.list (listToVList xs), r')
          | none => none
      | none => none
  | .map k v, bs =>
      match decVarNat? bs with
      | some (n, r) =>
          match decManyBind? (decPair? (decKey? k) (decVal v)) n r with
          | some (kvs, r') => some (.map (listToVMap kvs), r')
          | none => none
      | none => none
  | .set k, bs =>
      match decVarNat? bs with
      | some (n, r) =>
          match decManyBind? (decKey? k) n r with
          | some (xs, r') => some (.set (listToVList xs), r')
          | none => none
      | none => none
  | .bounded cap, bs =>
      match decVarNat? bs with
      | some (n, r) =>
          if h : n < cap then some (.bounded ⟨n, h⟩, r) else none
      | none => none

/-! ## The known-answer coverage pins (the tags are data) -/

example : encVal .bool (.bool false) = [0] := rfl
example : encVal .bool (.bool true) = [1] := rfl
example : encVal .u64 (.u64 300) = [0xAC, 0x02] := rfl
example : encVal .i64 (.i64 (-1)) = [1] := rfl
example : encVal .i64 (.i64 1) = [2] := rfl
example : encVal .string (.string "hi") = [2, 104, 105] := rfl
example : encVal (.option .u64) .none = [0] := rfl
example : encVal (.option .u64) (.some (.u64 5)) = [1, 5] := rfl
example : encVal (.result .u64 .string) (.ok (.u64 1)) = [0, 1] := rfl
example : encVal (.result .u64 .string) (.err (.string "x")) = [1, 1, 120] := rfl
example : encVal (.list .u64)
    (.list (.cons (.u64 1) (.cons (.u64 2) .nil))) = [2, 1, 2] := rfl
example : encVal (.bounded 5) (.bounded ⟨2, by decide⟩) = [2] := rfl
example : decVal .u64 [0xAC, 0x02] = some (.u64 300, []) := rfl
example : decVal (.option .u64) [1, 5] = some (.some (.u64 5), []) := rfl
/-- The truncation control, at the kernel: a dangling continuation bit
    refuses. -/
example : decVal .u64 [0x80] = none := rfl
/-- The cap control, at the kernel: a value over the cap refuses. -/
example : decVal (.bounded 5) [9] = none := rfl

/-! ## The per-ctor append-form theorems + the composed whole

The leaf laws cite their scalar atoms; the container laws compose the
element laws (the induction hypotheses); the MASTER theorem is ONE
structural induction over the closed `Ty` — the composition discipline
of pattern #2. -/

/-- PATTERN #2 — the value codec's append-form law, over the CLOSED
    universe: every value of every `Ty` decodes from its encoding plus
    any suffix, exactly. -/
theorem decVal_encVal_append : ∀ (t : Ty) (v : Value t) (rest : List UInt8),
    decVal t (encVal t v ++ rest) = some (v, rest) := by
  intro t
  induction t with
  | bool =>
      intro v rest
      cases v
      simp [encVal, decVal, decBool?_encBool_append]
  | u64 =>
      intro v rest
      cases v
      simp [encVal, decVal, decU64raw?_append]
  | i64 =>
      intro v rest
      cases v
      simp [encVal, decVal, decI64raw?_append]
  | string =>
      intro v rest
      cases v
      simp [encVal, decVal, decStringraw?_append]
  | option t ih =>
      intro v rest
      cases v with
      | none => simp [encVal, decVal, decByte?_cons]
      | some x =>
          simp only [encVal, decVal, decByte?_cons, List.cons_append,
            if_neg (by decide : ¬((1 : UInt8) = 0))]
          rw [ih x rest]
          simp
  | result ok err ihok iherr =>
      intro v rest
      cases v with
      | ok x =>
          simp only [encVal, decVal, decByte?_cons, List.cons_append]
          rw [ihok x rest]
          simp
      | err x =>
          simp only [encVal, decVal, decByte?_cons, List.cons_append,
            if_neg (by decide : ¬((1 : UInt8) = 0))]
          rw [iherr x rest]
          simp
  | list t ih =>
      intro v rest
      cases v with
      | list vl =>
          simp only [encVal, decVal, encList, List.append_assoc,
            decVarNat?_encVarNat_append]
          rw [decManyBind?_enc_append (decVal t) (encVal t) ih (vListToList vl) rest]
          simp [listToVList_vListToList]
  | map k v ih =>
      intro v rest
      cases v with
      | map m =>
          simp only [encVal, decVal, encList, List.append_assoc,
            decVarNat?_encVarNat_append]
          rw [decManyBind?_enc_append _ _
            (decPair?_encPair_append (encKey k) (encVal v) (decKey? k) (decVal v)
              (decKey?_encKey_append k) ih) (vMapToList m) rest]
          simp [listToVMap_vMapToList]
  | set k =>
      intro v rest
      cases v with
      | set vl =>
          simp only [encVal, decVal, encList, List.append_assoc,
            decVarNat?_encVarNat_append]
          rw [decManyBind?_enc_append (decKey? k) (encKey k) (decKey?_encKey_append k)
            (vListToList vl) rest]
          simp [listToVList_vListToList]
  | bounded cap =>
      intro v rest
      cases v with
      | bounded f =>
          simp only [encVal, decVal, decVarNat?_encVarNat_append, dif_pos f.isLt]

/-- The value decoder's exact-image inversion: a successful decode's
    input is exactly an encoding plus a suffix — the accepted-byte
    policy's content, theorem-backed per ctor and composed once. -/
theorem encVal_decVal_eq : ∀ (t : Ty) (bs : List UInt8) (v : Value t) (rest : List UInt8),
    decVal t bs = some (v, rest) → bs = encVal t v ++ rest := by
  intro t
  induction t with
  | bool =>
      intro bs v rest h
      simp only [decVal] at h
      obtain ⟨b, r, hd, hv, hr⟩ :=
        mapWrap_some_inv (d := decBool?) (wrap := Value.bool) h
      subst hv
      subst hr
      exact encBool_decBool?_eq bs b _ hd
  | u64 =>
      intro bs v rest h
      simp only [decVal] at h
      obtain ⟨n, r, hd, hv, hr⟩ :=
        mapWrap_some_inv (d := decU64raw?) (wrap := Value.u64) h
      subst hv
      subst hr
      exact decU64raw?_eq bs n _ hd
  | i64 =>
      intro bs v rest h
      simp only [decVal] at h
      obtain ⟨n, r, hd, hv, hr⟩ :=
        mapWrap_some_inv (d := decI64raw?) (wrap := Value.i64) h
      subst hv
      subst hr
      exact decI64raw?_eq bs n _ hd
  | string =>
      intro bs v rest h
      simp only [decVal] at h
      obtain ⟨s, r, hd, hv, hr⟩ :=
        mapWrap_some_inv (d := decStringraw?) (wrap := Value.string) h
      subst hv
      subst hr
      exact decStringraw?_eq bs s _ hd
  | option t ih =>
      intro bs v rest h
      simp only [decVal] at h
      cases hd : decByte? bs with
      | none => rw [hd] at h; simp at h
      | some p =>
          obtain ⟨b0, r⟩ := p
          rw [hd] at h
          simp only at h
          by_cases hb0 : b0 = 0
          · rw [if_pos hb0] at h
            obtain ⟨hvf, hvr⟩ := Prod.mk.inj (Option.some.inj h)
            subst hvf
            subst hvr
            rw [decByte?_eq bs b0 _ hd]
            simp [encVal, hb0]
          · by_cases hb1 : b0 = 1
            · rw [if_neg hb0, if_pos hb1] at h
              obtain ⟨x, r', hd2, hv, hr⟩ :=
                mapWrap_some_inv (d := decVal t) (wrap := Value.some) h
              subst hv
              subst hr
              rw [decByte?_eq bs b0 _ hd, ih r x _ hd2]
              simp [encVal, hb1]
            · rw [if_neg hb0, if_neg hb1] at h
              simp at h
  | result ok err ihok iherr =>
      intro bs v rest h
      simp only [decVal] at h
      cases hd : decByte? bs with
      | none => rw [hd] at h; simp at h
      | some p =>
          obtain ⟨b0, r⟩ := p
          rw [hd] at h
          simp only at h
          by_cases hb0 : b0 = 0
          · rw [if_pos hb0] at h
            obtain ⟨x, r', hd2, hv, hr⟩ :=
              mapWrap_some_inv (d := decVal ok) (wrap := Value.ok) h
            subst hv
            subst hr
            rw [decByte?_eq bs b0 _ hd, ihok r x _ hd2]
            simp [encVal, hb0]
          · by_cases hb1 : b0 = 1
            · rw [if_neg hb0, if_pos hb1] at h
              obtain ⟨x, r', hd2, hv, hr⟩ :=
                mapWrap_some_inv (d := decVal err) (wrap := Value.err) h
              subst hv
              subst hr
              rw [decByte?_eq bs b0 _ hd, iherr r x _ hd2]
              simp [encVal, hb1]
            · rw [if_neg hb0, if_neg hb1] at h
              simp at h
  | list t ih =>
      intro bs v rest h
      simp only [decVal] at h
      cases hd : decVarNat? bs with
      | none => rw [hd] at h; simp at h
      | some q =>
          obtain ⟨n, r⟩ := q
          rw [hd] at h
          simp only at h
          cases hd2 : decManyBind? (decVal t) n r with
          | none => rw [hd2] at h; simp at h
          | some q2 =>
              obtain ⟨xs, r'⟩ := q2
              rw [hd2] at h
              simp only at h
              obtain ⟨hvf, hvr⟩ := Prod.mk.inj (Option.some.inj h)
              subst hvf
              subst hvr
              obtain ⟨hlen, hbs⟩ := decManyBind?_eq (encVal t) ih n r xs _ hd2
              rw [decVarNat?_encVarNat_eq bs n r hd, hbs]
              simp [encVal, encList, vListToList_listToVList, ← hlen]
  | map kt vt ih =>
      intro bs v rest h
      simp only [decVal] at h
      cases hd : decVarNat? bs with
      | none => rw [hd] at h; simp at h
      | some q =>
          obtain ⟨n, r⟩ := q
          rw [hd] at h
          simp only at h
          cases hd2 : decManyBind? (decPair? (decKey? kt) (decVal vt)) n r with
          | none => rw [hd2] at h; simp at h
          | some q2 =>
              obtain ⟨kvs, r'⟩ := q2
              rw [hd2] at h
              simp only at h
              obtain ⟨hvf, hvr⟩ := Prod.mk.inj (Option.some.inj h)
              subst hvf
              subst hvr
              have hPair : ∀ (q3 : List UInt8) (p : Value kt.toTy × Value vt)
                  (r2 : List UInt8),
                  decPair? (decKey? kt) (decVal vt) q3 = some (p, r2) →
                    q3 = encPair (encKey kt) (encVal vt) p ++ r2 :=
                decPair?_eq (encKey kt) (encVal vt) (decKey? kt) (decVal vt)
                  (encKey_decKey?_eq kt) ih
              obtain ⟨hlen, hbs⟩ := decManyBind?_eq _ hPair n r kvs _ hd2
              rw [decVarNat?_encVarNat_eq bs n r hd, hbs]
              simp [encVal, encList, vMapToList_listToVMap, ← hlen]
  | set k =>
      intro bs v rest h
      simp only [decVal] at h
      cases hd : decVarNat? bs with
      | none => rw [hd] at h; simp at h
      | some q =>
          obtain ⟨n, r⟩ := q
          rw [hd] at h
          simp only at h
          cases hd2 : decManyBind? (decKey? k) n r with
          | none => rw [hd2] at h; simp at h
          | some q2 =>
              obtain ⟨xs, r'⟩ := q2
              rw [hd2] at h
              simp only at h
              obtain ⟨hvf, hvr⟩ := Prod.mk.inj (Option.some.inj h)
              subst hvf
              subst hvr
              obtain ⟨hlen, hbs⟩ :=
                decManyBind?_eq (encKey k) (encKey_decKey?_eq k) n r xs _ hd2
              rw [decVarNat?_encVarNat_eq bs n r hd, hbs]
              simp [encVal, encList, vListToList_listToVList, ← hlen]
  | bounded cap =>
      intro bs v rest h
      simp only [decVal] at h
      cases hd : decVarNat? bs with
      | none => rw [hd] at h; simp at h
      | some q =>
          obtain ⟨n, r⟩ := q
          rw [hd] at h
          simp only at h
          by_cases hn : n < cap
          · rw [dif_pos hn] at h
            obtain ⟨hvf, hvr⟩ := Prod.mk.inj (Option.some.inj h)
            subst hvf
            subst hvr
            rw [decVarNat?_encVarNat_eq bs n _ hd]
            simp only [encVal]
          · rw [dif_neg hn] at h
            simp at h

/-! ## THE WIRE GRADE — the per-type codec as a `Kit.Codec` value -/

/-- THE value codec of schema type `t` as a `Kit.Codec` (01-core §4's
    wire grade): encode/decode + the accepted-byte policy as the EXACT
    IMAGE of the encoder (`∃ v rest, bs = encVal t v ++ rest`) + both
    law fields. The policy's content is theorem-backed:
    `decVal_encVal_append` (everything we emit decodes back — with ANY
    suffix) and `encVal_decVal_eq` (a `some` verdict certifies the
    input was in policy). -/
def valCodec (t : Ty) : Kit.Codec (List UInt8) (Value t) where
  encode := encVal t
  decode bs := (decVal t bs).map (fun p => p.1)
  policy bs := ∃ v rest, bs = encVal t v ++ rest
  decode_encode v := by
    have h := decVal_encVal_append t v []
    rw [List.append_nil] at h
    simp [h]
  decode_some_policy bs v h := by
    cases hd : decVal t bs with
    | none => rw [hd] at h; simp at h
    | some p =>
        rw [hd] at h
        simp only [Option.map_some] at h
        have hv : p.1 = v := Option.some.inj h
        subst hv
        exact ⟨p.1, p.2, encVal_decVal_eq t bs p.1 p.2 hd⟩

end SchemaCore

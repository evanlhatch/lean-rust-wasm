/-
# SchemaLang.CodecValue — the schema-typed wire codec over `Value t`

Connects `Ty`'s GADT payloads (`Value : Ty → Type`, `VList`) to the
`Codec` wire layer: `encodeValue` / `decodeValue` with a kernel-checked
append-form round trip.

Ownership: this module is the Value↔wire bridge; `SchemaLang/Codec.lean`
(scalar + combinator layer) and `SchemaLang/Ty.lean` (the universe) are
read-only dependencies — the one combinator a `Value` needs that Codec
lacks (a tagged sum, for `result`) is defined HERE, not by extending
Codec.

Deliberate exclusions (scope honesty):
- `f32`/`f64` get wire forms (bit pattern over the varint base) but NO
  round-trip theorem: `Float.ofBits ∘ toBits` has no usable core
  congruence lemmas (and NaN payloads break BEq reflexivity), so they
  are outside `CodecClosed`.
- `.ty n` is outside `CodecClosed` too: `Value` has no constructor
  indexed by `.ty` (named refs are resolved before values exist), so
  the encode arm is discharged by `nomatch`.

Driving decision: the master theorem is stated over the inductive
predicate `CodecClosed : Ty → Prop` (the provable sub-universe) rather
than as per-constructor fragments — composition (`option (list u8)`)
needs the append-form statement at arbitrary depth, which a single
induction on `CodecClosed` delivers and fragments cannot.

GADT note: lists of values ride `VList` (nested `List (Value t)` inside
the GADT is kernel-forbidden); the `VList ↔ List (Value t)` pair here is
plain functions, which the kernel accepts.
-/

module

public import SchemaLang.Codec

@[expose] public section

namespace SchemaLang

/-! ## Zigzag: signed integers over the varint base -/

/-- Map `ℤ` onto `ℕ`: nonnegative `i` to `2*i`, negative `i` to
    `2*(-i) - 1` (0 → 0, -1 → 1, 1 → 2, -2 → 3, …). -/
def zigzag (i : Int) : Nat :=
  if 0 ≤ i then (2 * i).toNat else (2 * (-i) - 1).toNat

/-- The inverse map: even `n` is a nonnegative value, odd a negative one. -/
def unzigzag (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else -(Int.ofNat (n / 2) + 1)

/-- `Int.ofNat` of a `toNat` in range is the value (the cast lemma omega
    cannot see through unaided). -/
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

/-! ## A new combinator: tagged sum (the `result` shape) -/

/-- Sum: tag byte 0 = inl, 1 = inr, each followed by the payload. -/
def encSum (encA : α → List UInt8) (encB : β → List UInt8) :
    Sum α β → List UInt8
  | .inl a => 0 :: encA a
  | .inr b => 1 :: encB b

/-- Decode a tagged sum. -/
def decSum? (decA : List UInt8 → Option (α × List UInt8))
    (decB : List UInt8 → Option (β × List UInt8)) :
    List UInt8 → Option (Sum α β × List UInt8)
  | 0 :: rest => (decA rest).map fun (a, r) => (.inl a, r)
  | 1 :: rest => (decB rest).map fun (b, r) => (.inr b, r)
  | _ => none

/-- The sum round trip, append form (mirrors Codec's combinator laws). -/
theorem decSum_encSum_append (encA : α → List UInt8) (encB : β → List UInt8)
    (decA : List UInt8 → Option (α × List UInt8))
    (decB : List UInt8 → Option (β × List UInt8))
    (hA : ∀ (a : α) (rest : List UInt8), decA (encA a ++ rest) = some (a, rest))
    (hB : ∀ (b : β) (rest : List UInt8), decB (encB b ++ rest) = some (b, rest))
    (s : Sum α β) (rest : List UInt8) :
    decSum? decA decB (encSum encA encB s ++ rest) = some (s, rest) := by
  cases s with
  | inl a => simp [encSum, decSum?, hA a rest]
  | inr b => simp [encSum, decSum?, hB b rest]

/-- Sum: `encSum`/`decSum?` — the tagged-sum twin of the Prod instance
    (`LawfulCodec`'s home is SchemaLang.Codec, the `Sum` combinators' is
    here) — composes the two halves' laws
    (`decSum_encSum_append`). The class name is qualified (`Codec.`):
    this module's namespace is `SchemaLang`, the class's home is
    `SchemaLang.Codec`. -/
instance lawfulCodecSum [Codec.LawfulCodec α] [Codec.LawfulCodec β] :
    Codec.LawfulCodec (Sum α β) where
  enc := encSum (Codec.LawfulCodec.enc (α := α)) (Codec.LawfulCodec.enc (α := β))
  dec := decSum? (Codec.LawfulCodec.dec (α := α)) (Codec.LawfulCodec.dec (α := β))
  roundtrip := decSum_encSum_append (Codec.LawfulCodec.enc (α := α))
    (Codec.LawfulCodec.enc (α := β)) (Codec.LawfulCodec.dec (α := α))
    (Codec.LawfulCodec.dec (α := β)) (Codec.LawfulCodec.roundtrip (α := α))
    (Codec.LawfulCodec.roundtrip (α := β))

/-! ## Value adapters -/

/-- `Value (.option t)` viewed as `Option (Value t)`. -/
def valOpt : {t : Ty} → Value (.option t) → Option (Value t)
  | _, .some v => some v
  | _, .none => none

/-- The inverse adapter. -/
def optVal : {t : Ty} → Option (Value t) → Value (.option t)
  | _, some v => .some v
  | _, none => .none

/-- `Value (.result ok err)` viewed as `Sum (Value ok) (Value err)`. -/
def valSum : {ok err : Ty} → Value (.result ok err) → Sum (Value ok) (Value err)
  | _, _, .ok x => .inl x
  | _, _, .err e => .inr e

/-- The inverse adapter. -/
def sumVal : {ok err : Ty} → Sum (Value ok) (Value err) → Value (.result ok err)
  | _, _, .inl x => .ok x
  | _, _, .inr e => .err e

/-! ## VList ↔ List -/

/-- Erase a `VList` to a plain list of values (functions only — the
    nested-inductive ban applies to DATA, not to this pair). -/
def vListToList : {t : Ty} → VList t → List (Value t)
  | _, .nil => []
  | _, .cons v vl => v :: vListToList vl

/-- Rebuild a `VList` from a plain list. -/
def listToVList : {t : Ty} → List (Value t) → VList t
  | _, [] => .nil
  | _, v :: vs => .cons v (listToVList vs)

/-- Char codepoint round trip (the string codec's element law). -/
@[simp] theorem char_ofNat_toNat (c : Char) : Char.ofNat c.toNat = c := by simp

/-- The string codec's payload law: codepoint round trip on lists. -/
theorem map_ofNat_toNat_id (l : List Char) :
    List.map (Char.ofNat ∘ Char.toNat) l = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      show Char.ofNat (Char.toNat c) ::
        List.map (Char.ofNat ∘ Char.toNat) l = c :: l
      rw [char_ofNat_toNat, ih]

/-- The erase/rebuild round trip on `VList` (pattern-recursion proof —
    `VList` is mutually inductive, so the `induction` tactic is barred;
    a proof-carrying def recurses structurally instead). -/
theorem listToVList_vListToList :
    ∀ {t : Ty} (vl : VList t), listToVList (vListToList vl) = vl
  | _, .nil => by simp [vListToList, listToVList]
  | _, .cons v vl => by
      simp only [vListToList, listToVList]
      rw [listToVList_vListToList vl]

/-! ## The key codec (direct — the `toTy` indirection breaks
    `encodeValue`'s structural recursion)

`encodeKey`/`decKey?` are the scalar arms of `encodeValue`/`decVal?`
factored over `KeyTy`; `decode_encodeKey_append` is their round trip,
case-split per key (the same discharges as the master theorem's scalar
arms). Coherent with the generic codec by construction — the arms are
the same terms. -/

/-- Encode a key payload (the scalar encode arms, direct). -/
def encodeKey : (k : KeyTy) → Value k.toTy → List UInt8
  | .bool, .bool b => Codec.encodeBool b
  | .u8, .u8 x => Codec.encodeU8 x
  | .u16, .u16 x => Codec.encVarNat x.toNat
  | .u32, .u32 x => Codec.encVarNat x.toNat
  | .u64, .u64 x => Codec.encVarNat x.toNat
  | .i8, .i8 x => Codec.encVarNat (zigzag x.toInt)
  | .i16, .i16 x => Codec.encVarNat (zigzag x.toInt)
  | .i32, .i32 x => Codec.encVarNat (zigzag x.toInt)
  | .i64, .i64 x => Codec.encVarNat (zigzag x.toInt)
  | .string, .string s => Codec.encList Codec.encVarNat (s.toList.map Char.toNat)

/-- Decode a key payload (the scalar decode arms, direct). -/
def decKey? : (k : KeyTy) → List UInt8 → Option (Value k.toTy × List UInt8)
  | .bool, bs => (Codec.decBool? bs).map fun (b, r) => (.bool b, r)
  | .u8, bs => (Codec.decU8? bs).map fun (x, r) => (.u8 x, r)
  | .u16, bs =>
      match Codec.decNat? bs with
      | some (n, r) =>
          if _ : n < 2 ^ 16 then some (.u16 (UInt16.ofNat n), r) else none
      | none => none
  | .u32, bs =>
      match Codec.decNat? bs with
      | some (n, r) =>
          if _ : n < 2 ^ 32 then some (.u32 (UInt32.ofNat n), r) else none
      | none => none
  | .u64, bs =>
      match Codec.decNat? bs with
      | some (n, r) =>
          if _ : n < 2 ^ 64 then some (.u64 (UInt64.ofNat n), r) else none
      | none => none
  | .i8, bs =>
      match Codec.decNat? bs with
      | some (n, r) => some (.i8 (Int8.ofInt (unzigzag n)), r)
      | none => none
  | .i16, bs =>
      match Codec.decNat? bs with
      | some (n, r) => some (.i16 (Int16.ofInt (unzigzag n)), r)
      | none => none
  | .i32, bs =>
      match Codec.decNat? bs with
      | some (n, r) => some (.i32 (Int32.ofInt (unzigzag n)), r)
      | none => none
  | .i64, bs =>
      match Codec.decNat? bs with
      | some (n, r) => some (.i64 (Int64.ofInt (unzigzag n)), r)
      | none => none
  | .string, bs =>
      match Codec.decList? Codec.decNat? bs with
      | some (ns, r) => some (.string (String.ofList (ns.map Char.ofNat)), r)
      | none => none

/-- The key round trip, append form (the scalar arms of
    `decode_encodeValue_append`, factored). -/
theorem decode_encodeKey_append : ∀ (k : KeyTy) (v : Value k.toTy)
    (rest : List UInt8),
    decKey? k (encodeKey k v ++ rest) = some (v, rest)
  | .bool, .bool _, rest => by simp [encodeKey, decKey?]
  | .u8, .u8 _, rest => by simp [encodeKey, decKey?]
  | .u16, .u16 _, rest => by simp [encodeKey, decKey?, UInt16.toNat_lt _]
  | .u32, .u32 _, rest => by simp [encodeKey, decKey?, UInt32.toNat_lt _]
  | .u64, .u64 _, rest => by simp [encodeKey, decKey?, UInt64.toNat_lt _]
  | .i8, .i8 _, rest => by simp [encodeKey, decKey?, unzigzag_zigzag]
  | .i16, .i16 _, rest => by simp [encodeKey, decKey?, unzigzag_zigzag]
  | .i32, .i32 _, rest => by simp [encodeKey, decKey?, unzigzag_zigzag]
  | .i64, .i64 _, rest => by simp [encodeKey, decKey?, unzigzag_zigzag]
  | .string, .string s, rest => by
      simp only [encodeKey, decKey?]
      rw [Codec.decList_encList_append Codec.encVarNat Codec.decNat?
        Codec.decNat_encVarNat_append (s.toList.map Char.toNat) rest]
      simp [map_ofNat_toNat_id, String.ofList_toList]

/-! ## VMap ↔ List (the association-list payloads) -/

/-- Erase a `VMap` to a plain association list (the `vListToList`
    pattern over the entry family). -/
def vMapToList : {k : KeyTy} → {v : Ty} → VMap k v → List (Value k.toTy × Value v)
  | _, _, .nil => []
  | _, _, .cons kv vv m => (kv, vv) :: vMapToList m

/-- Rebuild a `VMap` from a plain association list. -/
def listToVMap : {k : KeyTy} → {v : Ty} → List (Value k.toTy × Value v) → VMap k v
  | _, _, [] => .nil
  | _, _, (kv, vv) :: kvs => .cons kv vv (listToVMap kvs)

/-- The erase/rebuild round trip on `VMap` (the `listToVList_vListToList`
    pattern — proof-carrying def, `induction` barred on the mutual
    family). -/
theorem listToVMap_vMapToList :
    ∀ {k : KeyTy} {v : Ty} (m : VMap k v), listToVMap (vMapToList m) = m
  | _, _, .nil => by simp [vMapToList, listToVMap]
  | _, _, .cons _ _ m => by
      simp only [vMapToList, listToVMap]
      rw [listToVMap_vMapToList m]

/-! ## The tensor payload: shape-indexed values, flat wire form

The wire form is SELF-DESCRIBING and SHAPE-GATED: the dims list
(length-prefixed), then the flat row-major element list (length-
prefixed). Decode CHECKS the wire dims against the TYPE's static dims
and the element count against `dims.prod` — a mismatch is a decode
failure (`none`), the corruption-is-a-gate-failure rule — then
rebuilds the shape-indexed `TVal` (a wrong-shape value is
unconstructible, the `RowVals` discipline).

The builder (`buildTVal?`) is fuel-explicit: the shape tree's node
count is bounded by `elems.length * (dims.length + 1) + 10` (each
level consumes its elements), and every recursive call decrements —
no mutual-WF gymnastics, one measure.
-/

/-! ## The codec -/

-- (plain comment: a doc comment cannot precede `mutual` — the parser
-- rejects the block token after a dangling doc comment, the Update
-- lesson. The doc: the tensor's flat element list — the encode side's
-- row-major flatten, the `vListToList` pattern over the second family.)
mutual
def TSlices.toList : {t : Ty} → {dims : List Nat} → {m : Nat} →
    TSlices t dims m → List (Value t)
  | _, _, _, .nil => []
  | _, _, _, .cons v ss => TVal.toList v ++ TSlices.toList ss

def TVal.toList : {t : Ty} → {dims : List Nat} → TVal t dims → List (Value t)
  | _, _, .scalar v => [v]
  | _, _, .dim ss => TSlices.toList ss
end

-- (plain comment: doc comments cannot precede `mutual`. The doc:
-- rebuild `k` slices of shape `dims` off the front of a flat element
-- list. Every recursive path decrements `fuel` — the caller's bound
-- (`elems.length * (dims.length + 1) + 10`, the header's theorem) —
-- so `fuel = 0` = the shape could not be filled (the corruption gate).)
def TSlices.ofCount? : {t : Ty} → {dims : List Nat} → (k : Nat) →
    List (TVal t dims) → Option (TSlices t dims k)
  | _, _, 0, [] => some .nil
  | _, _, k + 1, x :: xs => do
      let ss ← TSlices.ofCount? k xs
      some (.cons x ss)
  | _, _, _, _ => none

/-! ## The rebuild inverse (the round trip's Lean half)

`buildOne?`/`buildSlices?` rebuild a `TVal` from its flat element list.
The theorems: the rebuild of the FLATTENED tensor is the tensor — for
any fuel `f` at least the shape's need. The need is ONE per nesting
level (the builder decrements on level changes; SIBLINGS SHARE the
fuel — `buildSlices?` passes its own `fuel` to both sub-calls), so
`needS` at any positive count is the element need. Proof-carrying defs
(the `evalBNeutral` pattern: the mutual GADT bars the `induction`
tactic, the defs recurse structurally on the payload family).
-/

-- (plain comment: doc comments cannot precede `mutual` — the Update
-- lesson's third occurrence). The rebuild's fuel need, by shape: ONE
-- per nesting level (the builder's dim level decrements; the slice
-- siblings SHARE the fuel — `buildSlices?` passes its own `fuel` to
-- both sub-calls).
mutual
def needOne (t : Ty) : List Nat → Nat
  | [] => 0
  | d :: ds => 1 + needS t ds d

def needS (t : Ty) (dims : List Nat) : Nat → Nat
  | 0 => 0
  | _ + 1 => needOne t dims
end

theorem needS_le (t : Ty) (dims : List Nat) : ∀ k, needS t dims k ≤ needS t dims (k + 1)
  | 0 => by simp [needS]
  | k + 1 => by simp [needS]

/-- the rebuild's fuel need is at most the DIM LIST's length + 1 (each
    nesting level contributes one; a zero dim cuts the chain) — so the
    decode's generous element-count bound always covers it -/
theorem needOne_le_len (t : Ty) : ∀ dims, needOne t dims ≤ dims.length + 1
  | [] => by simp [needOne]
  | d :: ds => by
      have h := needOne_le_len t ds
      have hNeedS : needS t ds d ≤ needOne t ds := by
        cases d with
        | zero => simp [needS]
        | succ _ => simp [needS]
      simp only [needOne, List.length_cons]
      omega

/-- the flat length by shape: the product, as a structural def (the
    same recursion the flatten uses, so the length lemmas are
    structural too) -/
def flatLength (t : Ty) : List Nat → Nat
  | [] => 1
  | d :: ds => d * flatLength t ds

/-- the slice-list's flat length, by count (the siblings' sum) -/
def slicesLength (t : Ty) : List Nat → Nat → Nat
  | _, 0 => 0
  | dims, k + 1 => flatLength t dims + slicesLength t dims k

theorem flatLength_eq_prod (t : Ty) : ∀ dims, flatLength t dims = dims.prod
  | [] => rfl
  | d :: ds => by
      simp only [flatLength]
      rw [show (d :: ds).prod = d * ds.prod from rfl]
      rw [flatLength_eq_prod t ds]

theorem slicesLength_mul (t : Ty) : ∀ (dims : List Nat) (k : Nat),
    slicesLength t dims k = k * flatLength t dims
  | _, 0 => by simp [slicesLength]
  | dims, k + 1 => by
      simp only [slicesLength]
      rw [slicesLength_mul t dims k, Nat.succ_mul, Nat.add_comm]

mutual
theorem TSlices.toList_length : {t : Ty} → {dims : List Nat} → {m : Nat} →
    (ss : TSlices t dims m) → (TSlices.toList ss).length = slicesLength t dims m
  | _, _, _, .nil => rfl
  | t, dims, _, .cons x ss => by
      simp only [TSlices.toList, List.length_append]
      rw [TVal.toList_length x, TSlices.toList_length ss]
      rfl

theorem TVal.toList_length : {t : Ty} → {dims : List Nat} → (tv : TVal t dims) →
    (TVal.toList tv).length = flatLength t dims
  | _, _, .scalar v => rfl
  | t, (d :: ds), .dim ss => by
      simp only [TVal.toList, flatLength]
      rw [TSlices.toList_length ss, slicesLength_mul t ds d]
end

def TSlices.sliceList : {t : Ty} → {dims : List Nat} → {m : Nat} →
    TSlices t dims m → List (TVal t dims)
  | _, _, _, .nil => []
  | _, _, _, .cons x ss => x :: TSlices.sliceList ss

/-- `ofCount?` on a slices-list's own list rebuilds it (the counted
    builder's inverse on data it produced). -/
theorem TSlices.ofCount?_sliceList : {t : Ty} → {dims : List Nat} → {m : Nat} →
    (ss : TSlices t dims m) → TSlices.ofCount? m ss.sliceList = some ss
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ ss => by
      simp only [TSlices.sliceList, TSlices.ofCount?]
      rw [ofCount?_sliceList ss]
      simp

mutual
def buildSlices? : (t : Ty) → (fuel : Nat) → (dims : List Nat) → (k : Nat) →
    List (Value t) → Option (List (TVal t dims) × List (Value t))
  | _, _, _, 0, vs => some ([], vs)
  | t, fuel, dims, k + 1, vs => do
      let (x, r) ← buildOne? t fuel dims vs
      let (xs, r2) ← buildSlices? t fuel dims k r
      pure (x :: xs, r2)
  termination_by _ fuel dims k _ => (fuel, k, List.length dims)

def buildOne? : (t : Ty) → (fuel : Nat) → (dims : List Nat) →
    List (Value t) → Option (TVal t dims × List (Value t))
  | _, _, [], [] => none
  -- ONE element off the front, the TAIL FLOWS to the siblings (the
  -- `[v]`-pattern bug this replaced consumed the tail and rejected
  -- every multi-element tensor — invisible without the round-trip
  -- theorem above; this is why the theorem is mandatory, not
  -- decoration)
  | _, _, [], v :: rest => some (TVal.scalar v, rest)
  | _, 0, _ :: _, _ => none
  | t, fuel + 1, d :: ds, vs => do
      -- d inner slices of shape ds, off the front; the count-checked
      -- list → the length-indexed slice list
      let (inner, r) ← buildSlices? t fuel ds d vs
      let ss ← TSlices.ofCount? d inner
      some (TVal.dim ss, r)
  termination_by _ fuel dims _ => (fuel, 0, dims.length)
end

mutual
theorem buildSlices?_toList : {t : Ty} → {dims : List Nat} → {k : Nat} →
    (ss : TSlices t dims k) → (f : Nat) → needS t dims k ≤ f →
    ∀ rest : List (Value t),
      buildSlices? t f dims k (TSlices.toList ss ++ rest)
        = some (TSlices.sliceList ss, rest)
  | _, _, _, .nil, _, _, rest => by
      -- the builder is WF (termination_by) — its equations are simp
      -- lemmas, not definitional (rfl cannot whnf a WellFounded.fix)
      simp [TSlices.toList, TSlices.sliceList, buildSlices?]
  | t, dims, _, @TSlices.cons _ _ _ x ss', fuel, h, rest => by
      -- the sibling fuel is SHARED: both sub-calls run at the SAME
      -- `fuel`, and `needS (k'+1) = needOne dims` covers each
      have h' : needOne t dims ≤ fuel := by simpa [needS] using h
      have hss' : needS t dims _ ≤ fuel := Nat.le_trans (needS_le t dims _) h
      have hx := buildOne?_toList x fuel h' (TSlices.toList ss' ++ rest)
      have hss := buildSlices?_toList ss' fuel hss' rest
      simp only [TSlices.toList, List.append_assoc, TSlices.sliceList,
        buildSlices?]
      rw [hx]
      simp [hss]
  termination_by _ _ _ ss _ _ _ => sizeOf ss

theorem buildOne?_toList : {t : Ty} → {dims : List Nat} → (tv : TVal t dims) →
    (f : Nat) → needOne t dims ≤ f → ∀ rest : List (Value t),
      buildOne? t f dims (TVal.toList tv ++ rest) = some (tv, rest)
  | _, [], .scalar v, _, _, rest => by
      simp only [TVal.toList]
      simp [buildOne?]
  | _, _ :: _, .dim _, 0, h, _ => by simp [needOne] at h
  | t, (d :: ds), .dim ss, fuel + 1, h, rest => by
      -- h : needOne t (d :: ds) = 1 + needS t ds d ≤ fuel + 1 — the dim
      -- level's one decrement buys the slices' need
      have hNeed : needS t ds d ≤ fuel := by
        have hdef : needOne t (d :: ds) = 1 + needS t ds d := by simp [needOne]
        omega
      simp only [TVal.toList]
      simp only [buildOne?]
      rw [buildSlices?_toList ss fuel hNeed rest]
      simp [TSlices.ofCount?_sliceList]
  termination_by _ _ tv _ _ _ => sizeOf tv
end



/-- Encode a schema-typed value. Composite types reuse Codec's
    combinators; `future`/`stream` erase to their payload (the
    `Ty.toType` precedent); `.ty` refs carry no values (nomatch). -/
def encodeValue : (t : Ty) → Value t → List UInt8
  | .bool, .bool b => Codec.encodeBool b
  | .u8, .u8 x => Codec.encodeU8 x
  | .u16, .u16 x => Codec.encVarNat x.toNat
  | .u32, .u32 x => Codec.encVarNat x.toNat
  | .u64, .u64 x => Codec.encVarNat x.toNat
  | .i8, .i8 x => Codec.encVarNat (zigzag x.toInt)
  | .i16, .i16 x => Codec.encVarNat (zigzag x.toInt)
  | .i32, .i32 x => Codec.encVarNat (zigzag x.toInt)
  | .i64, .i64 x => Codec.encVarNat (zigzag x.toInt)
  | .f32, .f32 x => Codec.encVarNat (Float32.toBits x).toNat
  | .f64, .f64 x => Codec.encVarNat (Float.toBits x).toNat
  | .string, .string s => Codec.encList Codec.encVarNat (s.toList.map Char.toNat)
  | .bytes, .bytes bs => Codec.encBytes bs
  | .option a, v => Codec.encOpt (encodeValue a) (valOpt v)
  | .result ok err, v => encSum (encodeValue ok) (encodeValue err) (valSum v)
  | .list a, .list vl => Codec.encList (encodeValue a) (vListToList vl)
  -- the map wire: the length-prefixed ENTRY list (each entry the
  -- concatenated key/value encodings, `Codec.encProd` over the DIRECT key
  -- codec — the `toTy` indirection would break structural recursion);
  -- insertion order is payload data and rides the wire (the `list`
  -- discipline)
  | .map k v, .map m =>
      Codec.encList (Codec.encProd (encodeKey k) (encodeValue v)) (vMapToList m)
  | .set k, .set vl => Codec.encList (encodeKey k) (vListToList vl)
  | .future a, .future x => encodeValue a x
  | .stream a, .stream vl => Codec.encList (encodeValue a) (vListToList vl)
  -- the tensor wire: the dims list, then the flat row-major elements
  -- (each length-prefixed by `encList` — self-describing + gated)
  | .tensor dims a, .tensor tv =>
      Codec.encList Codec.encVarNat dims
        ++ Codec.encList (encodeValue a) (TVal.toList tv)
  | .ty _, v => nomatch v

/-- The append-form decoder: returns the value AND the remaining bytes —
    the shape Codec's compositional decoders (`decOpt?`, `decList?`,
    `decSum?`) consume. Trailing garbage passes through untouched. -/
def decVal? (t : Ty) (bs : List UInt8) : Option (Value t × List UInt8) :=
  match t with
  | .bool => (Codec.decBool? bs).map fun (b, r) => (.bool b, r)
  | .u8 => (Codec.decU8? bs).map fun (x, r) => (.u8 x, r)
  | .u16 =>
      match Codec.decNat? bs with
      | some (n, r) =>
          if _ : n < 2 ^ 16 then some (.u16 (UInt16.ofNat n), r) else none
      | none => none
  | .u32 =>
      match Codec.decNat? bs with
      | some (n, r) =>
          if _ : n < 2 ^ 32 then some (.u32 (UInt32.ofNat n), r) else none
      | none => none
  | .u64 =>
      match Codec.decNat? bs with
      | some (n, r) =>
          if _ : n < 2 ^ 64 then some (.u64 (UInt64.ofNat n), r) else none
      | none => none
  | .i8 =>
      match Codec.decNat? bs with
      | some (n, r) => some (.i8 (Int8.ofInt (unzigzag n)), r)
      | none => none
  | .i16 =>
      match Codec.decNat? bs with
      | some (n, r) => some (.i16 (Int16.ofInt (unzigzag n)), r)
      | none => none
  | .i32 =>
      match Codec.decNat? bs with
      | some (n, r) => some (.i32 (Int32.ofInt (unzigzag n)), r)
      | none => none
  | .i64 =>
      match Codec.decNat? bs with
      | some (n, r) => some (.i64 (Int64.ofInt (unzigzag n)), r)
      | none => none
  | .f32 =>
      match Codec.decNat? bs with
      | some (n, r) =>
          if _ : n < 2 ^ 32 then
            some (.f32 (Float32.ofBits (UInt32.ofNat n)), r)
          else none
      | none => none
  | .f64 =>
      match Codec.decNat? bs with
      | some (n, r) =>
          if _ : n < 2 ^ 64 then
            some (.f64 (Float.ofBits (UInt64.ofNat n)), r)
          else none
      | none => none
  | .string =>
      match Codec.decList? Codec.decNat? bs with
      | some (ns, r) => some (.string (String.ofList (ns.map Char.ofNat)), r)
      | none => none
  | .bytes => (Codec.decBytes? bs).map fun (x, r) => (.bytes x, r)
  | .option a =>
      (Codec.decOpt? (decVal? a) bs).map fun (o, r) => (optVal o, r)
  | .result ok err =>
      (decSum? (decVal? ok) (decVal? err) bs).map fun (s, r) => (sumVal s, r)
  | .list a =>
      match Codec.decList? (decVal? a) bs with
      | some (xs, r) => some (.list (listToVList xs), r)
      | none => none
  | .map k v =>
      match Codec.decList? (Codec.decProd? (decKey? k) (decVal? v)) bs with
      | some (kvs, r) => some (.map (listToVMap kvs), r)
      | none => none
  | .set k =>
      match Codec.decList? (decKey? k) bs with
      | some (xs, r) => some (.set (listToVList xs), r)
      | none => none
  | .future a => (decVal? a bs).map fun (x, r) => (.future x, r)
  | .stream a =>
      match Codec.decList? (decVal? a) bs with
      | some (xs, r) => some (.stream (listToVList xs), r)
      | none => none
  | .tensor dims a =>
      -- THE SHAPE GATE: wire dims must equal the TYPE's static dims,
      -- and the flat elements must fill `dims.prod` — a mismatch is a
      -- decode failure, never a mis-shaped `TVal` (unconstructible).
      match Codec.decList? Codec.decNat? bs with
      | none => none
      | some (wireDims, r) =>
          if wireDims != dims then none
          else match Codec.decList? (decVal? a) r with
            | none => none
            | some (elems, r2) =>
                if elems.length != dims.prod then none
                else match buildOne? a (elems.length * (dims.length + 1) + dims.length + 10) dims elems with
                  | some (tv, []) => some (.tensor tv, r2)
                  | _ => none
  | .ty _ => none

/-- The user-facing decoder: same wire, remainder discarded. -/
def decodeValue (t : Ty) (bs : List UInt8) : Option (Value t) :=
  (decVal? t bs).map fun p => p.1

/-! ## The round-trip theorem -/

/-- The codec-closed sub-universe of `Ty`: every type whose `Value`
    round trip is PROVED. Floats are out (no `ofBits ∘ toBits` core
    lemmas); `.ty` refs are out (no `Value` constructor exists).
    `Type`-valued (not `Prop`): defaultValue eliminates it into
    `Value t` — a `Prop` wrapper has no large elimination. -/
inductive CodecClosed : Ty → Type where
  | bool : CodecClosed .bool
  | u8 : CodecClosed .u8
  | u16 : CodecClosed .u16
  | u32 : CodecClosed .u32
  | u64 : CodecClosed .u64
  | i8 : CodecClosed .i8
  | i16 : CodecClosed .i16
  | i32 : CodecClosed .i32
  | i64 : CodecClosed .i64
  | string : CodecClosed .string
  | bytes : CodecClosed .bytes
  | option {t : Ty} : CodecClosed t → CodecClosed (.option t)
  | result {ok err : Ty} : CodecClosed ok → CodecClosed err →
      CodecClosed (.result ok err)
  | list {t : Ty} : CodecClosed t → CodecClosed (.list t)
  | map {k : KeyTy} {v : Ty} : CodecClosed v → CodecClosed (.map k v)
  | set {k : KeyTy} : CodecClosed (.set k)
  | /-- the tensor's element codec (the dims are static data — the
      shape gate needs no closure hypothesis) -/
  tensor {t : Ty} {dims : List Nat} : CodecClosed t → CodecClosed (.tensor dims t)
  | future {t : Ty} : CodecClosed t → CodecClosed (.future t)
  | stream {t : Ty} : CodecClosed t → CodecClosed (.stream t)

/-! THE COMPOSITE VALUE INSTANCES — placed BEFORE the append-form
theorems (their consumers): Lean's linear elaboration makes an
instance declared later invisible at an earlier use site, so the
composites sit above the per-container append theorems, which route
their round-trips through the class `roundtrip` fields; the LEAVES
live below the master theorem (they cite its arms). Each composite
guards on the element/payload class parameter where honest
(`[Codec.LawfulCodec (Value a)]` and friends), and its law field
composes through `Codec.LawfulCodec.roundtrip` at the combinator
shape (`decOpt_encOpt_append`, `decSum_encSum_append`,
`decList_encList_append`) or the module's own key/list lemmas
(`decode_encodeKey_append`, `listToVList_vListToList`). -/

instance {a : Ty} [Codec.LawfulCodec (Value a)] :
    Codec.LawfulCodec (Value (.option a)) where
  enc := fun v => Codec.encOpt (Codec.LawfulCodec.enc (α := Value a)) (valOpt v)
  dec := fun bs =>
    (Codec.decOpt? (Codec.LawfulCodec.dec (α := Value a)) bs).map (fun o => (optVal o.1, o.2))
  roundtrip := by
    intro v rest
    cases v with
    | none => simp [Codec.encOpt, Codec.decOpt?, valOpt, optVal]
    | some x =>
        simp only [valOpt]
        rw [Codec.decOpt_encOpt_append (Codec.LawfulCodec.enc (α := Value a))
          (Codec.LawfulCodec.dec (α := Value a))
          (Codec.LawfulCodec.roundtrip (α := Value a)) (some x) rest]
        simp [optVal]

instance {ok err : Ty} [Codec.LawfulCodec (Value ok)]
    [Codec.LawfulCodec (Value err)] : Codec.LawfulCodec (Value (.result ok err)) where
  enc := fun v => encSum (Codec.LawfulCodec.enc (α := Value ok))
    (Codec.LawfulCodec.enc (α := Value err)) (valSum v)
  dec := fun bs =>
    (decSum? (Codec.LawfulCodec.dec (α := Value ok))
      (Codec.LawfulCodec.dec (α := Value err)) bs).map (fun s => (sumVal s.1, s.2))
  roundtrip := by
    intro v rest
    cases v with
    | ok x =>
        simp only [valSum]
        rw [decSum_encSum_append (Codec.LawfulCodec.enc (α := Value ok))
          (Codec.LawfulCodec.enc (α := Value err))
          (Codec.LawfulCodec.dec (α := Value ok)) (Codec.LawfulCodec.dec (α := Value err))
          (Codec.LawfulCodec.roundtrip (α := Value ok))
          (Codec.LawfulCodec.roundtrip (α := Value err)) (.inl x) rest]
        simp [sumVal]
    | err e =>
        simp only [valSum]
        rw [decSum_encSum_append (Codec.LawfulCodec.enc (α := Value ok))
          (Codec.LawfulCodec.enc (α := Value err))
          (Codec.LawfulCodec.dec (α := Value ok)) (Codec.LawfulCodec.dec (α := Value err))
          (Codec.LawfulCodec.roundtrip (α := Value ok))
          (Codec.LawfulCodec.roundtrip (α := Value err)) (.inr e) rest]
        simp [sumVal]

instance {a : Ty} [Codec.LawfulCodec (Value a)] :
    Codec.LawfulCodec (Value (.list a)) where
  enc := fun v => match v with
    | .list vl => Codec.encList (Codec.LawfulCodec.enc (α := Value a)) (vListToList vl)
  dec := fun bs =>
    match Codec.decList? (Codec.LawfulCodec.dec (α := Value a)) bs with
    | some (xs, r) => some (.list (listToVList xs), r)
    | none => none
  roundtrip := by
    intro v rest
    cases v with
    | list vl =>
        -- the `enc` field's match on `Value.list` is iota (simp, not
        -- rw — the rw matcher cannot see through the match scrutinee)
        simp only
        rw [Codec.decList_encList_append (Codec.LawfulCodec.enc (α := Value a))
          (Codec.LawfulCodec.dec (α := Value a))
          (Codec.LawfulCodec.roundtrip (α := Value a)) (vListToList vl) rest]
        simp [listToVList_vListToList]

instance {k : KeyTy} {v : Ty} [Codec.LawfulCodec (Value v)] :
    Codec.LawfulCodec (Value (.map k v)) where
  enc := fun r => match r with
    | .map m => Codec.encList
        (Codec.encProd (encodeKey k) (Codec.LawfulCodec.enc (α := Value v))) (vMapToList m)
  dec := fun bs =>
    match Codec.decList? (Codec.decProd? (decKey? k) (Codec.LawfulCodec.dec (α := Value v))) bs with
    | some (kvs, r) => some (.map (listToVMap kvs), r)
    | none => none
  roundtrip := by
    intro r rest
    cases r with
    | map m =>
        simp only
        rw [Codec.decList_encList_append
          (Codec.encProd (encodeKey k) (Codec.LawfulCodec.enc (α := Value v)))
          (Codec.decProd? (decKey? k) (Codec.LawfulCodec.dec (α := Value v)))
          (fun p r => Codec.decProd_encProd_append (encodeKey k)
            (Codec.LawfulCodec.enc (α := Value v)) (decKey? k)
            (Codec.LawfulCodec.dec (α := Value v)) (decode_encodeKey_append k)
            (Codec.LawfulCodec.roundtrip (α := Value v)) p r)
          (vMapToList m) rest]
        simp [listToVMap_vMapToList]

/-- The `set` instance needs NO payload guard: its element codec is the
    KEY codec (`encodeKey k`/`decKey? k`), whose law needs no closure
    hypothesis (`decode_encodeKey_append` — the module's key half) —
    `Codec.decList_encList_append` at that law proves the list shape
    directly (no class guard to compose). -/
instance {k : KeyTy} : Codec.LawfulCodec (Value (.set k)) where
  enc := fun v => match v with
    | .set vl => Codec.encList (encodeKey k) (vListToList vl)
  dec := fun bs =>
    match Codec.decList? (decKey? k) bs with
    | some (xs, r) => some (.set (listToVList xs), r)
    | none => none
  roundtrip := by
    intro v rest
    cases v with
    | set vl =>
        simp only
        rw [Codec.decList_encList_append (encodeKey k) (decKey? k)
          (decode_encodeKey_append k) (vListToList vl) rest]
        simp [listToVList_vListToList]

instance {a : Ty} [Codec.LawfulCodec (Value a)] :
    Codec.LawfulCodec (Value (.future a)) where
  enc := fun v => match v with
    | .future x => Codec.LawfulCodec.enc (α := Value a) x
  dec := fun bs => (Codec.LawfulCodec.dec (α := Value a) bs).map (fun x => (.future x.1, x.2))
  roundtrip := by
    intro v rest
    cases v with
    | future x =>
        simp only
        rw [Codec.LawfulCodec.roundtrip (α := Value a) x rest]
        rfl

instance {a : Ty} [Codec.LawfulCodec (Value a)] :
    Codec.LawfulCodec (Value (.stream a)) where
  enc := fun v => match v with
    | .stream vl => Codec.encList (Codec.LawfulCodec.enc (α := Value a)) (vListToList vl)
  dec := fun bs =>
    match Codec.decList? (Codec.LawfulCodec.dec (α := Value a)) bs with
    | some (xs, r) => some (.stream (listToVList xs), r)
    | none => none
  roundtrip := by
    intro v rest
    cases v with
    | stream vl =>
        simp only
        rw [Codec.decList_encList_append (Codec.LawfulCodec.enc (α := Value a))
          (Codec.LawfulCodec.dec (α := Value a))
          (Codec.LawfulCodec.roundtrip (α := Value a)) (vListToList vl) rest]
        simp [listToVList_vListToList]

/-- The tensor instance: the same proof the master theorem's tensor arm
    runs, with the two list decodes composed THROUGH the class (the
    dims list as `Codec.LawfulCodec (List Nat)`, restated in its
    concrete combinator shape by `show … from` — the class law and the
    combinator law are the same statement; the flat elements as
    `Codec.LawfulCodec (List (Value a))`); the shape gate + the fuel
    bound + `buildOne?_toList` are the module's own lemmas. -/
instance {dims : List Nat} {a : Ty} [Codec.LawfulCodec (Value a)] :
    Codec.LawfulCodec (Value (.tensor dims a)) where
  enc := fun v => match v with
    | .tensor tv => Codec.encList Codec.encVarNat dims
        ++ Codec.encList (Codec.LawfulCodec.enc (α := Value a)) (TVal.toList tv)
  dec := fun bs =>
    match Codec.decList? Codec.decNat? bs with
    | none => none
    | some (wireDims, r) =>
        if wireDims != dims then none
        else match Codec.decList? (Codec.LawfulCodec.dec (α := Value a)) r with
          | none => none
          | some (elems, r2) =>
              if elems.length != dims.prod then none
              else match buildOne? a (elems.length * (dims.length + 1) + dims.length + 10)
                    dims elems with
                | some (tv', []) => some (.tensor tv', r2)
                | _ => none
  roundtrip := by
    intro v rest
    cases v with
    | tensor tv =>
        -- the `enc` field's match on `Value.tensor` is iota (simp, not
        -- rw — the rw matcher cannot see through the match scrutinee)
        simp only
        rw [List.append_assoc,
          (show ∀ (d : List Nat) (r : List UInt8),
                Codec.decList? Codec.decNat? (Codec.encList Codec.encVarNat d ++ r)
                  = some (d, r) from
            by
              intro d r
              change Codec.LawfulCodec.dec (α := List Nat)
                  (Codec.LawfulCodec.enc (α := List Nat) d ++ r) = some (d, r)
              exact Codec.LawfulCodec.roundtrip (α := List Nat) d r)
            dims (Codec.encList (Codec.LawfulCodec.enc (α := Value a)) (TVal.toList tv) ++ rest)]
        -- the dims match's iota (simp, not rw — the rw-produced
        -- scrutinee is a `some` ctor the rewriter cannot see through)
        simp only
        rw [(show ∀ (es : List (Value a)) (r : List UInt8),
                Codec.decList? (Codec.LawfulCodec.dec (α := Value a))
                  (Codec.encList (Codec.LawfulCodec.enc (α := Value a)) es ++ r)
                  = some (es, r) from
              by
                intro es r
                change Codec.LawfulCodec.dec (α := List (Value a))
                    (Codec.LawfulCodec.enc (α := List (Value a)) es ++ r) = some (es, r)
                exact Codec.LawfulCodec.roundtrip (α := List (Value a)) es r)
          (TVal.toList tv) rest]
        simp only [TVal.toList_length tv, flatLength_eq_prod,
          if_neg (by simp : ¬((dims != dims) = true)),
          if_neg (by simp : ¬((dims.prod != dims.prod) = true))]
        have hApp : tv.toList = tv.toList ++ [] := (List.append_nil _).symm
        rw [hApp]
        rw [buildOne?_toList tv _ (by
          have h1 := needOne_le_len a dims
          omega) []]

/-! ## The append-form per-container theorems

The per-container append statements the master round-trip theorem's
composite arms consume; each body routes through the composite
instance's `roundtrip` (the local instance is the closure hypothesis in
class form — the set arm needs none: its codec is the key codec). -/


/-- The VList round trip over an element codec, append form (list arm). -/
theorem decode_encListVList_append (t : Ty)
    (ih : ∀ (v : Value t) (rest : List UInt8),
      decVal? t (encodeValue t v ++ rest) = some (v, rest))
    (vl : VList t) (rest : List UInt8) :
    decVal? (.list t)
        (Codec.encList (encodeValue t) (vListToList vl) ++ rest)
      = some (.list vl, rest) := by
  letI : Codec.LawfulCodec (Value t) := ⟨encodeValue t, decVal? t, ih⟩
  exact Codec.LawfulCodec.roundtrip (α := Value (.list t)) (.list vl) rest

/-- The VList round trip over an element codec, append form (stream arm —
    same wire shape, different `Value` constructor). -/
theorem decode_encStreamVList_append (t : Ty)
    (ih : ∀ (v : Value t) (rest : List UInt8),
      decVal? t (encodeValue t v ++ rest) = some (v, rest))
    (vl : VList t) (rest : List UInt8) :
    decVal? (.stream t)
        (Codec.encList (encodeValue t) (vListToList vl) ++ rest)
      = some (.stream vl, rest) := by
  letI : Codec.LawfulCodec (Value t) := ⟨encodeValue t, decVal? t, ih⟩
  exact Codec.LawfulCodec.roundtrip (α := Value (.stream t)) (.stream vl) rest

/-- The association-list round trip over the key codec + a value codec,
    append form (map arm): the entry codec is `Codec.encProd`/`Codec.decProd?`, so
    the list combinator's law instantiates at the pair law (the key half
    by `decode_encodeKey_append` — keys need no closure hypothesis). -/
theorem decode_encListVMap_append (k : KeyTy) (v : Ty)
    (ihV : ∀ (vv : Value v) (rest : List UInt8),
      decVal? v (encodeValue v vv ++ rest) = some (vv, rest))
    (m : VMap k v) (rest : List UInt8) :
    decVal? (.map k v)
        (Codec.encList (Codec.encProd (encodeKey k) (encodeValue v))
            (vMapToList m) ++ rest)
      = some (.map m, rest) := by
  letI : Codec.LawfulCodec (Value v) := ⟨encodeValue v, decVal? v, ihV⟩
  exact Codec.LawfulCodec.roundtrip (α := Value (.map k v)) (.map m) rest

/-- The VList round trip over the key codec, append form (set arm —
    same wire shape as `list`, different `Value` constructor; the set
    instance's codec is the KEY codec directly, so no closure hypothesis
    is needed). -/
theorem decode_encSetVList_append (k : KeyTy)
    (vl : VList k.toTy) (rest : List UInt8) :
    decVal? (.set k)
        (Codec.encList (encodeKey k) (vListToList vl) ++ rest)
      = some (.set vl, rest) := by
  exact Codec.LawfulCodec.roundtrip (α := Value (.set k)) (.set vl) rest

/-- THE theorem: over the codec-closed universe, `decode ∘ encode = id`,
    in append form (the trailing bytes flow through every layer). -/
theorem decode_encodeValue_append (t : Ty) (h : CodecClosed t) :
    ∀ (v : Value t) (rest : List UInt8),
      decVal? t (encodeValue t v ++ rest) = some (v, rest) := by
  induction h with
  | bool =>
      intro v rest
      cases v
      simp [encodeValue, decVal?]
  | u8 =>
      intro v rest
      cases v
      simp [encodeValue, decVal?]
  | u16 =>
      intro v rest
      cases v
      simp [encodeValue, decVal?, UInt16.toNat_lt _]
  | u32 =>
      intro v rest
      cases v
      simp [encodeValue, decVal?, UInt32.toNat_lt _]
  | u64 =>
      intro v rest
      cases v
      simp [encodeValue, decVal?, UInt64.toNat_lt _]
  | i8 =>
      intro v rest
      cases v
      simp [encodeValue, decVal?, unzigzag_zigzag]
  | i16 =>
      intro v rest
      cases v
      simp [encodeValue, decVal?, unzigzag_zigzag]
  | i32 =>
      intro v rest
      cases v
      simp [encodeValue, decVal?, unzigzag_zigzag]
  | i64 =>
      intro v rest
      cases v
      simp [encodeValue, decVal?, unzigzag_zigzag]
  | string =>
      intro v rest
      cases v with
      | string s =>
          simp only [encodeValue, decVal?]
          rw [Codec.decList_encList_append Codec.encVarNat Codec.decNat?
            Codec.decNat_encVarNat_append (s.toList.map Char.toNat) rest]
          simp [map_ofNat_toNat_id, String.ofList_toList]
  | bytes =>
      intro v rest
      cases v
      simp [encodeValue, decVal?]
  | option _ ih =>
      intro v rest
      cases v with
      | none =>
          simp [encodeValue, decVal?, valOpt, optVal, Codec.encOpt,
            Codec.decOpt?]
      | some x =>
          simp [encodeValue, decVal?, valOpt, optVal, Codec.encOpt,
            Codec.decOpt?, ih]
  | result _ _ ihok iherr =>
      intro v rest
      cases v with
      | ok x =>
          simp [encodeValue, decVal?, valSum, sumVal, encSum, decSum?,
            ihok]
      | err e =>
          simp [encodeValue, decVal?, valSum, sumVal, encSum, decSum?,
            iherr]
  | list _ ih =>
      intro v rest
      cases v with
      | list vl =>
          simp only [encodeValue]
          rw [decode_encListVList_append _ ih vl rest]
  | map _ ihV =>
      intro v rest
      cases v with
      | map m =>
          simp only [encodeValue]
          rw [decode_encListVMap_append _ _ ihV m rest]
  | set =>
      intro v rest
      cases v with
      | set vl =>
          simp only [encodeValue]
          rw [decode_encSetVList_append _ vl rest]
  | future _ ih =>
      intro v rest
      cases v with
      | future x => simp [encodeValue, decVal?, ih x rest]
  | stream _ ih =>
      intro v rest
      cases v with
      | stream vl =>
          simp only [encodeValue]
          rw [decode_encStreamVList_append _ ih vl rest]
  | @tensor a dims h ih =>
      intro v rest
      cases v with
      | tensor tv =>
          -- the wire: dims-list ++ flat-elements; both round trip (the
          -- dims by the combinator, the elements by the ih), the count
          -- gate reads the flatten's length (the product), and the
          -- rebuild-inverse assembles the original TVal
          simp only [encodeValue, decVal?]
          rw [List.append_assoc, Codec.decList_encList_append Codec.encVarNat
            Codec.decNat? Codec.decNat_encVarNat_append dims
            (Codec.encList (encodeValue a) (TVal.toList tv) ++ rest)]
          -- the match's iota (simp, not rw — the rw-produced scrutinee is
          -- a `some` ctor the rewriter cannot see through)
          simp only
          rw [Codec.decList_encList_append (encodeValue a) (decVal? a) ih
            (TVal.toList tv) rest]
          simp only [TVal.toList_length tv, flatLength_eq_prod,
            if_neg (by simp : ¬((dims != dims) = true)),
            if_neg (by simp : ¬((dims.prod != dims.prod) = true))]
          have hApp : tv.toList = tv.toList ++ [] := (List.append_nil _).symm
          rw [hApp]
          rw [buildOne?_toList tv _ (by
            have h1 := needOne_le_len a dims
            omega) []]

/-- The plain round trip: `decodeValue t (encodeValue t v) = some v`. -/
theorem decode_encodeValue (t : Ty) (v : Value t) (h : CodecClosed t) :
    decodeValue t (encodeValue t v) = some v := by
  simp only [decodeValue]
  have h2 := decode_encodeValue_append t h v []
  simp only [List.append_nil] at h2
  simp [h2]

/-!
THE VALUE INSTANCES: each `Value t` ctor family riding the class — the
shape this module's codec-closed story genuinely admits (the honest
`[CodecClosed t]`-guarded single instance is NOT statable: Lean rejects
a Type-valued non-`class` inductive as an instance-implicit binder, so
`[cc : CodecClosed t]` does not compile, and an explicit `(cc : …)`
parameter would be inert — `CodecClosed`'s ctors carry no instance
attribute, so typeclass search could never discharge the guard).

- THE LEAVES (`bool`..`string`, `bytes`) cite the master theorem's
  arms (`decode_encodeValue_append … CodecClosed.X`) — the induction
already proved each; nothing re-proved.
- THE COMPOSITES (`option`..`tensor`) live ABOVE the append-form
  theorems — the section before them — so those (and, through them,
  the master theorem's composite arms) can route through the class
  `roundtrip` fields; THIS section holds the LEAVES only. Each
  composite guards on the element/payload class parameter where honest
  (`[Codec.LawfulCodec (Value a)]` and friends — the task's
  `[LawfulCodec t]` guard).
- `f32`/`f64` stay OUT (no `ofBits ∘ toBits` law — the module's
  exclusion, unchanged) and `.ty` has no `Value` constructor (no
  instance is even statable).
-/

instance lawfulCodecValueBool : Codec.LawfulCodec (Value .bool) where
  enc := encodeValue .bool
  dec := decVal? .bool
  roundtrip := decode_encodeValue_append .bool CodecClosed.bool

instance lawfulCodecValueU8 : Codec.LawfulCodec (Value .u8) where
  enc := encodeValue .u8
  dec := decVal? .u8
  roundtrip := decode_encodeValue_append .u8 CodecClosed.u8

instance lawfulCodecValueU16 : Codec.LawfulCodec (Value .u16) where
  enc := encodeValue .u16
  dec := decVal? .u16
  roundtrip := decode_encodeValue_append .u16 CodecClosed.u16

instance lawfulCodecValueU32 : Codec.LawfulCodec (Value .u32) where
  enc := encodeValue .u32
  dec := decVal? .u32
  roundtrip := decode_encodeValue_append .u32 CodecClosed.u32

instance lawfulCodecValueU64 : Codec.LawfulCodec (Value .u64) where
  enc := encodeValue .u64
  dec := decVal? .u64
  roundtrip := decode_encodeValue_append .u64 CodecClosed.u64

instance lawfulCodecValueI8 : Codec.LawfulCodec (Value .i8) where
  enc := encodeValue .i8
  dec := decVal? .i8
  roundtrip := decode_encodeValue_append .i8 CodecClosed.i8

instance lawfulCodecValueI16 : Codec.LawfulCodec (Value .i16) where
  enc := encodeValue .i16
  dec := decVal? .i16
  roundtrip := decode_encodeValue_append .i16 CodecClosed.i16

instance lawfulCodecValueI32 : Codec.LawfulCodec (Value .i32) where
  enc := encodeValue .i32
  dec := decVal? .i32
  roundtrip := decode_encodeValue_append .i32 CodecClosed.i32

instance lawfulCodecValueI64 : Codec.LawfulCodec (Value .i64) where
  enc := encodeValue .i64
  dec := decVal? .i64
  roundtrip := decode_encodeValue_append .i64 CodecClosed.i64

instance lawfulCodecValueString : Codec.LawfulCodec (Value .string) where
  enc := encodeValue .string
  dec := decVal? .string
  roundtrip := decode_encodeValue_append .string CodecClosed.string

instance lawfulCodecValueBytes : Codec.LawfulCodec (Value .bytes) where
  enc := encodeValue .bytes
  dec := decVal? .bytes
  roundtrip := decode_encodeValue_append .bytes CodecClosed.bytes



-- (plain comment: doc comments cannot precede `mutual`. The doc:
-- a default value for any codec-closed type — the generator/shrinker
-- base case (structural recursion on the CodecClosed proof). The
-- tensor default FILLS the shape with the element's default.)
/-- the counted builder never fails on a length-matched list (the
    default-tensor's extraction) -/
theorem ofCount?_of_length : ∀ {t : Ty} {dims : List Nat} (l : List (TVal t dims)) (k : Nat),
    l.length = k → ∃ ss, TSlices.ofCount? k l = some ss
  | _, _, [], 0, _ => ⟨.nil, rfl⟩
  | _, _, x :: l, k + 1, h => by
      have hl : l.length = k := by
        have h2 := h
        simp at h2
        exact h2
      have ⟨ss, hss⟩ := ofCount?_of_length l k hl
      exact ⟨.cons x ss, by simp [TSlices.ofCount?, hss]⟩

def defaultTVal (elemDefault : Value t) : (dims : List Nat) → TVal t dims
  | [] => .scalar elemDefault
  | d :: ds => by
      have hex := ofCount?_of_length
        (List.replicate d (defaultTVal elemDefault ds)) d
        (by simp [List.length_replicate])
      cases hop : TSlices.ofCount? d (List.replicate d (defaultTVal elemDefault ds)) with
      | some ss' => exact .dim ss'
      | none =>
          have hFalse : False := by
            obtain ⟨ss, hs⟩ := hex
            rw [hs] at hop
            exact absurd hop (by simp)
          exact hFalse.elim

-- (plain comment: doc comments are ModuleDocs-extracted, byte-tied.
-- The CONSOLIDATION: the default/zero value per `Ty` lived in FOUR
-- match tables (`defaultValue` here, `Validate.defaultValue?`,
-- `Emit.Rust.rustLiteral?`, the `genVal` fallback) — now the `DefaultVal`
-- instances below are the ONE table; the other three consume it.
-- Composite ctors compose by construction, mirroring what the old
-- tables spelled out per arm: option → none, list/map/set/stream →
-- empty, result → ok default, future → default, tensor → the
-- shape-filled default (`defaultTVal`).)

-- The coverage: every `Ty` ctor except `.ty` — `Value` has no
-- constructor indexed by `.ty` (named refs are resolved before values
-- exist), so no instance is even statable. The honest gap.
-- `f32`/`f64` DO get instances (the zero): they sit outside
-- `CodecClosed` (no round-trip proof — the module's own exclusion
-- note), but that is a codec-admission fact, not a default gap.
class DefaultVal (t : Ty) where
  default : Value t

instance : DefaultVal .bool := ⟨.bool false⟩
instance : DefaultVal .u8 := ⟨.u8 0⟩
instance : DefaultVal .u16 := ⟨.u16 0⟩
instance : DefaultVal .u32 := ⟨.u32 0⟩
instance : DefaultVal .u64 := ⟨.u64 0⟩
instance : DefaultVal .i8 := ⟨.i8 0⟩
instance : DefaultVal .i16 := ⟨.i16 0⟩
instance : DefaultVal .i32 := ⟨.i32 0⟩
instance : DefaultVal .i64 := ⟨.i64 0⟩
instance : DefaultVal .f32 := ⟨.f32 0⟩
instance : DefaultVal .f64 := ⟨.f64 0⟩
instance : DefaultVal .string := ⟨.string ""⟩
instance : DefaultVal .bytes := ⟨.bytes []⟩
-- the composites: each is the old table's arm, once (the inner
-- instance is REQUIRED for result/future/tensor — composition by
-- construction; the rest are inner-independent like the old arms)
instance {t : Ty} : DefaultVal (.option t) := ⟨.none⟩
instance {t : Ty} : DefaultVal (.list t) := ⟨.list .nil⟩
instance {k : KeyTy} {v : Ty} : DefaultVal (.map k v) := ⟨.map .nil⟩
instance {k : KeyTy} : DefaultVal (.set k) := ⟨.set .nil⟩
instance {t : Ty} : DefaultVal (.stream t) := ⟨.stream .nil⟩
instance {ok err : Ty} [DefaultVal ok] : DefaultVal (.result ok err) :=
  ⟨.ok (DefaultVal.default (t := ok))⟩
instance {t : Ty} [DefaultVal t] : DefaultVal (.future t) :=
  ⟨.future (DefaultVal.default (t := t))⟩
instance {t : Ty} {dims : List Nat} [DefaultVal t] :
    DefaultVal (.tensor dims t) :=
  ⟨.tensor (defaultTVal (DefaultVal.default (t := t)) dims)⟩

-- The composition pin: instance search composes through nested ctors
-- at elaboration time (a vacuous or mis-composed instance table fails
-- these kernel-checked rfl pins).
example : (DefaultVal.default (t := .option (.list .u64))) = .none := rfl
example : (DefaultVal.default (t := .result .u64 .bool)) = .ok (.u64 0) := rfl

-- The bridge: instance search cannot run on a VARIABLE `t` (the
-- fuel-0/tensor-fallback arms of `Gen.genVal` bind `t` as a pattern
-- variable), so the `CodecClosed` witness drives the lookup — each arm
-- re-fires the canonical instance on the refined ctor; the VALUES
-- live once, in the instances above. Total by construction: floats
-- have no `CodecClosed` case (the old `nomatch` arms) and `.ty` none.
def closedDefault : (t : Ty) → CodecClosed t → DefaultVal t
  | .bool, _ => inferInstanceAs (DefaultVal .bool)
  | .u8, _ => inferInstanceAs (DefaultVal .u8)
  | .u16, _ => inferInstanceAs (DefaultVal .u16)
  | .u32, _ => inferInstanceAs (DefaultVal .u32)
  | .u64, _ => inferInstanceAs (DefaultVal .u64)
  | .i8, _ => inferInstanceAs (DefaultVal .i8)
  | .i16, _ => inferInstanceAs (DefaultVal .i16)
  | .i32, _ => inferInstanceAs (DefaultVal .i32)
  | .i64, _ => inferInstanceAs (DefaultVal .i64)
  | .string, _ => inferInstanceAs (DefaultVal .string)
  | .bytes, _ => inferInstanceAs (DefaultVal .bytes)
  | .option t, .option _ => inferInstanceAs (DefaultVal (.option t))
  | .result ok _, .result hok _ => ⟨.ok (closedDefault ok hok).default⟩
  | .list t, .list _ => inferInstanceAs (DefaultVal (.list t))
  | .map k v, .map _ => inferInstanceAs (DefaultVal (.map k v))
  | .set k, .set => inferInstanceAs (DefaultVal (.set k))
  | .tensor dims t, .tensor h' =>
      ⟨.tensor (defaultTVal (closedDefault t h').default dims)⟩
  | .future t, .future h' => ⟨.future (closedDefault t h').default⟩
  | .stream t, .stream _ => inferInstanceAs (DefaultVal (.stream t))

-- (the generator/shrinker base case — the same signature, now the
-- bridge into the class; the tensor default FILLS the shape with the
-- element's default, via the tensor instance)
def defaultValue (t : Ty) (_h : CodecClosed t) : Value t :=
  (closedDefault t _h).default

-- the bridge pin: the old table's leaf values are the instances'
example : defaultValue .u8 CodecClosed.u8 = .u8 0 := rfl

end SchemaLang

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

import SchemaLang.Codec

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

mutual
def buildSlices? : (t : Ty) → (fuel : Nat) → (dims : List Nat) → (k : Nat) →
    List (Value t) → Option (List (TVal t dims) × List (Value t))
  | _, 0, _, _ + 1, _ => none
  | _, _, _, 0, vs => some ([], vs)
  | t, fuel + 1, dims, k + 1, vs => do
      let (x, r) ← buildOne? t fuel dims vs
      let (xs, r2) ← buildSlices? t fuel dims k r
      pure (x :: xs, r2)
  termination_by _ fuel dims k _ => (fuel, k, List.length dims)

def buildOne? : (t : Ty) → (fuel : Nat) → (dims : List Nat) →
    List (Value t) → Option (TVal t dims × List (Value t))
  | _, _, [], [v] => some (TVal.scalar v, [])
  | _, _, [], _ => none
  | _, 0, _ :: _, _ => none
  | t, fuel + 1, d :: ds, vs => do
      -- d inner slices of shape ds, off the front; the count-checked
      -- list → the length-indexed slice list
      let (inner, r) ← buildSlices? t fuel ds d vs
      let ss ← TSlices.ofCount? d inner
      some (TVal.dim ss, r)
  termination_by _ fuel dims _ => (fuel, 0, dims.length)
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
                else match buildOne? a (elems.length * (dims.length + 1) + 10) dims elems with
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
  | future {t : Ty} : CodecClosed t → CodecClosed (.future t)
  | stream {t : Ty} : CodecClosed t → CodecClosed (.stream t)

/-- The VList round trip over an element codec, append form (list arm). -/
theorem decode_encListVList_append (t : Ty)
    (ih : ∀ (v : Value t) (rest : List UInt8),
      decVal? t (encodeValue t v ++ rest) = some (v, rest))
    (vl : VList t) (rest : List UInt8) :
    decVal? (.list t)
        (Codec.encList (encodeValue t) (vListToList vl) ++ rest)
      = some (.list vl, rest) := by
  simp only [decVal?]
  rw [Codec.decList_encList_append (encodeValue t) (decVal? t) ih
    (vListToList vl) rest]
  simp [listToVList_vListToList]

/-- The VList round trip over an element codec, append form (stream arm —
    same wire shape, different `Value` constructor). -/
theorem decode_encStreamVList_append (t : Ty)
    (ih : ∀ (v : Value t) (rest : List UInt8),
      decVal? t (encodeValue t v ++ rest) = some (v, rest))
    (vl : VList t) (rest : List UInt8) :
    decVal? (.stream t)
        (Codec.encList (encodeValue t) (vListToList vl) ++ rest)
      = some (.stream vl, rest) := by
  simp only [decVal?]
  rw [Codec.decList_encList_append (encodeValue t) (decVal? t) ih
    (vListToList vl) rest]
  simp [listToVList_vListToList]

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

/-- The plain round trip: `decodeValue t (encodeValue t v) = some v`. -/
theorem decode_encodeValue (t : Ty) (v : Value t) (h : CodecClosed t) :
    decodeValue t (encodeValue t v) = some v := by
  simp only [decodeValue]
  have h2 := decode_encodeValue_append t h v []
  simp only [List.append_nil] at h2
  simp [h2]

/-- Sub-proof: a closed result's ok side is closed. -/
def resultOkClosed {ok err : Ty} (h : CodecClosed (.result ok err)) :
    CodecClosed ok :=
  match h with | .result hok _ => hok

/-- Sub-proof: a closed future's payload is closed. -/
def futureClosed {t : Ty} (h : CodecClosed (.future t)) : CodecClosed t :=
  match h with | .future h' => h'

/-- Sub-proof: a closed list's element type is closed. -/
def listClosed {t : Ty} (h : CodecClosed (.list t)) : CodecClosed t :=
  match h with | .list h' => h'

/-- Sub-proof: a closed stream's element type is closed. -/
def streamClosed {t : Ty} (h : CodecClosed (.stream t)) : CodecClosed t :=
  match h with | .stream h' => h'

/-- A default value for any codec-closed type — the generator/shrinker
    base case (structural recursion on the `CodecClosed` proof). -/
def defaultValue : (t : Ty) → CodecClosed t → Value t
  | .bool, _ => .bool false
  | .u8, _ => .u8 0
  | .u16, _ => .u16 0
  | .u32, _ => .u32 0
  | .u64, _ => .u64 0
  | .i8, _ => .i8 0
  | .i16, _ => .i16 0
  | .i32, _ => .i32 0
  | .i64, _ => .i64 0
  | .f32, h => nomatch h
  | .f64, h => nomatch h
  | .string, _ => .string ""
  | .bytes, _ => .bytes []
  | .option _, _ => .none
  | .result ok _, h => .ok (defaultValue ok (resultOkClosed h))
  | .list _, _ => .list .nil
  | .future t, h => .future (defaultValue t (futureClosed h))
  | .stream _, _ => .stream .nil

end SchemaLang

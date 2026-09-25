/-
# Vortex.Codecs — the array-level encodings, APPLIED (the real emission)

Owner: the Vortex agent (the mandate tree, `vortex/`).
Driving decisions: notes/design-vortex-encodings.md (the honest slice:
the SELECTED encodings applied to real column data — the layout drives
the emission; the full vortex FILE CONTAINER stays out — see the
boundary note at the bottom) + notes/v3/15-patterns.md #2 (THE
append-form codec law: `dec (enc xs ++ rest) = some (xs, rest)` —
codecs compose under bind BECAUSE the law is append-form) + #5 (the
mandatory negative control — every admissible-subdomain law pins its
OFF-domain loss in `VortexTests`) + #10 (the emitter spine stays
`Vortex.Emit`; these are the codec layer UNDER the plan).

THE SLICE JUDGMENT (the honest boundary, in full): the vortex file
format (github.com/spiraldb/vortex) is a deep stack — flatbuffers
metadata (Encodings message + array-spec trees), Arrow-IPC record-batch
framing, layouts (Flat/Chunked/Columnar), per-encoding message parsers,
the stats table. The FULL container is NOT this slice. What IS here:
the ARRAY level — each selected encoding as a real byte codec over a
fixture column's values, with the append-form law per encoding, the
round-trip theorem per encoding on its ADMISSIBLE SUBDOMAIN, and the
column-data emitter the layout drives (`encodeColumn`/`decodeColumn`
dispatching on the `EncodingSpec` the selection chose). The container
(framing, metadata, chunking, the flatbuffers face) lands with its
first consumer — the write path's named follow-up, per the leftover
rule.

THE BYTE DISCIPLINE: the packed payloads are LSB-first w-bit streams —
modeled as ONE stream natural (`packStream`: value `i` occupies bits
`[w*i, w*i + w)`), serialized little-endian (`bytesOfNat`/`readBytes?`).
This IS the bitpack discipline (the bit positions are real; a reader
packs the identical stream), proved at the arithmetic level — no
bit-list chunking, every law omega-tractable. The count/framing
prefixes ride `Kit.Varint` (the ONE LEB128, C0's shared atom).

THE DOMAIN HONESTY: a w-bit payload holds exactly the values below
`2^w`; the law states the round trip ON that admissible subdomain and
the tests PIN the off-domain loss (the seed's constant-encoding
discipline, extended to every width-bounded encoding — never a silent
truncation). `dict`'s law is UNCONDITIONAL (its width is computed from
its own dedup size); `identity`'s is the u64 range.

THE VALUE DOMAIN: this slice's columns are u64 columns — `List Nat`,
values below `2^64` (the boundary `Ty`'s fixed-width scalars). The
string/nested columns ride the `identity` fallback in the LAYOUT; their
DATA emission (the varint char wire et al.) is `SchemaCore.Codec`'s
proven lane and stays there — named exclusion, not an oversight.

Core-only (imports Kit + Kit.Correspondence + Kit.Varint +
SchemaCore.{Item,Codec} + LintKit.Basic — the cone rule; Vortex and
SchemaCore are both c1domain, lintkit's cone table; Correspondence is
the semantic dict codec's graded carrier, LintKit the nolint opt-out
attribute's reason-string form — core-only, any package may import it).
-/

import Kit
import Kit.Correspondence
import Kit.Varint
import SchemaCore.Item
import SchemaCore.Codec
import LintKit.Basic
import Vortex.Encoding

open Kit Varint SchemaCore

namespace Vortex

/-! ## The little-endian byte layer (the stream natural's serialization) -/

/-- Read `b` little-endian bytes off the front, MSB-last: the FIRST byte
    is the LOW byte. Truncation refuses (`none`), never a silent short
    read. -/
def readBytes? : (b : Nat) → List UInt8 → Option (Nat × List UInt8)
  | 0, bs => some (0, bs)
  | b + 1, bs =>
      match bs with
      | [] => none
      | byte :: r => (readBytes? b r).map fun (s, r') => (byte.toNat + 256 * s, r')

/-- The little-endian serialization: the LOW `b` bytes of `s`, first
    byte lowest. -/
def bytesOfNat : (b : Nat) → Nat → List UInt8
  | 0, _ => []
  | b + 1, s => (s % 256).toUInt8 :: bytesOfNat b (s / 256)

/-- PATTERN #2 — the byte layer's append-form law: `b` bytes read back
    exactly the `b`-byte serialization plus any suffix, when the value
    fits (no information above the boundary). -/
theorem readBytes?_bytesOfNat_append : ∀ (b s : Nat) (rest : List UInt8),
    s < 256 ^ b → readBytes? b (bytesOfNat b s ++ rest) = some (s, rest) := by
  intro b
  induction b with
  | zero =>
      intro s rest h
      have hs : s = 0 := by omega
      subst hs
      simp [readBytes?, bytesOfNat]
  | succ k ih =>
      intro s rest h
      have hsize : UInt8.size = 256 := rfl
      have hbyte : (s % 256).toUInt8.toNat = s % 256 :=
        UInt8.toNat_ofNat_of_lt' (by rw [hsize]; omega)
      simp only [readBytes?, bytesOfNat, List.cons_append, hbyte]
      rw [ih (s / 256) rest (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      have hval : s % 256 + 256 * (s / 256) = s := by omega
      rw [hval]

/-- The byte base as a power of two (the two faces of one boundary). -/
theorem pow256 (b : Nat) : 256 ^ b = 2 ^ (8 * b) := by
  induction b with
  | zero => rfl
  | succ k ih =>
      calc 256 ^ (k + 1) = 256 ^ k * 256 := by rw [Nat.pow_succ]
        _ = 2 ^ (8 * k) * 2 ^ 8 := by rw [ih]
        _ = 2 ^ (8 * k + 8) := (Nat.pow_add 2 (8 * k) 8).symm

/-! ## The bit-stream layer (the w-bit packing's value face) -/

/-- THE PACKED STREAM: value `i` of `xs` occupies bits
    `[w*i, w*i + w)` — LSB-first w-bit packing, as one natural. -/
def packStream (w : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => v + 2 ^ w * packStream w vs

/-- Unpack `n` values off the stream's low end. -/
def unpackStream (w : Nat) : (n : Nat) → Nat → List Nat
  | 0, _ => []
  | n + 1, s => s % 2 ^ w :: unpackStream w n (s / 2 ^ w)

/-- Packing is bounded: `w` bits per element (the `+ 1` shape keeps
    every step linear — no product-of-atoms arithmetic). -/
theorem packStream_le (w : Nat) (xs : List Nat) (h : ∀ v ∈ xs, v < 2 ^ w) :
    packStream w xs + 1 ≤ 2 ^ (w * xs.length) := by
  induction xs with
  | nil => simp [packStream, Nat.mul_zero, Nat.pow_zero]
  | cons v vs ih =>
      have hv : v + 1 ≤ 2 ^ w := by have := h v (by simp); omega
      have hS : packStream w vs + 1 ≤ 2 ^ (w * vs.length) :=
        ih (fun u hu => h u (by simp [hu]))
      have hsplit : 2 ^ (w * (vs.length + 1))
          = 2 ^ w * 2 ^ (w * vs.length) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
      calc packStream w (v :: vs) + 1
          = v + 2 ^ w * packStream w vs + 1 := rfl
        _ = v + 1 + 2 ^ w * packStream w vs := by
            rw [Nat.add_assoc, Nat.add_comm (2 ^ w * packStream w vs) 1,
              ← Nat.add_assoc]
        _ ≤ 2 ^ w + 2 ^ w * packStream w vs :=
            Nat.add_le_add_right hv (2 ^ w * packStream w vs)
        _ = 2 ^ w * (packStream w vs + 1) := by
            rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ 2 ^ w * 2 ^ (w * vs.length) := Nat.mul_le_mul_left _ hS
        _ = 2 ^ (w * (vs.length + 1)) := hsplit.symm

/-- Packing is bounded: `w` bits per element. -/
theorem packStream_lt (w : Nat) (xs : List Nat) (h : ∀ v ∈ xs, v < 2 ^ w) :
    packStream w xs < 2 ^ (w * xs.length) := by
  have := packStream_le w xs h
  omega

/-- Unpacking undoes packing — ON THE ADMISSIBLE SUBDOMAIN (every value
    below `2^w`). This is the bitpack discipline's semantic core. -/
theorem unpackStream_packStream (w : Nat) (xs : List Nat) (h : ∀ v ∈ xs, v < 2 ^ w) :
    unpackStream w xs.length (packStream w xs) = xs := by
  induction xs with
  | nil => simp [unpackStream]
  | cons v vs ih =>
      have hv : v < 2 ^ w := h v (by simp)
      have hs : ∀ u ∈ vs, u < 2 ^ w := fun u hu => h u (by simp [hu])
      have hlow : packStream w (v :: vs) % 2 ^ w = v := by
        simp only [packStream, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
      have hshift : packStream w (v :: vs) / 2 ^ w = packStream w vs := by
        simp only [packStream]
        rw [Nat.add_mul_div_left v (packStream w vs)
          (show 0 < 2 ^ w from Nat.pow_pos (by omega)),
          Nat.div_eq_of_lt hv, Nat.zero_add]
      simp only [unpackStream, List.length_cons, hlow, hshift]
      simp [ih hs]

/-! ## The foldl-min helper (the FoR base's min-ness) -/

/-- `foldl min` never rises above its start. -/
theorem foldlMin_le_acc : ∀ (us : List Nat) (acc : Nat), us.foldl min acc ≤ acc
  | [], _ => Nat.le_refl _
  | x :: us, acc =>
      Nat.le_trans (foldlMin_le_acc us (min acc x)) (Nat.min_le_left acc x)

/-- `foldl min` never rises above any element it folds over. -/
theorem foldlMin_le : ∀ (us : List Nat) (acc v : Nat), v ∈ us → us.foldl min acc ≤ v
  | [], _, _, hv => absurd hv (by simp)
  | x :: us, acc, v, hv => by
      rcases List.mem_cons.mp hv with hve | hin
      · rw [hve]
        exact Nat.le_trans (foldlMin_le_acc us (min acc x))
          (Nat.min_le_right acc x)
      · exact foldlMin_le us (min acc x) v hin

/-- A column's minimum (the FoR base; the empty column's base is 0). -/
def colMin : List Nat → Nat
  | [] => 0
  | v :: vs => vs.foldl min v

/-- The column's minimum is a min: `≤` every element. -/
theorem colMin_le (xs : List Nat) : ∀ v ∈ xs, colMin xs ≤ v := by
  intro v hv
  cases xs with
  | nil => exact absurd hv (by simp)
  | cons u us =>
      rcases List.mem_cons.mp hv with hve | hin
      · rw [hve]; exact foldlMin_le_acc us u
      · exact foldlMin_le us u v hin

/-! ## The bitPacked column codec (the layout's fixed-width row) -/

/-- The byte count that holds `bits` bits (the final byte zero-padded). -/
def padBytes (bits : Nat) : Nat := (bits + 7) / 8

/-- THE bitPacked column codec: the row count, then the LSB-first
    w-bit stream's bytes. The width is the LAYOUT's `w` — the selection
    fixed it from the static facts (the layout drives the emission). -/
def encBitPacked (w : Nat) (xs : List Nat) : List UInt8 :=
  encVarNat xs.length
    ++ bytesOfNat (padBytes (w * xs.length)) (packStream w xs)

/-- The bitPacked decoder: the count, the padded stream bytes, the
    values. Truncation refuses at either layer (varint, bytes). -/
def decBitPacked? (w : Nat) (bs : List UInt8) : Option (List Nat × List UInt8) :=
  match decVarNat? bs with
  | some (n, r) =>
      (readBytes? (padBytes (w * n)) r).map fun (s, r') =>
        (unpackStream w n s, r')
  | none => none

/-- The packed stream fits its padded byte count (the boundary's
    `bits ≤ 8 · bytes` face). -/
theorem packStream_fits (bits : Nat) (s : Nat) (h : s < 2 ^ bits) :
    s < 256 ^ padBytes bits := by
  rw [pow256]
  have hd := Nat.div_add_mod (bits + 7) 8
  have hle : bits ≤ 8 * ((bits + 7) / 8) := by omega
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_of_le (by omega) hle)

/-- PATTERN #2 — the bitPacked codec's append-form law, on the
    admissible subdomain (every value below `2^w`). -/
theorem decBitPacked?_encBitPacked_append (w : Nat) (xs : List Nat)
    (h : ∀ v ∈ xs, v < 2 ^ w) (rest : List UInt8) :
    decBitPacked? w (encBitPacked w xs ++ rest) = some (xs, rest) := by
  simp only [encBitPacked, List.append_assoc, decBitPacked?,
    decVarNat?_encVarNat_append,
    readBytes?_bytesOfNat_append (padBytes (w * xs.length)) (packStream w xs) rest
      (packStream_fits (w * xs.length) _ (packStream_lt w xs h)),
    Option.map_some, Option.some.injEq]
  simp [unpackStream_packStream w xs h]

/-! ## The foR column codec (base + offsets, the design's FoR row) -/

/-- THE foR column codec: the base (the column's min — offsets are then
    nonnegative), then the offsets' w-bit stream. -/
def encFoR (w : Nat) (xs : List Nat) : List UInt8 :=
  encVarNat (colMin xs)
    ++ encBitPacked w (xs.map (fun v => v - colMin xs))

/-- The foR decoder: the base, then the offsets; values re-add the
    base. -/
def decFoR? (w : Nat) (bs : List UInt8) : Option (List Nat × List UInt8) :=
  match decVarNat? bs with
  | some (base, r) =>
      (decBitPacked? w r).map fun (offsets, r') =>
        (offsets.map (fun o => o + base), r')
  | none => none

/-- The offsets' re-add face — general over the base: base + offset
    recovers the value when the base is ≤ every element. -/
theorem map_add_base (base : Nat) :
    ∀ (xs : List Nat), (∀ v ∈ xs, base ≤ v) →
      (xs.map (fun v => v - base)).map (fun o => o + base) = xs := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons u us ih =>
      intro hle
      have hb : base ≤ u := hle u (by simp)
      have hhead : u - base + base = u := by omega
      simp only [List.map_cons, hhead]
      rw [ih (fun v hv => hle v (by simp [hv]))]

/-- The offsets' re-add face at the column's own base. -/
theorem map_add_colMin (xs : List Nat) :
    (xs.map (fun v => v - colMin xs)).map (fun o => o + colMin xs) = xs :=
  map_add_base (colMin xs) xs (colMin_le xs)

/-- PATTERN #2 — the foR codec's append-form law, on the admissible
    subdomain: every offset from the min fits the layout's `w` bits
    (the column's RANGE fits — the selection's small-int-range row). -/
theorem decFoR?_encFoR_append (w : Nat) (xs : List Nat)
    (h : ∀ v ∈ xs, v - colMin xs < 2 ^ w) (rest : List UInt8) :
    decFoR? w (encFoR w xs ++ rest) = some (xs, rest) := by
  have hoff : ∀ v ∈ xs.map (fun v => v - colMin xs), v < 2 ^ w := by
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨v', hv'x, rfl⟩ := hv
    exact h v' hv'x
  simp only [encFoR, List.append_assoc, decFoR?, decVarNat?_encVarNat_append,
    decBitPacked?_encBitPacked_append w (xs.map (fun v => v - colMin xs)) hoff rest,
    Option.map_some, Option.some.injEq]
  simp [map_add_colMin xs]

/-! ## The u64 value atom (the dictionary's value lane + identity's row) -/

/-- One u64 value: its varint (the atom every non-packed lane shares). -/
def encU64 (v : Nat) : List UInt8 := encVarNat v

/-- The u64 atom's decode: the varint, range-checked (a value at/over
    `2^64` refuses — never a silent wrap). -/
def decU64? (bs : List UInt8) : Option (Nat × List UInt8) :=
  match decVarNat? bs with
  | some (n, r) => if n < 2 ^ 64 then some (n, r) else none
  | none => none

/-- PATTERN #2 — the u64 atom's append-form law (on the u64 range). -/
theorem decU64?_encU64_append (v : Nat) (hv : v < 2 ^ 64) (rest : List UInt8) :
    decU64? (encU64 v ++ rest) = some (v, rest) := by
  simp only [encU64, decU64?, decVarNat?_encVarNat_append, hv]
  simp


/-! ## The dict column codec (values + codes, the design's Dict row) -/

/-- The dictionary's UNIQUE values (a deterministic dedup: a head whose
    value recurs is dropped — the value's LAST occurrence's position is
    its code; order is an implementation detail, the uniqueness is the
    content). -/
def dedupVals : List Nat → List Nat
  | [] => []
  | v :: vs => if v ∈ vs then dedupVals vs else v :: dedupVals vs

/-- Dedup keeps every value: membership survives. -/
theorem mem_dedupVals : ∀ (xs : List Nat) (x : Nat), x ∈ xs → x ∈ dedupVals xs := by
  intro xs
  induction xs with
  | nil => intro x hv; cases hv
  | cons u us ih =>
      intro x hv
      rcases List.mem_cons.mp hv with hxe | hin
      · rw [hxe]
        simp only [dedupVals]
        by_cases hxu : u ∈ us
        · rw [if_pos hxu]; exact ih u hxu
        · rw [if_neg hxu]; exact List.mem_cons_self
      · simp only [dedupVals]
        by_cases hxu : u ∈ us
        · rw [if_pos hxu]
          exact ih x hin
        · rw [if_neg hxu]
          rcases List.mem_cons.mp (List.mem_cons_of_mem u hin) with hxe2 | hxin
          · rw [hxe2]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih x hxin)

/-- A value's position in a list (`none` = absent; `some i` = the first
    occurrence's index). -/
def codeOf? (v : Nat) : List Nat → Option Nat
  | [] => none
  | u :: us => if u == v then some 0 else (codeOf? v us).map (fun i => i + 1)

/-- The value at index `i` of a list. -/
def valueAt? : (i : Nat) → List Nat → Option Nat
  | _, [] => none
  | 0, v :: _ => some v
  | i + 1, _ :: vs => valueAt? i vs

/-- A lookup's index lands on the value — for every PRESENT value
    (the dictionary's own correctness core). -/
theorem codeOf?_find : ∀ (vs : List Nat) (v : Nat), v ∈ vs →
    ∃ i, codeOf? v vs = some i ∧ valueAt? i vs = some v := by
  intro vs
  induction vs with
  | nil => intro v hv; cases hv
  | cons u us ih =>
      intro v hv
      rcases List.mem_cons.mp hv with hve | hin
      · rw [hve]
        exact ⟨0, by simp [codeOf?], by simp [valueAt?]⟩
      · simp only [codeOf?]
        by_cases huv : (u == v) = true
        · have hueq : u = v := beq_iff_eq.mp huv
          rw [hueq]
          simp only [beq_self_eq_true]
          exact ⟨0, rfl, rfl⟩
        · simp only [huv]
          obtain ⟨i, hi, hvat⟩ := ih v hin
          refine ⟨i + 1, ?_, ?_⟩
          · rw [hi]; simp
          · simp only [valueAt?]
            exact hvat

/-- An index that lands is in bounds (the codes' width face). -/
theorem valueAt?_bound : ∀ (vs : List Nat) (i : Nat), valueAt? i vs ≠ none →
    i < vs.length := by
  intro vs
  induction vs with
  | nil =>
      intro i hne
      exact absurd (by simp [valueAt?]) hne
  | cons u us ih =>
      intro i hi
      cases i with
      | zero => simp
      | succ i' =>
          simp only [valueAt?] at hi
          have h' := ih i' hi
          simp only [List.length_cons]
          omega

/-- The u64 range survives dedup (dedup only holds values of xs). -/
theorem dedupVals_lt (xs : List Nat) (h : ∀ v ∈ xs, v < 2 ^ 64) :
    ∀ v ∈ dedupVals xs, v < 2 ^ 64 := by
  have hmem : ∀ v ∈ dedupVals xs, v ∈ xs := by
    intro v hv
    revert hv
    induction xs with
    | nil => intro hv; cases hv
    | cons u us ih =>
        intro hv
        simp only [dedupVals] at hv
        by_cases hxu : u ∈ us
        · rw [if_pos hxu] at hv
          exact List.mem_cons_of_mem u
            (ih (fun w hw => h w (List.mem_cons_of_mem _ hw)) hv)
        · rw [if_neg hxu] at hv
          rcases List.mem_cons.mp hv with hve | hv
          · rw [hve]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem u
              (ih (fun w hw => h w (List.mem_cons_of_mem _ hw)) hv)
  exact fun v hv => h v (hmem v hv)

/-- Each row's dict code: its value's first-occurrence index. -/
def dictCodes (xs : List Nat) : List Nat :=
  xs.map (fun x => (codeOf? x (dedupVals xs)).getD 0)

/-- A dict column's SEMANTIC stored form: the dictionary's values + the
    rows' codes (the byte codec below carries the same shape over real
    bytes; this is the retention face). -/
structure DictData where
  vals : List Nat
  codes : List Nat

/-- Encode: the deduped values + each row's first-occurrence code. -/
def dictEncode (xs : List Nat) : DictData :=
  ⟨dedupVals xs, dictCodes xs⟩

/-- Readback: each code re-indexes the dictionary (the byte decoder's
    join; a malformed code reads as row 0's value — the law's path
    never rides it, `codeOf?_find` pins every code on it). -/
def dictDecode (d : DictData) : List Nat :=
  d.codes.map (fun c => (valueAt? c d.vals).getD 0)

/-- THE dict semantic law — UNCONDITIONAL: the dict round-trips EVERY
    column, no premise at all (the width is the dedup size's own, and
    the semantic level has no bytes to bound — the byte law's `2^64`
    premise is the u64 ATOMS' range check, not the dict's). The factored
    core the byte law and `dictCodec` both cite. -/
theorem dictDecode_dictEncode (xs : List Nat) :
    dictDecode (dictEncode xs) = xs := by
  unfold dictDecode dictEncode dictCodes
  have key : ∀ x ∈ xs,
      (valueAt? ((codeOf? x (dedupVals xs)).getD 0) (dedupVals xs)).getD 0 = x := by
    intro x hx
    obtain ⟨i, hi, hvat⟩ := codeOf?_find (dedupVals xs) x (mem_dedupVals xs x hx)
    simp [hi, hvat]
  rw [List.map_map,
    List.map_congr_left (fun c hc => by simpa using key c hc)]
  simp

/-- THE dict column codec: the dedup size, the unique values (varints),
    then the row codes as a bitPacked stream at the DEDUP SIZE's width —
    the width computed from the encoding's own data, so the value
    retention is unconditional. -/
def encDict (xs : List Nat) : List UInt8 :=
  encVarNat (dedupVals xs).length
    ++ List.flatten ((dedupVals xs).map encU64)
    ++ encBitPacked (bitsFor (some (dedupVals xs).length)) (dictCodes xs)

/-- The dict decoder: the dedup size, the values, the codes; rows
    re-index the values. -/
def decDict? (bs : List UInt8) : Option (List Nat × List UInt8) :=
  match decVarNat? bs with
  | some (k, r) =>
      match decManyBind? decU64? k r with
      | some (vals, r') =>
          (decBitPacked? (bitsFor (some k)) r').map fun (codes, r'') =>
            (codes.map (fun c => (valueAt? c vals).getD 0), r'')
      | none => none
  | none => none

/-- The many-elements law's DOMAIN-RESTRICTED variant: the element law
    is needed only on members (the induction peels heads). -/
theorem decManyBind?_enc_append_dom
    (dec : List UInt8 → Option (Nat × List UInt8)) (enc : Nat → List UInt8)
    (as : List Nat)
    (h : ∀ (a : Nat) (rest : List UInt8), a ∈ as →
      dec (enc a ++ rest) = some (a, rest))
    (rest : List UInt8) :
    decManyBind? dec as.length ((as.map enc).flatten ++ rest) = some (as, rest) := by
  revert h
  induction as generalizing rest with
  | nil => intro h; simp [decManyBind?]
  | cons a as ih =>
      intro h
      simp only [decManyBind?, List.length_cons, List.map_cons,
        List.flatten_cons, List.append_assoc]
      rw [h a ((as.map enc).flatten ++ rest) (by simp)]
      simp [ih rest (fun a' r ha' => h a' r (by simp [ha']))]

/-- The dict's code width covers every code: `k ≤ 2 ^ bitsFor (some k)`. -/
theorem dict_width_cover (k : Nat) : k ≤ 2 ^ bitsFor (some k) := by
  simp only [bitsFor]
  by_cases hk : k = 0
  · rw [hk]; simp
  · have h : (k : Nat) ≠ 0 := by omega
    exact Nat.le_of_lt (Iff.mp (Nat.log2_lt h) (Nat.lt_succ_self (Nat.log2 k)))

/-- PATTERN #2 — the dict codec's append-form law: UNCONDITIONAL on the
    u64 range (the width is the dedup size's own, so every code fits). -/
theorem decDict?_encDict_append (xs : List Nat)
    (h : ∀ v ∈ xs, v < 2 ^ 64) (rest : List UInt8) :
    decDict? (encDict xs ++ rest) = some (xs, rest) := by
  have hvals : ∀ v ∈ dedupVals xs, v < 2 ^ 64 := dedupVals_lt xs h
  have hcodes : ∀ c ∈ dictCodes xs,
      c < 2 ^ bitsFor (some (dedupVals xs).length) := by
    intro c hc
    simp only [dictCodes, List.mem_map] at hc
    obtain ⟨x, hx, hcx⟩ := hc
    obtain ⟨i, hi, hvat⟩ := codeOf?_find (dedupVals xs) x (mem_dedupVals xs x hx)
    have hibound := valueAt?_bound (dedupVals xs) i (by simp [hvat])
    have hk := dict_width_cover (dedupVals xs).length
    rw [hi] at hcx
    simp only [Option.getD_some] at hcx
    omega
  have hmap : (dictCodes xs).map (fun c => (valueAt? c (dedupVals xs)).getD 0) = xs :=
    dictDecode_dictEncode xs
  simp only [encDict, List.append_assoc, decDict?, decVarNat?_encVarNat_append]
  simp [decManyBind?_enc_append_dom decU64? encU64 (dedupVals xs)
    (fun a r ha => decU64?_encU64_append a (hvals a ha) r),
    decBitPacked?_encBitPacked_append (bitsFor (some (dedupVals xs).length))
      (dictCodes xs) hcodes rest,
    hmap]

/-- The dict semantic codec: the retention law rides the graded carrier
    (PATTERN #18 at the semantic grade — the `forCodec` precedent in
    `Vortex.Encoding`; the byte layer's `decDict?_encDict_append` is the
    canonical instance). `policy` is `True`: the law is UNCONDITIONAL —
    the width is the dedup size's own, every datum is accepted. -/
@[nolint linter.guestlang.graduation "the image iso is NOT free here: `DictData`'s decode is not injective (the dictionary's values are stored verbatim — `⟨vals := [1, 1], codes := [0, 0]⟩` and `⟨vals := [1], codes := [0, 0]⟩` decode alike), so the `toIsoOfExact` upgrade needs the canonical-form discipline (vals deduped) on the data side; the LAW's unconditionality does not reach decode injectivity, and the byte layer's `decDict?_encDict_append` is the canonical law"]
def dictCodec : Kit.Codec DictData (List Nat) where
  encode := dictEncode
  decode d := some (dictDecode d)
  policy _ := True
  decode_encode xs := by
    show some (dictDecode (dictEncode xs)) = some xs
    rw [dictDecode_dictEncode xs]
  decode_some_policy _ _ _ := trivial

/-- Dict RETENTION: decode ∘ encode = id — the encoding holds the
    column's values UNCONDITIONALLY (the design's dict law). The
    CITATION of `dictCodec`'s law field (the `forRead_forEncode`
    precedent), not a second proof. -/
theorem dictRetention : ∀ (xs : List Nat), dictDecode (dictEncode xs) = xs :=
  fun xs => Option.some.inj (Kit.Codec.decode_encode dictCodec xs)

/-! ## The constant column codec (one value + a count) -/

/-- THE constant column codec: the shared value, then the row count. -/
def encConst (xs : List Nat) : List UInt8 :=
  encU64 (xs.headD 0) ++ encVarNat xs.length

/-- The constant decoder's rows: value, replicated by counting (the
    cons-form recursion the law's induction rides). -/
def constVals (v : Nat) : (n : Nat) → List Nat
  | 0 => []
  | n + 1 => v :: constVals v n

/-- The constant decoder: the value, the count; rows replicate. -/
def decConst? (bs : List UInt8) : Option (List Nat × List UInt8) :=
  match decU64? bs with
  | some (v, r) =>
      match decVarNat? r with
      | some (n, r') => some (constVals v n, r')
      | none => none
  | none => none

theorem headD_cons' (a : Nat) (l : List Nat) (d : Nat) : (a :: l).headD d = a := rfl

/-- PATTERN #2 — the constant codec's append-form law, on the admissible
    subdomain: every row holds the SAME value (a cardinality-1 column —
    the selection's is-constant row). -/
theorem decConst?_encConst_append (v : Nat) (hv64 : v < 2 ^ 64) (vs : List Nat)
    (h : vs.all (fun w => w == v) = true) (rest : List UInt8) :
    decConst? (encConst (v :: vs) ++ rest) = some (v :: vs, rest) := by
  have hrep : constVals v (vs.length + 1) = v :: vs := by
    induction vs with
    | nil => simp [constVals]
    | cons w ws ih =>
        have hw := List.all_eq_true.mp h w (by simp)
        have hws : ws.all (fun u => u == v) = true :=
          List.all_eq_true.mpr (fun x hx => List.all_eq_true.mp h x (by simp [hx]))
        have hweq : w = v := beq_iff_eq.mp hw
        rw [hweq]
        have h1 : constVals v (ws.length + 1) = v :: ws := ih hws
        show v :: constVals v (ws.length + 1) = v :: v :: ws
        rw [h1]
  simp only [encConst, List.append_assoc, decConst?, headD_cons',
    List.length_cons, decU64?_encU64_append v hv64, decVarNat?_encVarNat_append]
  simp [hrep]

/-- The empty column's constant face (count 0, no shared value). -/
theorem decConst?_encConst_nil (rest : List UInt8) :
    decConst? (encConst [] ++ rest) = some ([], rest) := by
  have h0 : (0 : Nat) < 2 ^ 64 := Nat.pow_pos (by omega)
  simp [encConst, decConst?, decU64?_encU64_append 0 h0,
    decVarNat?_encVarNat_append 0 rest, constVals]

/-! ## The sequence column codec (start + step + count) -/

/-- A data column's step: the second value minus the first. -/
def seqStep (xs : List Nat) : Int :=
  Int.ofNat (xs.getD 1 0) - xs.headD 0

/-- The progression's rows: `start + i·step`, clamped at the u64 floor
    (the clamp is off the admissible subdomain — the tests pin it). -/
def seqVals (start : Int) (step : Int) : (n : Nat) → List Nat
  | 0 => []
  | n + 1 => start.toNat :: seqVals (start + step) step n

/-- THE sequence column codec, canonical form: the start and the
    zigzagged step, then the count. -/
def encSeq (start : Int) (step : Int) (n : Nat) : List UInt8 :=
  encVarNat (zigzag start) ++ encVarNat (zigzag step) ++ encVarNat n

/-- The data-level sequence encode: start = head, step = second − first,
    count = length. Off a progression this LOSES (pinned in tests) —
    the declared-sorted+fixed-step fact is what makes the row honest. -/
def encSeqData (xs : List Nat) : List UInt8 :=
  encSeq (xs.headD 0) (seqStep xs) xs.length

/-- The sequence decoder: start, step, count; rows regenerate. -/
def decSeq? (bs : List UInt8) : Option (List Nat × List UInt8) :=
  match decVarNat? bs with
  | some (s0, r) =>
      match decVarNat? r with
      | some (z, r') =>
          match decVarNat? r' with
          | some (n, r'') => some (seqVals (unzigzag s0) (unzigzag z) n, r'')
          | none => none
      | none => none
  | none => none

/-- PATTERN #2 — the sequence codec's append-form law: UNCONDITIONAL on
    the canonical form (the loss lives in the data-level guess, above). -/
theorem decSeq?_encSeq_append (s st : Int) (n : Nat) (rest : List UInt8) :
    decSeq? (encSeq s st n ++ rest) = some (seqVals s st n, rest) := by
  simp only [encSeq, List.append_assoc, decSeq?, decVarNat?_encVarNat_append,
    unzigzag_zigzag]

/-- The data-level sequence law, on its admissible subdomain: the data
    IS the progression its own head/step generate. -/
theorem decSeq?_encSeqData_append (xs : List Nat)
    (h : seqVals (xs.headD 0) (seqStep xs) xs.length == xs) (rest : List UInt8) :
    decSeq? (encSeqData xs ++ rest) = some (xs, rest) := by
  simp only [encSeqData]
  rw [decSeq?_encSeq_append, beq_iff_eq.mp h]

/-! ## The identity row (the universal fallback's data lane) -/

/-- THE identity column codec: the count, then each value's varint. -/
def encIdentity (xs : List Nat) : List UInt8 :=
  encVarNat xs.length ++ List.flatten (xs.map encU64)

/-- The identity decoder: the count, then the values. -/
def decIdentity? (bs : List UInt8) : Option (List Nat × List UInt8) :=
  match decVarNat? bs with
  | some (n, r) => decManyBind? decU64? n r
  | none => none

/-- PATTERN #2 — the identity codec's append-form law (on the u64
    range — the wire is the u64 column's). -/
theorem decIdentity?_encIdentity_append (xs : List Nat)
    (h : ∀ v ∈ xs, v < 2 ^ 64) (rest : List UInt8) :
    decIdentity? (encIdentity xs ++ rest) = some (xs, rest) := by
  simp only [encIdentity, List.append_assoc, decIdentity?, decVarNat?_encVarNat_append]
  rw [decManyBind?_enc_append_dom decU64? encU64 xs
    (fun a r ha => decU64?_encU64_append a (h a ha) r) rest]

/-! ## The sparse column codec (bitmap + the CHILD encoding's patches —
    the nesting face) -/

/-- The sparse mask: 1-bit per row, 0 where the row holds the default
    (flatland §E2's dense-bitmap face — never a probe structure). -/
def sparseMask (d : Nat) : List Nat → List Nat
  | [] => []
  | v :: vs => (if v == d then 0 else 1) :: sparseMask d vs

/-- The patch values: the rows OFF the default, in row order. THE
    CHILD'S PAYLOAD — these bytes are the child encoding's column, the
    recursive discipline (flatland §E6: every child independently
    compressible). -/
def sparsePatches (d : Nat) : List Nat → List Nat
  | [] => []
  | v :: vs => if v == d then sparsePatches d vs else v :: sparsePatches d vs

/-- The readback join: the mask drives the rows — 0 emits the default,
    1 consumes the next patch value (the §E2 merge: `blend(mask, patch,
    default)`, branchless in the host). Malformed wires (a short mask,
    a missing patch value) read as the default fill — the dict
    decoder's `valueAt?.getD 0` honesty, the law's path never rides it.
    The wire's row count is FRAMING (the host sizes the column from it);
    the join is driven by the mask, whose length IS the count on the
    law's path (the 1-bit stream decodes exactly `n` bits). -/
def sparseJoin (d : Nat) : List Nat → List Nat → List Nat
  | [], _ => []
  | 0 :: bs, vs => d :: sparseJoin d bs vs
  | _ :: bs, vs =>
      match vs with
      | [] => []
      | v :: vs' => v :: sparseJoin d bs vs'

/-- THE reconstruction law — the sparse semantic core: the mask + the
    patches rebuild the column exactly. -/
theorem sparseJoin_mask_patches (d : Nat) :
    ∀ (xs : List Nat),
      sparseJoin d (sparseMask d xs) (sparsePatches d xs) = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons v vs ih =>
      simp only [sparseMask, sparsePatches]
      by_cases hvd : (v == d) = true
      · have hvdeq : v = d := beq_iff_eq.mp hvd
        subst hvdeq
        simp [sparseJoin, ih]
      · simp only [if_neg hvd]
        simp [sparseJoin, ih]

/-- The mask's bits are in the 1-bit domain (0/1). -/
theorem sparseMask_dom (d : Nat) (xs : List Nat) :
    ∀ b ∈ sparseMask d xs, b < 2 := by
  induction xs with
  | nil => intro b hb; simp [sparseMask] at hb
  | cons u us ih =>
      intro b hb
      simp only [sparseMask, List.mem_cons] at hb
      rcases hb with hb | hb
      · simp only [hb]
        split <;> simp
      · exact ih b hb

/-! ## THE DISPATCH — the layout drives the emission (the design's
    wire contract: the selected encoding's bytes, layer for layer) -/

/-- The data an encoding admits (the round-trip law's domain, per
    encoding — decidable, and checked at the emission boundary). -/
def inDomain : EncodingSpec → List Nat → Bool
  | .identity, xs => xs.all (fun v => v < 2 ^ 64)
  | .bitPacked w, xs => xs.all (fun v => v < 2 ^ w)
  | .foR w, xs => xs.all (fun v => v - colMin xs < 2 ^ w)
  | .dict, xs => xs.all (fun v => v < 2 ^ 64)
  | .sequence, xs => seqVals (xs.headD 0) (seqStep xs) xs.length == xs
  | .constant, xs => xs.all (fun v => v < 2 ^ 64 && v == xs.headD 0)
  | .sparse child, xs =>
      xs.all (fun v => v < 2 ^ 64)
        && inDomain child (sparsePatches (xs.headD 0) xs)

/-- THE column encoder: the selected encoding's payload. The sparse arm
    is the NESTING FACE: the count, the default, the 1-bit mask, then
    the patches THROUGH THE CHILD CODEC — the recursion is structural
    on the spec (the child encoding's buffer is the payload, flatland
    §E6's every-child-independently-compressible). -/
def encodeColumn (e : EncodingSpec) (xs : List Nat) : List UInt8 :=
  match e with
  | .identity => encIdentity xs
  | .bitPacked w => encBitPacked w xs
  | .foR w => encFoR w xs
  | .dict => encDict xs
  | .sequence => encSeqData xs
  | .constant => encConst xs
  | .sparse child =>
      let d := xs.headD 0
      encVarNat xs.length ++ encU64 d
        ++ encBitPacked 1 (sparseMask d xs)
        ++ encodeColumn child (sparsePatches d xs)

/-- THE column decoder: the encoding's inverse. The sparse arm peels
    count/default/mask, then recurses into the child. -/
def decodeColumn (e : EncodingSpec) (bs : List UInt8) :
    Option (List Nat × List UInt8) :=
  match e with
  | .identity => decIdentity? bs
  | .bitPacked w => decBitPacked? w bs
  | .foR w => decFoR? w bs
  | .dict => decDict? bs
  | .sequence => decSeq? bs
  | .constant => decConst? bs
  | .sparse child =>
      (decVarNat? bs).bind fun (_count, r) =>
        (decU64? r).bind fun (d, r') =>
          (decBitPacked? 1 r').bind fun (bits, r'') =>
            (decodeColumn child r'').map fun (vals, r''') =>
              (sparseJoin d bits vals, r''')

/-- The empty column is in EVERY encoding's domain (the all-faces of
    `[]` hold; the sequence row regenerates the empty progression). -/
theorem inDomain_nil (e : EncodingSpec) : inDomain e [] = true := by
  induction e with
  | identity => rfl
  | bitPacked _ => rfl
  | foR _ => rfl
  | dict => rfl
  | sequence => rfl
  | constant => rfl
  | sparse child ih => simp [inDomain, sparsePatches, ih]

/-- The all-equal extraction (the constant arm's domain face). -/
theorem allEq_mp {xs : List Nat} {v : Nat}
    (h : xs.all (fun w => w == v) = true) : ∀ w ∈ xs, w = v :=
  fun w hw => beq_iff_eq.mp (List.all_eq_true.mp h w hw)

/-- PATTERN #2 — THE DISPATCH LAW: the layout's encoding, applied to
    in-domain column data, round-trips through any suffix. One theorem,
    one case per encoding, each citing its codec's law. The INDUCTION on
    the spec is the nesting discipline's proof face: the sparse case's
    IH is the CHILD's own law — the recursive citation, never a
    re-proof. -/
theorem decodeColumn_encodeColumn_append (e : EncodingSpec) :
    ∀ (xs : List Nat), inDomain e xs = true → ∀ (rest : List UInt8),
      decodeColumn e (encodeColumn e xs ++ rest) = some (xs, rest) := by
  induction e with
  | identity =>
      intro xs h rest
      simp only [inDomain] at h
      exact decIdentity?_encIdentity_append xs
        (fun v hv => of_decide_eq_true (List.all_eq_true.mp h v hv)) rest
  | bitPacked w =>
      intro xs h rest
      simp only [inDomain] at h
      exact decBitPacked?_encBitPacked_append w xs
        (fun v hv => of_decide_eq_true (List.all_eq_true.mp h v hv)) rest
  | foR w =>
      intro xs h rest
      simp only [inDomain] at h
      exact decFoR?_encFoR_append w xs
        (fun v hv => of_decide_eq_true (List.all_eq_true.mp h v hv)) rest
  | dict =>
      intro xs h rest
      simp only [inDomain] at h
      exact decDict?_encDict_append xs
        (fun v hv => of_decide_eq_true (List.all_eq_true.mp h v hv)) rest
  | sequence =>
      intro xs h rest
      exact decSeq?_encSeqData_append xs h rest
  | constant =>
      intro xs h rest
      simp only [inDomain, Bool.and_eq_true, List.all_eq_true] at h
      cases xs with
      | nil => exact decConst?_encConst_nil rest
      | cons v vs =>
          have hv64 : v < 2 ^ 64 := of_decide_eq_true (h v (by simp)).1
          have h2 : vs.all (fun w => w == v) = true :=
            List.all_eq_true.mpr (fun w hw => by
              have := h w (by simp [hw])
              simpa using this.2)
          exact decConst?_encConst_append v hv64 vs h2 rest
  | sparse child ih =>
      intro xs h rest
      -- THE NESTING CITATION: the child's own dispatch law (the IH at
      -- the sub-spec) consumes the patches' payload; the framing layers
      -- peel (varint, u64, 1-bit mask) and the join rebuilds the rows.
      simp only [inDomain, Bool.and_eq_true, List.all_eq_true] at h
      have hzero : (0 : Nat) < 2 ^ 64 := Nat.pow_pos (by omega)
      cases xs with
      | nil =>
          simp only [encodeColumn, decodeColumn, List.headD, List.append_assoc,
            sparseMask, sparsePatches,
            decVarNat?_encVarNat_append,
            decU64?_encU64_append 0 hzero,
            decBitPacked?_encBitPacked_append 1 ([] : List Nat)
              (by simp) (encodeColumn child ([] : List Nat) ++ rest),
            Option.bind_some, Option.map_some]
          rw [ih [] (inDomain_nil child) rest]
          simp [sparseJoin]
      | cons u us =>
          have hu64 : u < 2 ^ 64 := of_decide_eq_true (h.1 u (by simp))
          have hmask := sparseMask_dom u (u :: us)
          have hjoin := sparseJoin_mask_patches u (u :: us)
          simp only [encodeColumn, decodeColumn, List.headD, List.append_assoc,
            decVarNat?_encVarNat_append,
            decU64?_encU64_append u hu64,
            decBitPacked?_encBitPacked_append 1 (sparseMask u (u :: us)) hmask
              (encodeColumn child (sparsePatches u (u :: us)) ++ rest),
            Option.bind_some, Option.map_some]
          rw [ih (sparsePatches u (u :: us)) h.2 rest]
          simp [hjoin]

/-! ## The column-data emitter (the layout drives the bytes) -/

/-- One column's data: the layout (the selection's row), the validity
    bits (when the layout carries the validity layer), the values. -/
structure ColumnData where
  name : String
  layout : ColumnLayout
  validity : List Bool
  values : List Nat

/-- THE EMISSION: the validity bitmap first (1 bit per row — the
    validity layer is OUTER; kernels peel), then the encoding's payload.
    The layout's spec DRIVES both. -/
def emitColumnData (c : ColumnData) : List UInt8 :=
  (if c.layout.validity then
      encBitPacked 1 (c.validity.map (fun b => if b then 1 else 0))
    else []) ++ encodeColumn c.layout.encoding c.values

/-- THE READBACK: the emission's inverse, layer for layer (the validity
    bits are consumed; the values' check is the law below). -/
def readColumnData (c : ColumnData) (bs : List UInt8) :
    Option (List Nat × List UInt8) :=
  if c.layout.validity then
    match decBitPacked? 1 bs with
    | some (_, r) => decodeColumn c.layout.encoding r
    | none => none
  else decodeColumn c.layout.encoding bs

/-- The validity bitmap's bits are in the 1-bit domain (0/1). -/
theorem validBits_dom (vs : List Bool) :
    ∀ v ∈ vs.map (fun b => if b then 1 else 0), v < 2 := by
  intro v hv
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
  cases b <;> simp

/-- PATTERN #2 — THE EMISSION LAW: the layout's encoding applied to
    in-domain data round-trips through the WHOLE emitted column (the
    validity bitmap consumed, the values restored). -/
theorem readColumnData_emitColumnData_append (c : ColumnData)
    (hdom : inDomain c.layout.encoding c.values = true) (rest : List UInt8) :
    readColumnData c (emitColumnData c ++ rest) = some (c.values, rest) := by
  unfold emitColumnData readColumnData
  split
  · next hv =>
      simp only [List.append_assoc]
      rw [decBitPacked?_encBitPacked_append 1
        (c.validity.map (fun b => if b then 1 else 0))
        (validBits_dom c.validity)
        (encodeColumn c.layout.encoding c.values ++ rest)]
      exact decodeColumn_encodeColumn_append _ _ hdom rest
  · next hv =>
      simp only [List.nil_append]
      exact decodeColumn_encodeColumn_append _ _ hdom rest

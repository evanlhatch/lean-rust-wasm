/-
# SchemaLang.Vortex.Encoding — the column encodings, with retention proofs

Lifted from flatland's `Flatland/Flatland/Encoding.lean` (the port-audit
called that file "engine-domain, not applicable" — overridden: the
encodings ARE the Vortex-central capability; the dtype layer this
package already ships is only half of vortex-array).

**The law.** An encoding is a transform `values → encoded form` with a
total decode, and the RETENTION THEOREM is `decode ∘ encode = id` —
the can't-lose round trip, proved PER ENCODING (flatland's
`read_encode` field; the erasure law). Bit layout, SIMD/cursor
mechanics, and byte formats stay OUT of Lean (lean-v3 Part 10
containment, inherited verbatim from flatland): an encoded column is a
representation with a readback, nothing more.

**The relation to our DType (the design, stated honestly).**
`SchemaLang.Vortex.DType` is the LOGICAL type-level vocabulary (the
wire-faithful dtype algebra). An encoding is a PHYSICAL COLUMN
transform: `ColumnEncoding α` acts on `List α` — a batch column's
values — never on the type. The relation: a `DType` names what the
values ARE; an `EncodingKind` (below) declares how the column is
physically stored; the retention theorem is what makes the declared
kind safe to erase at the readback boundary. The DType module is
UNTOUCHED (additive lane).

**The family** (flatland's = ported real; the additions marked):

- `ColumnEncoding` — the shape: `Repr` + `encode`/`read` + the law.
- `ColumnEncoding.id` — the identity (flatland).
- `ColumnEncoding.comp` — encodings stack; the law composes (flatland).
- `rleEncode`/`rleDecode`/`ColumnEncoding.rle` — **run-length** (NEW:
  the flatland file has FoR + dict but no RLE; vortex's run-end
  pattern, modeled as maximal runs of (value, count)).
- `ColumnEncoding.foR` — frame-of-reference over ℤ (flatland).
- `ColumnEncoding.dict` — dictionary, first-appearance order (flatland).
- `constEncode`/`constRead` — **constant** (NEW): the law holds on the
  ADMISSIBLE SUBDOMAIN (constant columns) only, so it is deliberately
  NOT a `ColumnEncoding` instance — the same honesty policy as
  flatland's lossy `Normalized` exemplar, ported below with its
  range/monotonicity facts.

**The policy this pins** (flatland REBUILD-architecture Part 15.3,
inherited): columns whose values the hash chain folds rest ONLY in
exact `ColumnEncoding`s (the retention theorem holds). Approximation
encodings (`Normalized`) are allowed only for consumers that tolerate
ε, and their facts must account for the error bound — proved below,
not asserted.

**Compiled tie (documented skip).** The validator-style duel
(encode → wasm → decode, the retention round trip executed against the
guest) needs a guest-compiled target over a wire representation this
lane does not model (Part 10 containment puts the byte format in Rust,
not Lean). The SPEC-level retention theorems here are the proof of
record; the duel joins when a wire codec for a concrete `Repr` lands.
-/
import SchemaLang.Vortex.DType

namespace SchemaLang.Vortex

/-! ## The encoding shape -/

/-- An encoding of columns of `α`: a representation type with a total
    encode and a cursor readback. The LAW is `read (encode xs) = xs`:
    encoding erases — logical values are recovered exactly. (Flatland's
    `ColumnEncoding`, lifted verbatim.) -/
structure ColumnEncoding (α : Type) where
  Repr : Type
  encode : List α → Repr
  read : Repr → List α
  read_encode : ∀ xs, read (encode xs) = xs

/-- The identity/primitive encoding: representation is the value list
    itself. Trivial instance, sanity — every law closes by `rfl`. -/
def ColumnEncoding.id : ColumnEncoding α where
  Repr := List α
  encode xs := xs
  read xs := xs
  read_encode _ := rfl

/-- Encodings stack: the outer encoding treats an `α`-column as the
    one-row column of reps `[e1.encode xs]` and encodes that with
    `e2`. The law goes through both laws by transitivity — nobody
    re-proves. (Flatland's `comp`, lifted verbatim.) -/
def ColumnEncoding.comp (e1 : ColumnEncoding α) (e2 : ColumnEncoding e1.Repr) :
    ColumnEncoding α where
  Repr := e2.Repr
  encode xs := e2.encode [e1.encode xs]
  read r := match e2.read r with | [] => [] | h :: _ => e1.read h
  read_encode := by
    intro xs
    have hrow : e2.read (e2.encode [e1.encode xs]) = [e1.encode xs] :=
      e2.read_encode (xs := [e1.encode xs])
    change (match e2.read (e2.encode [e1.encode xs]) with
              | [] => [] | h :: _ => e1.read h) = xs
    rw [hrow]
    change e1.read (e1.encode xs) = xs
    exact e1.read_encode xs

/-! ## The declared kind — the metadata half

The engine's per-column encoding declaration (flatland's
`predictedEncoding` fact strings, typed up). This is the DECLARATION a
schema/emitter records; `ColumnEncoding` above is the SEMANTICS the
declaration must denote. The name map is injective so the future
emitter's Rust table cannot collide (the `engineName_inj` pattern). -/

inductive EncodingKind where
  | identity | constant | rle | dict | forr
deriving Repr, BEq, DecidableEq, Inhabited

def EncodingKind.name : EncodingKind → String
  | .identity => "identity" | .constant => "constant" | .rle => "rle"
  | .dict => "dict" | .forr => "for"

theorem EncodingKind.name_inj : Function.Injective name := by
  intro a b h
  cases a <;> cases b <;> simp [name] at h ⊢ <;> exact h

/-! ## Run-length encoding — the runs exemplar (NEW)

Vortex's run-end pattern, shape-only: maximal runs of `(value, count)`,
last run first (built by `foldr`, so the head run is the one the new
head element extends). No bit layout, no run-end index arithmetic —
runs are data. The law holds for EVERY list (RLE is lossless
everywhere; no admissible-subdomain caveat). -/

/-- Extend the run encoding with a new head element: the head run grows
    when the values match, otherwise a fresh run opens. -/
def rleCons [DecidableEq α] (x : α) (runs : List (α × Nat)) : List (α × Nat) :=
  match runs with
  | (y, n) :: rest => if x == y then (y, n + 1) :: rest else (x, 1) :: runs
  | [] => (x, 1) :: []

/-- Encode: fold the runs from the right — the head run of the tail is
    the run the head element sees. -/
def rleEncode [DecidableEq α] (xs : List α) : List (α × Nat) :=
  xs.foldr rleCons []

/-- Readback: every run to its replicated block, blocks concatenated.
    Total on malformed data too (a zero-count run replicates to `[]`). -/
def rleDecode (runs : List (α × Nat)) : List α :=
  (runs.map fun p => List.replicate p.2 p.1).flatten

/-- The key step: extending the runs by one head element extends the
    readback by one head value. -/
theorem rleDecode_rleCons [DecidableEq α] (x : α) (runs : List (α × Nat)) :
    rleDecode (rleCons x runs) = x :: rleDecode runs := by
  cases runs with
  | nil => simp [rleCons, rleDecode]
  | cons r rest =>
      obtain ⟨y, n⟩ := r
      by_cases h : x = y
      · subst h
        simp [rleCons, rleDecode, List.replicate_succ]
      · have hne : (x == y) = false := by simp [h]
        simp [rleCons, hne, rleDecode, List.replicate_succ]

/-- **RLE retention**: decode ∘ encode = id. Every run is maximal and
    the fold rebuilds the list head-first, so the readback is exact. -/
theorem rleDecode_rleEncode [DecidableEq α] (xs : List α) :
    rleDecode (rleEncode xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hfold : rleEncode (x :: xs) = rleCons x (rleEncode xs) := rfl
      rw [hfold, rleDecode_rleCons, ih]

/-- The RLE exemplar as a `ColumnEncoding` instance. -/
def ColumnEncoding.rle [DecidableEq α] : ColumnEncoding α where
  Repr := List (α × Nat)
  encode := rleEncode
  read := rleDecode
  read_encode := rleDecode_rleEncode

/-! ## Constant — the admissible-subdomain exemplar (NEW, deliberately
     NOT a `ColumnEncoding` instance)

Vortex's `ConstantArray` applies only to columns whose values are all
equal — the array carries the check. Modeled honestly: `encode`/`read`
are total, but the retention law holds ONLY on the admissible subdomain
(constant columns). On a non-constant column the readback merges
distinct values (documented loss, like `Normalized` below) — so
pretending the universal law would be the lie the zero-sorry discipline
exists to prevent. -/

/-- A constant encoding: the row count plus the (optional) shared value.
    `none` is the empty column's count-0 row; a count with no value is
    malformed and reads back `[]` (the dead-fallback pattern — dead
    under the law, present so the read is total). -/
structure ConstantData (α : Type) where
  count : Nat
  value : Option α

/-- Encode: the count and the head value (if any). -/
def constEncode (xs : List α) : ConstantData α :=
  { count := xs.length, value := xs.head? }

/-- Readback: the shared value, replicated to the count. -/
def constRead : ConstantData α → List α
  | ⟨n, some v⟩ => List.replicate n v
  | ⟨_count, none⟩ => []

/-- **Constant retention, on the admissible subdomain**: a column whose
    every value equals its head round-trips exactly. (The empty column
    round-trips too: `constRead (constEncode []) = []` by `rfl` — the
    theorem states the informative case.) -/
theorem constRead_constEncode [DecidableEq α] (v : α) (vs : List α)
    (h : vs.all (fun w => w == v) = true) :
    constRead (constEncode (v :: vs)) = v :: vs := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
      have hall : (w == v) = true ∧ ws.all (fun u => u == v) = true := by
        simpa using List.all_eq_true.mp h
      have hweq : w = v := beq_iff_eq.mp hall.1
      subst hweq
      have hws := ih hall.2
      simp only [constEncode, List.length_cons, constRead, List.head?_cons] at hws ⊢
      rw [List.replicate_succ, hws]

/-! ## Frame-of-reference (FoR) — the primitive-int exemplar (flatland) -/

/-- A frame-of-reference encoding: a base value plus per-row offsets
    from it. Mirrors the engine's FoR block encoding in shape only
    (indexes, no bit layout). -/
structure FoRData where
  base : Int
  offsets : List Int

/-- Encode by choosing the frame base as the first value (head-or-0) and
    storing each value's offset from it. -/
def forEncode (xs : List Int) : FoRData :=
  { base := xs.headD 0, offsets := xs.map (fun x => x - xs.headD 0) }

/-- Readback: re-add the base to every offset. -/
def forRead (d : FoRData) : List Int :=
  d.offsets.map (fun o => o + d.base)

/-- FoR erases: encode-then-read recovers the column exactly. -/
theorem forRead_forEncode : ∀ (xs : List Int), forRead (forEncode xs) = xs := by
  intro xs
  simp [forRead, forEncode, List.map_map, Function.comp_def]

/-- The FoR exemplar as a `ColumnEncoding` instance. -/
def ColumnEncoding.foR : ColumnEncoding Int where
  Repr := FoRData
  encode := forEncode
  read := forRead
  read_encode := forRead_forEncode

/-! ## Dictionary encoding — the dedupe exemplar (flatland) -/

/-- A dictionary encoding: a deduplicated value list in first-appearance
    order plus per-row position codes into it. -/
structure DictData (α : Type) where
  /-- The dictionary, in first-appearance order (no duplicates). -/
  dict : List α
  /-- Codes into `dict` (positions, one per row; all in-bounds under
      the law). -/
  codes : List Nat

/-- Encode: the dictionary is `xs.eraseDups` (keeps first occurrences),
    and each row's code is its `List.idxOf` position in that dictionary. -/
def dictEncode [DecidableEq α] (xs : List α) : DictData α :=
  { dict := xs.eraseDups, codes := xs.map (fun x => xs.eraseDups.idxOf x) }

/-- Readback: map each code to the dictionary entry at that position.
    Total even on malformed data (the head serves as the `getD`
    fallback); the fallback never fires on law-abiding data. -/
def dictRead [DecidableEq α] (d : DictData α) : List α :=
  match d.dict with
  | [] => []
  | h :: _ => d.codes.map (fun c => d.dict.getD c h)

/-- Indexing a list at the position of `x` recovers `x` itself.
    (Flatland's lemma, lifted verbatim.) -/
theorem getD_idxOf_mem [DecidableEq α] {x : α} {xs : List α} (h : x ∈ xs) (fallback : α) :
    xs.getD (xs.idxOf x) fallback = x := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      by_cases hxy : x = y
      · subst x
        simp
      · have hys : x ∈ ys := (List.mem_cons.mp h).resolve_left hxy
        have hty : (y :: ys).idxOf x = ys.idxOf x + 1 := by
          rw [List.idxOf_cons]
          have hbeq : (y == x) = false := (beq_eq_false_iff_ne.mpr (fun hyx => hxy (Eq.symm hyx)))
          rw [hbeq]
          rfl
        rw [hty]
        simp [List.getD]
        exact ih hys

/-- **Dictionary retention**: for every element, its code is found at
    its position, and the read recovers it (dedup preserves membership). -/
theorem dictRead_dictEncode [DecidableEq α] : ∀ (xs : List α), dictRead (dictEncode xs) = xs := by
  intro xs
  induction xs with
  | nil => simp [dictEncode, dictRead]
  | cons y ys _ih =>
      rw [dictEncode, List.eraseDups_cons]
      let dict : List α := y :: (ys.filter (fun b => !b == y)).eraseDups
      change dictRead ⟨dict, (y :: ys).map (fun x => dict.idxOf x)⟩ = y :: ys
      have hmem {x : α} (hx : x ∈ y :: ys) : x ∈ dict := by
        dsimp [dict]
        by_cases hxy : x = y
        · subst x; simp
        · right
          have hxys : x ∈ ys := (List.mem_cons.mp hx).resolve_left hxy
          have hfilter : x ∈ ys.filter (fun b => !b == y) := by
            apply List.mem_filter.mpr
            constructor
            · exact hxys
            · have hbeq : (x == y) = false := (beq_eq_false_iff_ne.mpr hxy)
              simp [hbeq]
          exact List.mem_eraseDups.mpr hfilter
      have hgetD {x : α} (hx : x ∈ y :: ys) : dict.getD (dict.idxOf x) y = x :=
        getD_idxOf_mem (hmem hx) y
      simp only [dictRead, dict, List.map_map, List.map_cons]
      congr 1
      · have hyMem : y ∈ y :: ys := by simp
        exact hgetD hyMem
      · rw [show
            ys.map ((fun c : Nat => dict.getD c y) ∘ (fun x : α => dict.idxOf x))
              = ys.map (fun x : α => x)
          by
            apply List.map_congr_left
            intro x hx
            exact hgetD (List.mem_cons_of_mem y hx)]
        simp

/-- The dictionary exemplar as a `ColumnEncoding` instance. -/
def ColumnEncoding.dict [DecidableEq α] : ColumnEncoding α where
  Repr := DictData α
  encode := dictEncode
  read := dictRead
  read_encode := dictRead_dictEncode

/-! ## Normalized — the lossy exemplar (flatland; breaks erasure,
     modeled honestly)

Uniform scalar quantization: a codebook `(lo, buckets, width)` over Nat
values; each row is stored as its bucket code; readback truncates
DOWNWARD to the bucket floor. Deliberately NOT a `ColumnEncoding`
instance — the erasure law does not hold. The honest laws, ported
verbatim: range facts transfer, error is bounded by one bucket width,
quantization is monotone, cardinality can only shrink (documented
loss). -/

/-- A quantization codebook: covers `[lo, lo + buckets*width]`. -/
structure NormCodebook where
  lo : Nat
  buckets : Nat
  width : Nat
  buckets_pos : 0 < buckets
  width_pos : 0 < width

/-- The codebook's covered top. -/
def NormCodebook.hi (cb : NormCodebook) : Nat :=
  cb.lo + cb.buckets * cb.width

/-- Quantize one value: its bucket index. Under the range hypothesis
    `lo ≤ x ≤ hi`, the clamp at `buckets` in `normEncode` never fires. -/
def normQuant (cb : NormCodebook) (x : Nat) : Nat :=
  (x - cb.lo) / cb.width

/-- The readback of one code: the bucket floor. Downward-only error. -/
def normDeq (cb : NormCodebook) (c : Nat) : Nat :=
  cb.lo + c * cb.width

/-- The quantized representation: codebook plus one code per row. -/
structure NormData where
  cb : NormCodebook
  codes : List Nat

/-- Encode: each value's bucket index, clamped to the bucket count (the
    clamp is dead under the range hypothesis). -/
def normEncode (cb : NormCodebook) (xs : List Nat) : NormData :=
  { cb := cb, codes := xs.map (fun x => (normQuant cb x).min cb.buckets) }

/-- Readback: every code to its bucket floor. -/
def normRead (d : NormData) : List Nat :=
  d.codes.map (normDeq d.cb)

/-- In-range values land at or below the top bucket (the clamp is dead
    under the range hypothesis). -/
theorem normQuant_le_buckets (cb : NormCodebook) {x : Nat}
    (hlo : cb.lo ≤ x) (hhi : x ≤ cb.hi) : normQuant cb x ≤ cb.buckets := by
  have hsub : x - cb.lo ≤ cb.buckets * cb.width := by
    unfold NormCodebook.hi at hhi; omega
  have h := Nat.div_le_div_right (c := cb.width) hsub
  rw [Nat.mul_comm cb.buckets cb.width, Nat.mul_div_cancel_left _ cb.width_pos] at h
  exact h

/-- **Range transfer**: every readback value stays inside the covered
    range — range facts survive the approximation verbatim. -/
theorem normRead_normEncode_in_range (cb : NormCodebook) {xs : List Nat}
    (h : xs.all (fun x => cb.lo ≤ x ∧ x ≤ cb.hi)) :
    ∀ v ∈ normRead (normEncode cb xs), cb.lo ≤ v ∧ v ≤ cb.hi := by
  intro v hv
  simp only [normRead, normEncode, List.mem_map] at hv
  obtain ⟨c, hc, rfl⟩ := hv
  obtain ⟨x, hx, hxmin⟩ := hc
  have hxl : cb.lo ≤ x ∧ x ≤ cb.hi := by simpa using List.all_eq_true.mp h x hx
  have hle := normQuant_le_buckets cb hxl.1 hxl.2
  unfold normDeq
  rw [← hxmin]
  have hm : Nat.min (normQuant cb x) cb.buckets = normQuant cb x :=
    Nat.min_eq_left hle
  rw [hm]
  have hcm : normQuant cb x * cb.width ≤ cb.buckets * cb.width :=
    Nat.mul_le_mul_right _ hle
  exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left hcm _⟩

/-- **Error bound**: an in-range value never undershoots its readback
    and exceeds it by strictly less than one bucket width (the ε of the
    policy). -/
theorem norm_err_bound (cb : NormCodebook) {x : Nat}
    (hlo : cb.lo ≤ x) (_hhi : x ≤ cb.hi) :
    normDeq cb (normQuant cb x) ≤ x ∧ x - normDeq cb (normQuant cb x) < cb.width := by
  have hd : cb.width * ((x - cb.lo) / cb.width) + (x - cb.lo) % cb.width = x - cb.lo :=
    Nat.div_add_mod _ _
  have hm : (x - cb.lo) % cb.width < cb.width := Nat.mod_lt _ cb.width_pos
  unfold normDeq normQuant
  rw [Nat.mul_comm ((x - cb.lo) / cb.width) cb.width]
  generalize hq : (x - cb.lo) / cb.width = q at hd hm ⊢
  generalize hr : (x - cb.lo) % cb.width = r at hd hm ⊢
  omega

/-- Quantization is monotone on the covered domain: order comparisons
    survive, so order-legality facts survive conservatively. -/
theorem norm_mono (cb : NormCodebook) {x y : Nat}
    (_hx : cb.lo ≤ x) (_hy : cb.lo ≤ y) (hxy : x ≤ y) :
    normQuant cb x ≤ normQuant cb y :=
  Nat.div_le_div_right (by omega)

end SchemaLang.Vortex

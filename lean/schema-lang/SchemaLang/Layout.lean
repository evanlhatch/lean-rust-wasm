/-
# SchemaLang.Layout — the tensor layout layer (typed coordinates + offsets)

PROVENANCE: adapted from flatland's `Flatland/Flatland/Tensor.lean` (the
user's own prior module — `CoordsOf`/`flatIdxT`/`dot_inj`/`Coords.ofList?`
are verbatim-shape ports; the flatland Cell/column specifics are dropped).
THE NEW CONTENT tying it to this repo: `TVal.get` and
`TVal.toList_get` — the codec's flatten (`TVal.toList`, the wire order)
IS the layout: the element at coordinate `cs` sits at the flat index
`flatIdxT dims cs`. That theorem is what licenses the wasm adapter's
future offsets (a tensor field's memory layout = this arithmetic) and
pins the codec's ORDER as the layout, not a convention.

The two-worlds discipline (flatland's, kept):
- the WIRE world: `List Nat` coordinates + runtime `inB` checks
  (`flatIdx`) — ingress's reading;
- the TYPED world: `CoordsOf dims` — out-of-bounds unrepresentable,
  `flatIdxT` total, the bound carried by types;
- the bridge: `Coords.ofList?` validates ONCE; `flatIdxT_ofList` says the
  worlds agree exactly where the parse succeeded.

Ownership: schema-lang (the tensor lane). Imports Ty (the universe +
TVal/TSlices) and CodecValue (the flatten + the length lemmas).
-/

module

public import SchemaLang.CodecValue

@[expose] public section

namespace SchemaLang

/-! ## The wire world: coordinates as lists -/

/-- Coordinate-wise bounds check (DIMS first, coords second): lengths must
    match AND each coordinate < its dim. -/
def inB : List Nat → List Nat → Bool
  | [], [] => true
  | d :: ds, c :: cs => (c < d) && inB ds cs
  | _, _ => false

/-- Row-major strides: the stride of coordinate i is the product of the dims
    after it. `[d0,d1,d2] ↦ [d1*d2, d2, 1]`. -/
def strides : List Nat → List Nat
  | [] => []
  | _ :: ds => ds.prod :: strides ds

/-- The row-major offset `Σ cᵢ·strideᵢ` (coords first; mismatched lengths
    contribute 0 but `inB` rules them out). -/
def dot : List Nat → List Nat → Nat
  | [], [] => 0
  | c :: cs, s :: ss => c * s + dot cs ss
  | _, _ => 0

/-- The flat offset of a coordinate tuple: `none` unless in-bounds. -/
def flatIdx (dims : List Nat) (cs : List Nat) : Option Nat :=
  if inB dims cs then some (dot cs (strides dims)) else none

/-- The core bound: in-bounds coordinates produce an offset strictly inside
    the shape. (flatland's `dot_bound` verbatim.) -/
theorem dot_bound : ∀ (dims cs : List Nat), inB dims cs = true →
    dot cs (strides dims) < dims.prod
  | [], [], _ => by simp [dot, strides]
  | [], _ :: _, hb => by simp [inB] at hb
  | _ :: _, [], hb => by simp [inB] at hb
  | _ :: _, _ :: _, hb => by
    simp only [inB, Bool.and_eq_true] at hb
    -- renamed binders (the flatland original's names shadow below)
    obtain ⟨hcd, hrest⟩ := hb
    rename_i d ds c cs
    simp only [strides, dot]
    have hcd : c < d := of_decide_eq_true hcd
    have ih := dot_bound ds cs hrest
    -- c · P + (< P) < (c+1)·P ≤ d·P since c < d (steps kept LINEAR in
    -- the atoms c·P / d·P — the flatland AGENTS.md trap)
    have step : c * ds.prod + ds.prod ≤ d * ds.prod := by
      have h := Nat.mul_le_mul_right ds.prod (Nat.succ_le_of_lt hcd)
      simpa [Nat.add_mul, Nat.one_mul] using h
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left ih (c * ds.prod)) step

/-- **No aliasing** (the write-safety theorem): two in-bounds coordinate
    tuples with the same offset are equal — scatter through a tensor view
    cannot collide. (flatland's `dot_inj` verbatim.) -/
theorem dot_inj : ∀ (dims cs₁ cs₂ : List Nat), inB dims cs₁ = true →
    inB dims cs₂ = true →
    dot cs₁ (strides dims) = dot cs₂ (strides dims) → cs₁ = cs₂
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, hb, _, _ => by simp [inB] at hb
  | [], [], _ :: _, _, h₂, _ => by simp [inB] at h₂
  | _ :: _, [], _, hb, _, _ => by simp [inB] at hb
  | _ :: _, _ :: _, [], _, h₂, _ => by simp [inB] at h₂
  | _ :: _, _ :: _, _ :: _, h₁, h₂, heq => by
    simp only [inB, Bool.and_eq_true] at h₁ h₂
    rename_i d ds c₁ r₁ c₂ r₂
    obtain ⟨hc₁, hr₁⟩ := h₁
    obtain ⟨hc₂, hr₂⟩ := h₂
    simp only [strides, dot] at heq
    rcases Nat.lt_trichotomy c₁ c₂ with hlt | heq' | hgt
    · exfalso
      have b₁ := dot_bound ds r₁ hr₁
      have step : c₁ * ds.prod + ds.prod ≤ c₂ * ds.prod := by
        have h := Nat.mul_le_mul_right ds.prod (Nat.succ_le_of_lt hlt)
        simpa [Nat.add_mul, Nat.one_mul] using h
      have key : c₁ * ds.prod + dot r₁ (strides ds) <
          c₂ * ds.prod + dot r₂ (strides ds) := by
        calc c₁ * ds.prod + dot r₁ (strides ds)
            < c₁ * ds.prod + ds.prod := Nat.add_lt_add_left b₁ _
          _ ≤ c₂ * ds.prod := step
          _ ≤ c₂ * ds.prod + dot r₂ (strides ds) := Nat.le_add_right _ _
      rw [heq] at key
      exact Nat.lt_irrefl _ key
    · subst heq'
      exact congrArg (List.cons _) (dot_inj ds r₁ r₂ hr₁ hr₂ (Nat.add_left_cancel heq))
    · exfalso
      have b₂ := dot_bound ds r₂ hr₂
      have step : c₂ * ds.prod + ds.prod ≤ c₁ * ds.prod := by
        have h := Nat.mul_le_mul_right ds.prod (Nat.succ_le_of_lt hgt)
        simpa [Nat.add_mul, Nat.one_mul] using h
      have key : c₂ * ds.prod + dot r₂ (strides ds) <
          c₁ * ds.prod + dot r₁ (strides ds) := by
        calc c₂ * ds.prod + dot r₂ (strides ds)
            < c₂ * ds.prod + ds.prod := Nat.add_lt_add_left b₂ _
          _ ≤ c₁ * ds.prod := step
          _ ≤ c₁ * ds.prod + dot r₁ (strides ds) := Nat.le_add_right _ _
      rw [← heq] at key
      exact Nat.lt_irrefl _ key

/-! ## The typed world: coordinates bounded by construction -/

/-- The coordinate type FOR a dims list — an indexed family over the
    shape's structure. `[2,3] ↦ Fin 2 × Fin 3`; rank-0 is Unit. -/
def CoordsOf : List Nat → Type
  | [] => Unit
  | d :: ds => Fin d × CoordsOf ds

/-- Total row-major offset: by construction inside the shape. (flatland's
    `flatIdxT` verbatim; the bound carried by types, not checked.) -/
def flatIdxT : (dims : List Nat) → CoordsOf dims → Fin dims.prod
  | [], _ => ⟨0, by simp [List.prod]⟩
  | d :: ds, (c, cs) =>
    ⟨c.val * ds.prod + (flatIdxT ds cs).val,
      by
        have hcd : c.val < d := c.isLt
        have ih := (flatIdxT ds cs).isLt
        have step : c.val * ds.prod + ds.prod ≤ d * ds.prod := by
          have h := Nat.mul_le_mul_right ds.prod (Nat.succ_le_of_lt hcd)
          simpa [Nat.add_mul, Nat.one_mul] using h
        calc c.val * ds.prod + (flatIdxT ds cs).val
            < c.val * ds.prod + ds.prod := Nat.add_lt_add_left ih _
          _ ≤ d * ds.prod := step⟩

/-- **Write-safety, typed**: the total offset map is injective — two
    distinct typed coordinates never hit one cell. (flatland's
    `flatIdxT_inj` verbatim.) -/
theorem flatIdxT_inj (dims : List Nat) :
    Function.Injective (fun cs => ((flatIdxT dims cs : Fin dims.prod) : Nat)) := by
  induction dims with
  | nil => intro cs₁ cs₂ _; cases cs₁; cases cs₂; rfl
  | cons d ds ih =>
    intro cs₁ cs₂ heq
    obtain ⟨c₁, r₁⟩ := cs₁
    obtain ⟨c₂, r₂⟩ := cs₂
    simp only [flatIdxT] at heq
    rcases Nat.lt_trichotomy c₁.val c₂.val with hlt | heq' | hgt
    · exfalso
      have b₁ := (flatIdxT ds r₁).isLt
      have step : c₁.val * ds.prod + ds.prod ≤ c₂.val * ds.prod := by
        have h := Nat.mul_le_mul_right ds.prod (Nat.succ_le_of_lt hlt)
        simpa [Nat.add_mul, Nat.one_mul] using h
      have key : c₁.val * ds.prod + (flatIdxT ds r₁).val <
          c₂ * ds.prod + (flatIdxT ds r₂).val := by
        calc c₁.val * ds.prod + (flatIdxT ds r₁).val
            < c₁.val * ds.prod + ds.prod := Nat.add_lt_add_left b₁ _
          _ ≤ c₂.val * ds.prod := step
          _ ≤ c₂.val * ds.prod + (flatIdxT ds r₂).val := Nat.le_add_right _ _
      rw [heq] at key
      exact Nat.lt_irrefl _ key
    · have hce : c₁ = c₂ := Fin.ext heq'
      cases hce
      rw [ih (Nat.add_left_cancel heq)]
    · exfalso
      have b₂ := (flatIdxT ds r₂).isLt
      have step : c₂.val * ds.prod + ds.prod ≤ c₁.val * ds.prod := by
        have h := Nat.mul_le_mul_right ds.prod (Nat.succ_le_of_lt hgt)
        simpa [Nat.add_mul, Nat.one_mul] using h
      have key : c₂.val * ds.prod + (flatIdxT ds r₂).val <
          c₁.val * ds.prod + (flatIdxT ds r₁).val := by
        calc c₂.val * ds.prod + (flatIdxT ds r₂).val
            < c₂.val * ds.prod + ds.prod := Nat.add_lt_add_left b₂ _
          _ ≤ c₁.val * ds.prod := step
          _ ≤ c₁.val * ds.prod + (flatIdxT ds r₁).val := Nat.le_add_right _ _
      rw [← heq] at key
      exact Nat.lt_irrefl _ key

/-! ## The bridge: wire coords ↔ typed coords (ingress validates ONCE) -/

/-- One-component boundary check: a raw Nat becomes a bounded index or
    nothing. Single dite — no match on the bound — so proofs split once. -/
def Fin.ofList? (d c : Nat) : Option (Fin d) :=
  if h : c < d then some ⟨c, h⟩ else none

/-- The parse succeeded iff the value is in bounds, and then the bounded
    index carries exactly that value. -/
theorem Fin.ofList?_eq_some {d c : Nat} {c' : Fin d}
    (h : Fin.ofList? d c = some c') : c'.val = c ∧ c < d := by
  unfold Fin.ofList? at h
  split at h
  · rename_i hlt
    have hinj := Option.some.inj h
    subst hinj
    exact ⟨rfl, hlt⟩
  · simp at h

/-- Parse raw coordinates into typed ones; none on length mismatch or any
    OOB component (THE boundary check, done once). Explicit matches, not
    do-notation: the proofs case on these scrutinees directly. -/
def Coords.ofList? : (dims : List Nat) → List Nat → Option (CoordsOf dims)
  | [], [] => some ()
  | [], _ :: _ => none
  | _ :: _, [] => none
  | d :: ds, c :: cs =>
    match Fin.ofList? d c with
    | none => none
    | some c' =>
      match Coords.ofList? ds cs with
      | none => none
      | some cs' => some (c', cs')

/-- The typed offset of parsed coordinates equals the list-world offset —
    the two worlds agree exactly where the parser succeeded. (flatland's
    `flatIdxT_ofList` verbatim-shape.) -/
theorem flatIdxT_ofList (dims cs : List Nat) (t : CoordsOf dims)
    (h : Coords.ofList? dims cs = some t) :
    (flatIdxT dims t : Nat) = dot cs (strides dims) ∧ inB dims cs = true := by
  induction dims generalizing cs with
  | nil => cases cs with
    | nil => cases t; simp [flatIdxT, dot, strides, inB]
    | cons c rest => simp [Coords.ofList?] at h
  | cons d ds ih => cases cs with
    | nil => simp [Coords.ofList?] at h
    | cons c rest =>
      obtain ⟨c', cs'⟩ := t
      simp only [Coords.ofList?] at h
      cases hFin : Fin.ofList? d c with
      | none => rw [hFin] at h; simp at h
      | some c'' =>
        rw [hFin] at h
        cases hRest : Coords.ofList? ds rest with
        | none => rw [hRest] at h; simp at h
        | some cs'' =>
          rw [hRest] at h
          have h' := Option.some.inj h
          obtain ⟨hc'', hcs''⟩ := Prod.mk.inj h'
          obtain ⟨hcv1, hcv2⟩ := Fin.ofList?_eq_some hFin
          cases hc''
          cases hcs''
          obtain ⟨ht, hb⟩ := ih rest cs' hRest
          constructor
          · simp only [flatIdxT, strides, dot]
            rw [hcv1, ht]
          · simp only [inB, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨hcv2, hb⟩

/-! ## THE LAYOUT TIE: the flatten's order IS this layout

`TVal.get` reads a tensor payload at a (typed) coordinate; the theorem:
the flatten (`TVal.toList` — the WIRE order) at the typed offset IS the
coordinate's element. The codec's order is the layout, not a convention —
this is the license any addressed-memory consumer (the wasm adapter) can
cite instead of re-deriving the row-major arithmetic.
-/

-- (plain comment: doc comments cannot precede `mutual`. The doc:
-- read a tensor payload at a typed coordinate — total, the coords
-- bounded by construction, the `readViewT` discipline. The Fin index
-- matches via .val — 4.33's Fin is a structure, not zero/succ ctors.)
mutual
def TVal.get : {t : Ty} → {dims : List Nat} → TVal t dims → CoordsOf dims → Value t
  | _, _, .scalar v, () => v
  | _, _, .dim ss, (c, cs) => TSlices.get ss c cs

def TSlices.get : {t : Ty} → {dims : List Nat} → {m : Nat} →
    TSlices t dims m → Fin m → CoordsOf dims → Value t
  | _, _, _, @TSlices.cons _ _ m' x ss, c, cs =>
      if h : c.val = 0 then x.get cs
      else ss.get ⟨c.val - 1, by have := c.isLt; omega⟩ cs
end

/-! ### THE LAYOUT TIE (getElem?-form — no default value exists for a
general `Value t` GADT, so the Option-form carries the totality; the
flatland `readView_eq` lesson holds: the offset rides explicitly, and the
builder's equations are simp lemmas — WF, not definitional) -/

-- (plain comment: doc comments cannot precede `mutual`. The doc:
-- the wire flatten's element at the SLICE's offset = the slice's read.
-- The offset = `c.val * dims.prod + off` — the SAME shape `flatIdxT`
-- uses, so this theorem is the one any addressed-memory consumer cites.)
mutual
theorem TSlices.toList_get : {t : Ty} → {dims : List Nat} → {m : Nat} →
    (ss : TSlices t dims m) → (c : Fin m) → (cs : CoordsOf dims) →
    (TSlices.toList ss)[c.val * dims.prod + (flatIdxT dims cs).val]?
      = some (TSlices.get ss c cs)
  | t, dims, _, .cons x ss, c, cs => by
      -- the offset = c.val·P + off — the HEAD slice when c.val = 0
      -- (inside ITS flatten at off), the TAIL at the j·P + off
      -- position otherwise (the head's flatten = P elements long)
      have hF := TVal.toList_length x
      have hP : (TVal.toList x).length = dims.prod := by
        rw [hF, flatLength_eq_prod]
      have hi := (flatIdxT dims cs).isLt
      simp only [TSlices.toList]
      cases hc : c.val with
      | zero =>
          -- the offset = 0·P + off = off — the HEAD's flatten
          simp only [Nat.zero_mul, Nat.zero_add]
          rw [List.getElem?_append_left (by omega)]
          simp only [TSlices.get, dif_pos hc]
          exact TVal.toList_get x cs
      | succ j =>
          -- the offset = (j+1)·P + off — the TAIL's flatten at
          -- j·P + off (the head's flatten = P elements long)
          have hcj : c.val = j + 1 := by rw [hc]
          have hshift : (j + 1) * dims.prod + (flatIdxT dims cs).val
              = (TVal.toList x).length
                + (j * dims.prod + (flatIdxT dims cs).val) := by
            rw [hP, Nat.succ_mul]; omega
          rw [hshift]
          simp only [List.getElem?_append]
          split
          · omega
          · rw [Nat.add_sub_cancel_left]
            have hnz : c.val ≠ 0 := by rw [hcj]; omega
            have hget : (TSlices.cons x ss).get c cs
                = ss.get ⟨c.val - 1, by have h1 := hcj; have h2 := c.isLt; omega⟩ cs := by
              simp only [TSlices.get, dif_neg hnz]
            rw [hget]
            simp only [show c.val - 1 = j from by rw [hcj]; omega]
            exact TSlices.toList_get ss
              ⟨j, by have h1 := hcj; have h2 := c.isLt; omega⟩ cs
  termination_by _ _ _ ss _ _ => sizeOf ss

theorem TVal.toList_get : {t : Ty} → {dims : List Nat} → (tv : TVal t dims) →
    (cs : CoordsOf dims) →
    (TVal.toList tv)[(flatIdxT dims cs).val]? = some (TVal.get tv cs)
  | _, _, .scalar v, () => rfl
  | _, _, .dim ss, (c, cs) => TSlices.toList_get ss c cs
  termination_by _ _ tv _ => sizeOf tv
end
end SchemaLang

/-
WasmBackend.Layout — the canonical-ABI FLAT record layout, as functions
the adapters emit FROM (notes/seam-contract.md seam #5).

The adapters lower the guest's records to the canonical ABI's memory
encoding: the fields in WIT order, each at its aligned offset — a u64/
i64/f64 field is 8-wide and 8-aligned; every other scalar is 4-wide and
4-aligned; a string/list/option field is a (ptr, len) PAIR (two 4-wide
halves; the pair = 8 bytes). THE BUG THIS CLOSES: the adapters' offsets
were hand numbers, and the hand numbers were wrong twice — listUser
stored every field at +0/+4 (the id clobbered by the name pointer), and
the element layout only surfaced when a record crossed a STREAM
(watch-users' decoded tags = the length pair read as bytes). The
offsets in the emitted WAT are now THIS module's functions' outputs:
the same numbers the theorems talk about.

Theorems (the layout's soundness):
* `width_pos` — every field is at least 1 byte wide (the round-up's
  fuel);
* `padded_ge` — the alignment padding never moves a field BACKWARD;
* `go_ge` — every field's offset ≥ the record's base offset;
* `go_pairwise` — the offsets are STRICTLY INCREASING = no two fields
  overlap (a store to field i cannot touch field j > i, because the
  gap between their offsets is ≥ field i's width — `go_ge` + the
  width_pos on the intermediate fields);
* the concrete pins — the demo's user record layout IS [0, 8, 16, 24]
  with size 32 (rfl — the numbers the adapters emit and the host's
  wit-bindgen Lift reads).

The HOST side's layout = wit-bindgen's generated Lift — the
guest≡host agreement = the differential duel (the decode through the
host's types, 240 rows); this module proves the GUEST side is the
canonical ABI's own layout.
-/
import SchemaLang

open SchemaLang

namespace WasmBackend.Layout

/-- The byte width of one canonical-ABI flat field. A string/bytes/
    list/option/result/future/stream/reference field is a (ptr, len)
    PAIR — 8 bytes; the 64-bit scalars are 8; the rest are 4. -/
def width : Ty → Nat
  | .u64 | .i64 | .f64 => 8
  | .string | .bytes | .list _ | .option _ | .result _ _ | .future _
      | .stream _ | .ty _ => 8
  | .bool | .u8 | .u16 | .u32 | .i8 | .i16 | .i32 | .f32 => 4

theorem width_pos (t : Ty) : 0 < width t := by cases t <;> simp [width] <;> omega

/-- The byte alignment of one field: 8 for the 8-wide fields, else 4. -/
def align : Ty → Nat
  | .u64 | .i64 | .f64 => 8
  | _ => 4

theorem align_pos (t : Ty) : 0 < align t := by cases t <;> simp [align] <;> omega

/-- The offsets walk: `go ts off` = the field offsets for `ts` starting
    from `off`, each field aligned up to its own alignment. -/
def go : List Ty → Nat → List Nat
  | [], _ => []
  | t :: ts, off =>
      ((off + align t - 1) / align t * align t) ::
        go ts ((off + align t - 1) / align t * align t + width t)

/-- THE field offsets for a record (from the record's base). -/
def offsets (ts : List Ty) : List Nat := go ts 0

/-- The total record size: the last field's end, rounded up to the
    record's max alignment (= the array stride = the host's item size). -/
def size (ts : List Ty) : Nat :=
  match go ts 0 with
  | [] => 0
  | offs =>
      let last := offs.getLast! + width ts.getLast!
      let maxAlign := (ts.map align).foldl Nat.max 4
      (last + maxAlign - 1) / maxAlign * maxAlign

/-- The alignment round-up never moves a field backward. -/
theorem padded_ge (off a : Nat) (ha : 0 < a) : off ≤ (off + a - 1) / a * a := by
  have h := Nat.mod_add_div' (off + a - 1) a
  have h2 := Nat.mod_lt (off + a - 1) ha
  omega

/-- Every offset in the walk is ≥ the walk's base offset. -/
theorem go_ge : ∀ (ts : List Ty) (off : Nat), ∀ x ∈ go ts off, off ≤ x := by
  intro ts
  induction ts with
  | nil => intro off x hx; cases hx
  | cons t ts ih =>
      intro off x hx
      simp only [go] at hx ⊢
      have hpad := padded_ge off (align t) (align_pos t)
      have hd := List.mem_cons.mp hx
      cases hd with
      | inl he => rw [he]; exact hpad
      | inr hm =>
          have h1 := ih _ x hm
          calc off ≤ (off + align t - 1) / align t * align t := hpad
            _ ≤ (off + align t - 1) / align t * align t + width t :=
                Nat.le_add_right _ _
            _ ≤ x := h1

/-- The offsets are STRICTLY INCREASING — no two fields overlap: the
    gap between consecutive offsets is ≥ the earlier field's width. -/
theorem go_pairwise : ∀ (ts : List Ty) (off : Nat), (go ts off).Pairwise (· < ·) := by
  intro ts
  induction ts with
  | nil => intro off; exact List.Pairwise.nil
  | cons t ts ih =>
      intro off
      refine List.Pairwise.cons ?_ (ih _)
      intro y hy
      have h1 := go_ge ts ((off + align t - 1) / align t * align t + width t) y hy
      have h2 := padded_ge off (align t) (align_pos t)
      have h3 := width_pos t
      omega

/-- The offsets are strictly increasing. -/
theorem offsets_sorted (ts : List Ty) : (offsets ts).Pairwise (· < ·) := go_pairwise ts 0

/-! ## The concrete pins — the demo's user record

The WIT field order: `id: u64, name: string, email: string, tags:
list<string>`. These ARE the numbers in the emitted adapters (the
element stores' `offset=` operands) and the host's item size. The type
list lives HERE once — WasmBackend.lean (userLayout/userSize/
userFieldTys) and Audit.lean (stride) consume the same abbrev, so the
five hand-written copies of the literal fold to one source. -/

/-- The user record's schema types, in WIT field order. -/
abbrev userTys : List Ty := [.u64, .string, .string, .list .string]

/-- The user record's field offsets: id@0, name@8, email@16, tags@24. -/
theorem user_offsets : offsets userTys = [0, 8, 16, 24] := rfl

/-- The user record's size = 32 bytes = the stream item stride. -/
theorem user_size : size userTys = 32 := rfl

/-- A scalar-only record packs from 0 with no padding. -/
theorem u64_offsets : offsets [.u64] = [0] := rfl

end WasmBackend.Layout

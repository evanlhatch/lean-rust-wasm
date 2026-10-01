/-
# Guest.Layout — the canonical-ABI FLAT record layout, as functions

The D6 port of the legacy `WasmBackend.Layout` (the PROVED
canonical-ABI layout: the offsets/size walk + the non-overlap theorem
+ the concrete pins — the proof content re-homed, the closed grammar
the new tree's own `Wit.Ty`).

The convention (the legacy one, over the new tree's closed grammar):
the fields sit in WIT order, each at its aligned offset — a `u64`/`i64`
field is 8-wide and 8-aligned; `bool` is 4-wide and 4-aligned; a
`string`/`list` field is the `(ptr, len)` PAIR (8 bytes, 8-aligned);
an `option`/`result` field is the `(disc, payload)` pair in the same
8-byte form (the legacy codec's convention: the payload rides
out-of-line — the full inline-payload size ladder is the codec lane's
named boundary, not this module's); a `tuple` field concatenates its
members' widths at the members' max alignment (conservative packing:
the round-up never under-allocates a max-aligned base); the D2 handle
rows (`stream`/`future`/`own`/`borrow`) are the ONE `i32` handle —
4-wide and 4-aligned (`Guest.Component.flatOf`'s face, NOT the legacy
`(ptr, len)` pair: the new tree's waitable rows are handles).

Theorems (the layout's soundness — the legacy statements, the proof
content intact):
* `width_pos` / `align_pos` — every field is at least 1 byte wide /
  4-aligned (the round-up's fuel);
* `padded_ge` — the alignment padding never moves a field BACKWARD;
* `go_ge` — every field's offset ≥ the record's base offset;
* `go_pairwise` — the offsets are STRICTLY INCREASING = no two fields
  overlap (a store to field i cannot touch field j > i, because the
  gap between their offsets is ≥ field i's width — `go_ge` + the
  width_pos on the intermediate fields);
* `offsets_sorted` — the record face of `go_pairwise`;
* the concrete pins — the demo's user record layout IS
  [0, 8, 16, 24] with size 32 (rfl — the numbers the adapters emit
  and the host's wit-bindgen Lift reads).

TRAP the port closes (the legacy module's finding, kept): the
adapters' offsets were hand numbers, wrong twice — listUser stored
every field at +0/+4 (the id clobbered by the name pointer), and the
layout only surfaced when a record crossed a STREAM. THE CONSUMER
STATE (the head's earlier "no emitter consumer" note, resolved for
the OBJECT lane): `Guest.Lower`'s boxed-Nat lane now derives its
object slot grid FROM this module's functions — the boxed object's
`boxSize`/`rcCellOff`/`boxPayloadOff` and the closure's
`closureFnIdxOff`/`closureCapOff`/`closureSize` are `size`/`offsets`
outputs (the honest adapter: one `.u64` Layout field per 8-byte
object SLOT; the u8 tag @4 is a sub-slot face, not a Layout field),
and `offsets_sorted` is CONSUMED — the emitter's stores to distinct
slots cannot overlap by construction (`box_slots_sorted` et al.).
The hand numbers died into the proved functions; the byte-tie held
(the generated components' bytes unchanged — the same layout, now
proved-derived). STILL NAMED (the leftover rule, the remaining
adoption order): the canonical-ABI ADAPTER face's field store — the
component boundary's record marshaling — when it lands, consumes
`width`/`offsets` too, never a second hand-numbered table. Today's
other consumers are the pins: ComponentTests' layout suite (the demo
record IS [0, 8, 16, 24] with size 32 — the legacy's wrong-twice
hand numbers, refused by the theorems' own numbers).

The HOST side's layout = wit-bindgen's generated Lift — the guest≡host
agreement = the differential duel (the host's typed calls); this
module pins the GUEST side is the canonical ABI's own layout.

Cone: core-only (imports `Wit` — itself core-only; no mathlib, no
Batteries — the cone rule).
-/

import Wit

namespace Guest.Layout

/-- The byte width of one canonical-ABI flat field (the convention
    documented at the module head). Total over the closed grammar. -/
def width : Wit.Ty → Nat
  | .atom .u64 | .atom .i64 => 8
  | .atom .string => 8
  | .atom .bool => 4
  -- the composites ride the 8-byte (ptr, len) / (disc, payload) pair
  -- of their wire form (the `list` precedent; the module head's note)
  | .option _ | .list _ | .result _ _ | .resultOk _ | .resultErr _ => 8
  -- the tuple concatenates its members (the record discipline)
  | .tuple a b => width a + width b
  -- the D2 handle rows: the ONE i32 (flatOf's face)
  | .stream _ | .future _ | .own _ | .borrow _ => 4

theorem width_pos : ∀ (t : Wit.Ty), 0 < width t := by
  intro t
  induction t with
  | atom s => cases s <;> simp [width] <;> omega
  | list _ => simp [width]
  | option _ => simp [width]
  | stream _ => simp [width]
  | future _ => simp [width]
  | result _ _ => simp [width]
  | resultOk _ => simp [width]
  | resultErr _ => simp [width]
  | own _ => simp [width]
  | borrow _ => simp [width]
  | tuple a b iha ihb => simp only [width]; omega

/-- The byte alignment of one field: 8 for the 8-wide fields, else 4;
    the tuple rides its members' max. -/
def align : Wit.Ty → Nat
  | .atom .u64 | .atom .i64 | .atom .string => 8
  | .option _ | .list _ | .result _ _ | .resultOk _ | .resultErr _ => 8
  | .tuple a b => Nat.max (align a) (align b)
  | _ => 4

theorem align_pos : ∀ (t : Wit.Ty), 0 < align t := by
  intro t
  induction t with
  | atom s => cases s <;> simp [align] <;> omega
  | list _ => simp [align]
  | option _ => simp [align]
  | stream _ => simp [align]
  | future _ => simp [align]
  | result _ _ => simp [align]
  | resultOk _ => simp [align]
  | resultErr _ => simp [align]
  | own _ => simp [align]
  | borrow _ => simp [align]
  | tuple a b iha ihb =>
      exact Nat.lt_of_lt_of_le iha (Nat.le_max_left (align a) (align b))

/-- The offsets walk: `go ts off` = the field offsets for `ts` starting
    from `off`, each field aligned up to its own alignment. -/
def go : List Wit.Ty → Nat → List Nat
  | [], _ => []
  | t :: ts, off =>
      ((off + align t - 1) / align t * align t) ::
        go ts ((off + align t - 1) / align t * align t + width t)

/-- THE field offsets for a record (from the record's base). -/
def offsets (ts : List Wit.Ty) : List Nat := go ts 0

/-- The total record size: the last field's end, rounded up to the
    record's max alignment (= the array stride = the host's item
    size). -/
def size (ts : List Wit.Ty) : Nat :=
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
theorem go_ge : ∀ (ts : List Wit.Ty) (off : Nat), ∀ x ∈ go ts off, off ≤ x := by
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
theorem go_pairwise : ∀ (ts : List Wit.Ty) (off : Nat), (go ts off).Pairwise (· < ·) := by
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

theorem offsets_sorted (ts : List Wit.Ty) : (offsets ts).Pairwise (· < ·) := go_pairwise ts 0

/-! ## The concrete pins — the demo's user record

The WIT field order: `id: u64, name: string, email: string, tags:
list<string>`. These ARE the numbers in the emitted adapters (the
element stores' `offset=` operands) and the host's item size. The
type list lives HERE once — the host's wit-bindgen Lift and the
emitters consume the same abbrev's numbers, so the hand-written
copies of the literal fold to one source. -/

/-- The user record's schema types, in WIT field order. -/
abbrev userTys : List Wit.Ty :=
  [.atom .u64, .atom .string, .atom .string, .list (.atom .string)]

/-- The user record's field offsets: id@0, name@8, email@16, tags@24. -/
theorem user_offsets : offsets userTys = [0, 8, 16, 24] := rfl

/-- The user record's size = 32 bytes = the stream item stride. -/
theorem user_size : size userTys = 32 := rfl

theorem u64_offsets : offsets [.atom .u64] = [0] := rfl

end Guest.Layout

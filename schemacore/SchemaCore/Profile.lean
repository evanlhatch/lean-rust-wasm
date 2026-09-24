/- # SchemaCore.Profile — the semantic-profiles lane (notes/v3/16-surface.md §4.5)

Owner: the semantic-profiles agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/16-surface.md §4.5 (the ACTIVATED lane: the
game-engine product needs the deterministic float) + the review's §12
(units/semantic profiles at the primitive level: "a field called
amount : UInt64 omits crucial meaning — cents or dollars? … Make
semantic profiles explicit. Phantom indices/refinements often erase
without storage cost").

THE DISCIPLINE (§4.5, the honest minimal): a `Profile` names WHICH
semantic a scalar carries. The lane lands in two pieces:

1. `Profile` — the closed enum: `plain` (the default: the bare
   scalar's own semantics) and `deterministic` (the fixed-point
   discipline — the honest resolution of the no-floats exclusion,
   NOT its avoidance). The enum stays CLOSED (15-patterns #15's
   discipline, one level up): the honest `fast` slot (hardware-float
   semantics with its forfeits named) extends the enum only with its
   full fold — every consumer's match downstream — when a consumer
   that needs hardware floats lands. The extension is driven by the
   compiler, not remembered.

2. `Profiled p α` — the profiled wrapper. The phantom index `p` is a
   TYPE INDEX only: the runtime representation is the base scalar
   (ONE field, nothing else). The erasure is PROVED, not asserted:
   `Profiled.iso` is a true `Kit.Iso` whose both round trips are
   `rfl`, and `Profiled.erase` pins the wrapper's data as the raw
   field alone. This is the review's "phantom indices erase without
   storage cost" as a theorem shape.

THE DETERMINISTIC FLOAT (the one honest profile first — the OWNER's
discipline): `Fixed scale` is the fixed-point carrier, the
`Money USD Cents` shape — the value IS `units`, an integer of the
scale's units; it represents the rational `units / scale`. The scale
lives in the TYPE (erases at runtime — §4.5's erasure doctrine); the
u64 wire capacity lives in the type too (the bounded lane's pattern:
out-of-contract values are unconstructible, not checked).

What `deterministic` PROMISES (each a law below, never a hope):

- exact addition: `add?` is the units' sum, no rounding, and the
  overflow teeth REFUSE (return `none`) at the wire capacity — never
  a silent wrap (the hardware `+`'s forfeited lie);
- named rounding for multiplication: `mul?` rounds the exact
  rational product DOWN — floor, the truncating division — with the
  floor bounds stated as laws (error strictly under one unit);
- total ordering: no NaN hole (the legacy W8.1 exclusion's
  resolution — the order `le_total` is total BY LAW);
- codec legality: the value rides the EXISTING `u64` wire row —
  the bytes are the bare u64 varint's, byte-for-byte (`Fixed.val_bytes`),
  and round-trip through the value codec untouched (`Fixed.val_codecLegal`).

What `deterministic` FORFEITS (named, per §4.5 — honesty cuts both
ways): hardware-float SPEED (every operation is integer arithmetic
plus a range check) and dynamic range (the scale is fixed at
compile time; magnitudes past `2^64 / scale` units refuse). The
`fast` slot names the opposite trade when it lands.

THE TY-INTEGRATION JUDGMENT: `Ty` does NOT grow a ctor. The profile
is METADATA over the existing ctors — the deterministic float's wire
type IS `.u64` (codec legality is byte-identity with the base
scalar; that is what the promise MEANS), and the type-level
guarantee lives in `Profiled .deterministic (Fixed scale)` in Lean
space, which the codegen lane transports (the review's "transport
them through codegen") without storage cost. A `scaled`-flavored
ctor would break every fold's exhaustiveness (15-patterns #15) and
change the byte-tie artifacts while buying no guarantee the wrapper
does not already carry. The ctor route opens only if the EMITTER
must render profile text into generated code — the codegen lane's
consumer, not the universe's.

The five questions (notes/v3/01-core.md): root = Universe (data —
the profile enum + the profiled carriers, the semantics-side
discipline over the closed scalar codes); carrier = the single-field
phantom wrapper (the erasure IS the carrier's shape) + `Fixed`'s
proof fields (out-of-contract values unconstructible — the
`bounded`/`Fin cap` grade); spine reading = the lift `Fixed.toValue`
into the closed universe's value lane, composing with the existing
Value/Codec spine byte-identically; ladder rung = `rfl`/`decide` over
concrete values (all arithmetic structural Nat, kernel-visible); gate
row = SchemaTests' profile suite (known answers + overflow teeth +
erasure pins + the mandatory negative controls) + the axiom report.

Core-only (imports Kit + SchemaCore.{Ty,Value,Codec} — the cone rule).
-/

import Kit
import SchemaCore.Ty
import SchemaCore.Value
import SchemaCore.Codec

namespace SchemaCore

open Kit.Varint

/-! ## The Profile enum — closed, the honest minimal -/

/-- WHICH semantic a scalar carries. CLOSED (see the module header):
    `fast` (the hardware-float trade, forfeits named) extends with its
    full fold — the compiler drives it — when its consumer lands. -/
inductive Profile where
  /-- The bare scalar's own semantics (the default — an unprofiled
      `u64` reads `plain`). -/
  | plain
  /-- The fixed-point discipline (`Fixed` below): exact checked
      addition, named floor rounding for multiplication, total
      order, codec-legal on the `u64` wire row. -/
  | deterministic
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## The profiled wrapper — the phantom index erases -/

/-- A scalar of base type `α` under profile `p`. The phantom `p` is a
    TYPE INDEX only — the runtime representation is the base scalar
    (ONE field; §4.5's "profiles erase at runtime"). Two profiles of
    one base are DISTINCT types (the `plain` amount and the
    `deterministic` one do not mix — the review's meaning rides the
    type), yet both collapse to the same bytes and the same storage. -/
structure Profiled (p : Profile) (α : Type) where
  /-- The base scalar — the ONLY data. -/
  raw : α

namespace Profiled

/-- THE ERASURE: the wrapper's data is the raw field alone — the
    phantom index carries no runtime content (kernel-checked `rfl`). -/
theorem erase {p : Profile} {α : Type} (s : Profiled p α) : s = ⟨s.raw⟩ := rfl

/-- The erasure as a correspondence value (the Kit grade): the
    profiled scalar and its base are a TRUE bijection — both round
    trips `rfl`. The wire, the storage and the evaluator see the base
    scalar; the profile text is type-level only. -/
def iso (p : Profile) (α : Type) : Kit.Iso (Profiled p α) α where
  to s := s.raw
  inv a := ⟨a⟩
  to_inv := fun _ => rfl
  inv_to := fun _ => rfl

/-- The wrapper's comparison: the raw's comparison (the phantom is
    nowhere in it — the erasure's BEq face). -/
instance {p : Profile} {α : Type} [BEq α] : BEq (Profiled p α) :=
  ⟨fun a b => a.raw == b.raw⟩

end Profiled

/-! ## The deterministic-float model — the fixed-point carrier -/

/-- The fixed-point carrier: the value IS `units`, an integer of the
    scale's units — it represents the rational `units / scale` (the
    `Money Cents` reading: scale 100 counts cents). Both the scale
    AND the u64 wire capacity live in the TYPE (the bounded lane's
    pattern — the `Fin cap` payload discipline): a units value at or
    over `2^64` is UNCONSTRUCTIBLE, so every `Fixed` value is
    codec-legal by construction. At runtime the payload is the one
    Nat — the scale (and the proofs) erase (§4.5). -/
structure Fixed (scale : Nat) where
  /-- The value, in the scale's units. -/
  units : Nat
  /-- The u64 wire capacity, in the type (out-of-contract values
      unconstructible — never range-checked after the fact). -/
  units_lt : units < 2 ^ 64
  /-- The scale's well-formedness: the rational reading needs it
      (a zero scale divides by zero). -/
  scale_pos : 0 < scale

namespace Fixed

/-- The scale accessor — the scale lives in the TYPE (an index), not
    in the value. -/
def scaleOf (_f : Fixed scale) : Nat := scale

/-- The carrier's own erasure: the proofs are Prop — the runtime
    payload is the units alone (kernel-checked). -/
theorem erase (f : Fixed scale) :
    f = ⟨f.units, f.units_lt, f.scale_pos⟩ := rfl

/-- Structural equality on the carrier: the units' equality (the
    proofs ride along). -/
instance : BEq (Fixed scale) := ⟨fun a b => a.units == b.units⟩

/-- The BEq law: equality IS the units' equality (the erasure's
    comparison face — two carriers are equal iff their rationals
    coincide). -/
theorem beq_eq_true_iff (a b : Fixed scale) :
    (a == b) = true ↔ a.units = b.units := by
  show (a.units == b.units) = true ↔ a.units = b.units
  simp

/-! ## The ordering — the total-order promise -/

/-- The order on fixed-point values: the units' order. Total by law
    (below) — the NaN hole the legacy W8.1 exclusion feared cannot
    exist here because the carrier has no NaN. -/
instance : LE (Fixed scale) := ⟨fun a b => a.units ≤ b.units⟩

/-- The order decides (the ladder rung: every checkable fact over
    concrete values decides in the kernel). -/
instance (a b : Fixed scale) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.units ≤ b.units))

/-- THE ORDER LAW: the order is total — every pair compares (no NaN
    hole, the codec-legal order the legacy map form needed). -/
theorem le_total (a b : Fixed scale) : a ≤ b ∨ b ≤ a :=
  show a.units ≤ b.units ∨ b.units ≤ a.units from Nat.le_total _ _

/-- The order REFLECTS the rational order (same scale): `n/scale ≤
    m/scale ↔ n ≤ m` for scale > 0 — definitional here. -/
theorem le_iff (a b : Fixed scale) : a ≤ b ↔ a.units ≤ b.units := Iff.rfl

/-! ## The checked arithmetic — the overflow honesty -/

/-- Checked addition: the units' sum — EXACT (no rounding; same scale
    adds units). Overflows REFUSE (`none`) at the wire capacity,
    never wrap silently — the hardware `+`'s lie is refused, not
    emulated. -/
def add? (a b : Fixed scale) : Option (Fixed scale) :=
  if h : a.units + b.units < 2 ^ 64 then
    some ⟨a.units + b.units, h, a.scale_pos⟩
  else none

/-- Checked multiplication: the exact rational product is
    `(a.units / scale) * (b.units / scale) = (a.units * b.units) /
    scale²`; re-expressed at the SAME scale it is
    `(a.units * b.units) / scale` — which ROUNDS. The rounding is
    NAMED: floor (Nat's truncating division — the values are
    nonnegative, so truncation IS floor). Overflows refuse at the
    wire capacity, never wrap. -/
def mul? (a b : Fixed scale) : Option (Fixed scale) :=
  if h : a.units * b.units / scale < 2 ^ 64 then
    some ⟨a.units * b.units / scale, h, a.scale_pos⟩
  else none

/-- THE ADD LAW (exactness): a successful add's units are the sum —
    no rounding, no wrap (the refusal teeth carry the overflow case). -/
theorem add?_some {scale : Nat} {a b : Fixed scale} {c : Fixed scale}
    (h : a.add? b = some c) : c.units = a.units + b.units := by
  simp only [add?] at h
  split at h
  · exact (congrArg (fun s : Fixed scale => s.units) (Option.some.inj h)).symm
  · simp at h

/-- THE OVERFLOW TEETH: add refuses exactly at the capacity —
    `none` iff the units' sum reaches `2^64` (never a wrap). -/
theorem add?_none_iff {scale : Nat} (a b : Fixed scale) :
    a.add? b = none ↔ ¬ (a.units + b.units < 2 ^ 64) := by
  simp only [add?]
  split <;> simp_all

/-- THE MUL LAW (the named rounding): a successful mul's units are
    the floor of the exact product's units —
    `c.units = (a.units * b.units) / scale` — and the floor bounds
    hold: the result understates by strictly less than one unit
    (`c.units * scale ≤ a.units * b.units < (c.units + 1) * scale`),
    i.e. the represented rational misses the exact product by
    strictly less than `1 / scale`. -/
theorem mul?_some {scale : Nat} {a b : Fixed scale} {c : Fixed scale}
    (h : a.mul? b = some c) :
    c.units = a.units * b.units / scale
      ∧ c.units * scale ≤ a.units * b.units
      ∧ a.units * b.units < (c.units + 1) * scale := by
  simp only [mul?] at h
  split at h
  · next hg =>
      have hunit : c.units = a.units * b.units / scale :=
        (congrArg (fun s : Fixed scale => s.units) (Option.some.inj h)).symm
      refine ⟨hunit, ?_, ?_⟩
      · rw [hunit]
        exact Nat.div_mul_le_self _ _
      · rw [hunit]
        have hmod : a.units * b.units % scale < scale :=
          Nat.mod_lt _ a.scale_pos
        calc a.units * b.units
            = scale * (a.units * b.units / scale) + a.units * b.units % scale :=
              (Nat.div_add_mod _ _).symm
          _ < scale * (a.units * b.units / scale) + scale :=
              Nat.add_lt_add_left hmod _
          _ = (a.units * b.units / scale + 1) * scale := by
              rw [Nat.add_mul, Nat.one_mul,
                Nat.mul_comm scale (a.units * b.units / scale)]
  · simp at h

/-- THE OVERFLOW TEETH (mul): mul refuses exactly when the rounded
    result reaches the capacity — never a wrap. -/
theorem mul?_none_iff {scale : Nat} (a b : Fixed scale) :
    a.mul? b = none ↔ ¬ (a.units * b.units / scale < 2 ^ 64) := by
  simp only [mul?]
  split <;> simp_all

/-! ## The Value/Codec integration — the profile rides the EXISTING u64 -/

/-- The lift into the closed universe's value lane: the profiled
    scalar rides the EXISTING `.u64` ctor (the Ty-integration
    judgment — no new ctor, the wire type IS the base scalar's). -/
def toValue (f : Fixed scale) : Value .u64 :=
  .u64 (UInt64.ofNat f.units)

/-- The lift is faithful (the eval side). -/
theorem toValue_eval (f : Fixed scale) :
    f.toValue.eval = UInt64.ofNat f.units := rfl

/-- The u64 re-read of a units value is the value (the capacity
    proof's whole job — the codec-legality's hinge). -/
theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt h

/-- CODEC LEGALITY, the bytes face: the profiled scalar's wire bytes
    are the BARE u64 varint's — the profile text is nowhere in the
    bytes (the phantom erases on the wire too; the negative control
    in SchemaTests pins the teeth). -/
theorem val_bytes (f : Fixed scale) :
    encVal .u64 f.toValue = encVarNat f.units := by
  show encVarNat (UInt64.ofNat f.units).toNat = encVarNat f.units
  rw [ofNat_toNat f.units_lt]

/-- CODEC LEGALITY, the round trip: the lifted value decodes from its
    encoding plus ANY suffix, exactly — a citation of the value
    codec's master law (the profile composes with the existing wire
    spine for free; nothing new to prove). -/
theorem val_codecLegal (f : Fixed scale) (rest : List UInt8) :
    decVal .u64 (encVal .u64 f.toValue ++ rest) = some (f.toValue, rest) :=
  decVal_encVal_append .u64 f.toValue rest

end Fixed

/-- The `Money USD Cents` shape (§4.5's example): a deterministic
    fixed-point scalar at the named scale — the profile AND the units
    live in the type; at runtime the value is the units alone. -/
abbrev Money (scale : Nat) := Profiled .deterministic (Fixed scale)

/-- The review's `amount : UInt64` note as a type: the plain profile
    NAMES the meaning without changing the runtime — a distinct type
    from the bare scalar AND from every other profile, erasing to the
    same field. -/
abbrev Labeled (α : Type) := Profiled .plain α

/-! ## The coverage pins (kernel level, the known answers) -/

-- The Money-cents shape: 150¢ + 275¢ = 425¢, EXACT.
example : (⟨150, by decide, by decide⟩ : Fixed 100).add?
    (⟨275, by decide, by decide⟩ : Fixed 100)
    = some (⟨425, by decide, by decide⟩ : Fixed 100) := rfl

-- The named rounding: 33¢ × 33¢ = 10.89 units² — floor to 10 (NOT 11).
example : (⟨33, by decide, by decide⟩ : Fixed 100).mul?
    (⟨33, by decide, by decide⟩ : Fixed 100)
    = some (⟨10, by decide, by decide⟩ : Fixed 100) := rfl

-- The exact square: 50¢ × 50¢ = 25¢ — no rounding needed, exactly.
example : (⟨50, by decide, by decide⟩ : Fixed 100).mul?
    (⟨50, by decide, by decide⟩ : Fixed 100)
    = some (⟨25, by decide, by decide⟩ : Fixed 100) := rfl

-- THE OVERFLOW TEETH: max units + 1 REFUSES (never wraps to zero).
example : (⟨2 ^ 64 - 1, by decide, by decide⟩ : Fixed 100).add?
    (⟨1, by decide, by decide⟩ : Fixed 100) = none := rfl

-- The scale is type-level data, not runtime.
example : (⟨425, by decide, by decide⟩ : Fixed 100).scaleOf = 100 := rfl

-- The wrapper's erasure at runtime: the phantom is nowhere.
example : (⟨(7 : UInt64)⟩ : Profiled .plain UInt64).raw = 7 := rfl
example : (Profiled.iso .plain UInt64).to ((Profiled.iso .plain UInt64).inv 7) = 7 := rfl

end SchemaCore

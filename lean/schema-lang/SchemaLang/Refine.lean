/-
# SchemaLang.Refine — ranged refinements (the W8.11 order's lane)

The order (the runbook's ranged-refinements line): "`u16 @range`-style:
emitted validators + decide-discharged obligations". The surface is a
NUMERIC type + a range constraint (`u32 0..100` — an inclusive
`lo..hi` over an existing scalar); the canon row it instantiates is
"floored stock / budget / quota = a canonically-ordered value with
monus (nonneg BY CONSTRUCTION)" — the monus lemma set lands here.

NO new `Ty` constructor — the closed-universe rule costs the emitters
NOTHING. `Ty.lean`'s header omits refinement predicates DELIBERATELY
("the schema-indexed package owns `{x // P x}`; v1 payloads are plain
types"): a ranged type is METADATA over an existing scalar, so WIT /
Rust / snapshot render the BASE type unchanged (byte-tie by
construction); the CONSTRAINT is a new consumer of the existing
surfaces, not a new shape.

## The discharge ladder, per case (the order decides — not a
## dependent pair)

The order's default names TWO backends (emitted validators +
decide-discharged obligations) and NO dependent pair: construction-
time unrepresentability (a `Subtype`-refined `Value`) would re-thread
EVERY consumer of `Value` for one lane's benefit, and the boundary is
where the constraint's enforcement belongs (a range is DATA, checked
at ingress — the `RowVals` discipline). So the ladder is:

1. **Spec construction** (`Range.mk?`): the checked smart constructor
   — an in-range value passes, an out-of-range value refuses (BOTH
   directions pinned in Tests). A check, not unrepresentability.
2. **Obligation** (`RangeCheck.discharge`): the range check as a
   `decidableNow`-tier obligation (W7.1p2's backend — a concrete value
   against concrete bounds is a decidable claim; the kernel's `decide`
   discharges; `none` is the loud gap). The WORD lane
   (`Range.wordClaim32`) restates the claim over `BitVec` so the
   `bv_decide` backend discharges it (the order's named backend; the
   LRAT certificate is kernel-checked) — the two lanes AGREE, proved
   (`wordClaim32_iff`).
3. **Boundary** (the validator lane): the constraint lowers to the
   EXISTING `VExpr` fragment (`!(lo > x) && !(x > hi)` — `≥`/`≤` are
   the double-negation form, exact on Bool) and renders through the
   SHARED `Emit.Expr` lowering — the same emitted-validator text the
   invariant lane emits, no new emitter machinery. A misspelled field
   fails at elaboration (the `HasCol` gate rides).

## The monus tie (the canon row)

A floored stock's composition is monus — the saturating subtraction:
spending `b` from stock `a` yields `a ⊖ b`, nonneg BY CONSTRUCTION
(the guard IS the construction; machine sub would WRAP — the witness
`monusU64 5 9 = 0`, not the wrap, is pinned in Tests). The closure law
`Range.inRange_monus`: a monus result STAYS in range whenever the
floor is ≤ 0 — the range check after a spend needs no re-check.

Ownership: this module (the refinement lane). Deliberate exclusions:
no signed-base validator lane (the VExpr fragment is u64-scalar —
`Range.u64Bounds?` refuses a bound that is not u64-expressible, LOUD);
no float/string bases (`valInt?` is `none` there — a refinement over a
non-ordered base is unrepresentable at the projection); no new
obligation tier (the kit's five-tier ladder governs); signed-base
VALIDATOR emission joins when a consumer needs it (a VExpr width
extension — Validate's closed fragment governs, not this module).
-/

module

public import Lean
public import SchemaLang.Validate
public import CodegenCore

@[expose] public section

namespace SchemaLang

/-! ## The range -/

/-- A range over a numeric base: INCLUSIVE bounds (`u32 0..100` =
    `⟨.u32, 0, 100⟩`). Metadata over an EXISTING `Ty` — the base is
    the type every emitter already renders; the bounds are `Int`
    literals so signed bases stay expressible at the spec level. -/
structure Range where
  /-- The refined base type (an int scalar for every operation below). -/
  base : Ty
  /-- The inclusive lower bound. -/
  lo : Int
  /-- The inclusive upper bound. -/
  hi : Int
deriving Repr, BEq, DecidableEq, Inhabited

/-- The numeric projection: the int scalars' EXACT `Int` value (u64
    fits — Lean's `Int` is arbitrary precision; no wrap, the check is
    at the spec level). Non-numeric bases have no projection: a
    refinement over string/bytes/composites is unrepresentable here
    (`none` — the type-level gate). -/
def Range.valInt? : (t : Ty) → Value t → Option Int
  | .u8, .u8 v => some v.toNat
  | .u16, .u16 v => some v.toNat
  | .u32, .u32 v => some v.toNat
  | .u64, .u64 v => some v.toNat
  | .i8, .i8 v => some v.toInt
  | .i16, .i16 v => some v.toInt
  | .i32, .i32 v => some v.toInt
  | .i64, .i64 v => some v.toInt
  | _, _ => none

/-- In range: the projection within the inclusive bounds. A value
    without a projection (non-numeric base) refuses — `false`, the
    check never silently passes what it cannot read. -/
def Range.inRange (r : Range) (v : Value r.base) : Bool :=
  match Range.valInt? r.base v with
  | some i => r.lo ≤ i && i ≤ r.hi
  | none => false

/-- THE CONSTRUCTION GATE: in-range passes, out-of-range refuses.
    The iff (the two theorems below) is the two-direction pin: accept
    EXACTLY the in-range values (Tests execute both arms on both
    sides of the bounds). -/
def Range.mk? (r : Range) (v : Value r.base) : Option (Value r.base) :=
  if r.inRange v then some v else none

/-- Completeness: an in-range value is accepted. -/
theorem Range.mk?_some_of_inRange (r : Range) (v : Value r.base)
    (h : r.inRange v = true) : r.mk? v = some v := by
  simp [Range.mk?, h]

/-- Soundness: an accepted value IS in range (an acceptance never
    smuggles an out-of-range one). -/
theorem Range.inRange_of_mk?_some (r : Range) (v : Value r.base)
    (h : r.mk? v = some v) : r.inRange v = true := by
  simp [Range.mk?] at h
  exact h

/-- An out-of-range value is refused (the loud `none`). -/
theorem Range.mk?_none_of_not_inRange (r : Range) (v : Value r.base)
    (h : r.inRange v = false) : r.mk? v = none := by
  simp [Range.mk?, h]

/-! ## The obligation tier (W7.1p2's decidableNow backend) -/

/-- A range check as an obligation payload: the range, the value under
    it, and the NAME the obligation label carries (the refined field's
    name at the call site). -/
structure RangeCheck where
  /-- The obligation label (the refined field / value's name). -/
  name : String
  /-- The range. -/
  r : Range
  /-- The value checked. -/
  v : Value r.base

/-- The claim: the value IS in range. -/
def RangeCheck.claim (c : RangeCheck) : Prop := c.r.inRange c.v = true

/-- The claim is decidable: `inRange` computes to a `Bool`. -/
instance (c : RangeCheck) : Decidable c.claim := by
  unfold RangeCheck.claim; infer_instance

/-- The obligation: `decidableNow` tier (the W7.1p2 backend — a
    concrete value against concrete bounds is a decidable claim; the
    kernel's `decide` is the decision procedure). Provenance is the
    lane's name (no registry row behind a hand check). -/
def RangeCheck.obligation (c : RangeCheck) : CodegenCore.Obligation RangeCheck :=
  { label := c.name
  , tier := .decidableNow
  , payload := c
  , provenance := `SchemaLang.Refine }

/-- The obligation's tier IS the lane's (the mis-wire check, as data). -/
theorem RangeCheck.obligation_tier (c : RangeCheck) :
    c.obligation.tier = .decidableNow := rfl

/-- THE DISCHARGE (the decidableNow backend's shape —
    `SchemaObligation.discharge`'s arm): fires `.decided true` on a
    TRUE claim; `none` on false — no fabricated evidence, the loud
    gap is a REFUSAL, not a fake pass. -/
def RangeCheck.discharge (c : RangeCheck) :
    Option CodegenCore.Obligation.Evidence :=
  match decide c.claim with
  | true => some (.decided true)
  | false => none

/-- SOUNDNESS: a fired discharge means the value IS in range (the
    kernel's `decide` validated it — `of_decide_eq_true`; no new trust
    base). -/
theorem RangeCheck.discharge_sound (c : RangeCheck)
    (h : c.discharge = some (.decided true)) : c.claim := by
  unfold RangeCheck.discharge at h
  cases hd : decide c.claim with
  | true => exact of_decide_eq_true hd
  | false => rw [hd] at h; simp at h

/-- COMPLETENESS: a true claim fires the backend (the discharge is not
    vacuous). -/
theorem RangeCheck.discharge_of_claim (c : RangeCheck) (h : c.claim) :
    c.discharge = some (.decided true) := by
  unfold RangeCheck.discharge
  rw [decide_eq_true h]

/-! ## The word lane (the order's bv_decide backend) -/

/-- A u32 value's Nat is within the width (the bridge's side
    condition; core carries it per type). -/
theorem UInt32.toNat_lt (v : UInt32) : v.toNat < 2^32 :=
  UInt32.toNat_lt_size v

/-- The word lane's claim: the value AS A 32-BIT WORD is within the
    hi bound's word (unsigned — the u32 lane; the two's-complement
    word lane is the signed follow-up). Stated over `BitVec` so the
    `bv_decide` backend discharges it (the order's named backend; the
    LRAT certificate is kernel-checked). Decidable so the TESTS can
    `decide` the concrete pins (the tactic is the backend at work). -/
def Range.wordClaim32 (hi : Nat) (v : UInt32) : Prop :=
  BitVec.ule (BitVec.ofNat 32 v.toNat) (BitVec.ofNat 32 hi)

instance (hi : Nat) (v : UInt32) : Decidable (Range.wordClaim32 hi v) := by
  unfold Range.wordClaim32; infer_instance

/-- The two lanes AGREE: the word claim is EXACTLY the Int-level
    in-range check's upper half (u32 values are nonneg, so the lower
    half is `0 ≤ i` — trivially true). The bridge is `rw`-level (core
    BitVec lemmas; no new trust base). -/
theorem Range.wordClaim32_iff (hi : Nat) (v : UInt32) (hh : hi < 2^32) :
    Range.wordClaim32 hi v ↔ v.toNat ≤ hi := by
  unfold Range.wordClaim32
  rw [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt v.toNat_lt, Nat.mod_eq_of_lt hh]

/-- The in-range stock value's word obligation: FIRES (`bv_decide` —
    the kernel-checked LRAT certificate). -/
theorem Range.wordClaim32_accept :
    Range.wordClaim32 100 50 := by
  show BitVec.ule (BitVec.ofNat 32 50) (BitVec.ofNat 32 100)
  bv_decide

/-- The out-of-range stock value's word obligation: REFUSES (the
    negative control — a backend that fired both ways would be a
    rubber stamp). -/
theorem Range.wordClaim32_refuse :
    ¬ Range.wordClaim32 100 150 := by
  rw [Range.wordClaim32_iff (hi := 100) (v := 150) (by decide)]
  decide

/-! ## The validator lane (the generated boundary check) -/

/-- The bounds' u64-lane projection (`none` = not u64-expressible: a
    negative `hi`, an over-wide bound — the lane refuses LOUD, it does
    not clamp a lie). A negative `lo` IS expressible: on a u64 field
    every value is ≥ 0 ≥ lo, so the floor is VACUOUS and the
    projection floors it at 0 (the emitted check is the truth it was
    going to compute anyway). Widths ride `UInt64.size` — the same
    constant the `toNat` round-trip lemmas are stated over. -/
def Range.u64Bounds? (r : Range) : Option (UInt64 × UInt64) :=
  if r.lo < (UInt64.size : Int) ∧ 0 ≤ r.hi ∧ r.hi.toNat < UInt64.size then
    some ((max r.lo 0).toNat.toUInt64, r.hi.toNat.toUInt64)
  else none

/-- The check's Bool kernel at the u64 lane: the double-negation
    spelling computes EXACTLY the two-sided comparison — `!(lo > x) &&
    !(x > hi)` IS `lo ≤ x && x ≤ hi` (the raw evaluator's 0/1
    arithmetic: a failed half zeroes the product, the `== 1` verdict
    passes only both). -/
theorem Range.rawCheck_u64 (lo hi x : UInt64) :
    (((1 - boolToU64 (lo > x)) * (1 - boolToU64 (x > hi))) == 1)
      = (lo ≤ x && x ≤ hi) := by
  have k : ∀ (b1 b2 : Bool),
      (((1 - boolToU64 b1) * (1 - boolToU64 b2)) == 1) = (!b1 && !b2) := by
    intros b1 b2
    cases b1 <;> cases b2 <;> rfl
  have nlt : ∀ (a b : UInt64),
      (!(Decidable.decide (a < b))) = Decidable.decide (b ≤ a) := by
    intros a b
    cases hb : Decidable.decide (a < b) with
    | true =>
        have hlt : a < b := decide_eq_true_iff.mp hb
        exact (decide_eq_false
          (UInt64.not_le (a := b) (b := a) |>.mpr hlt)).symm
    | false =>
        have hn := decide_eq_false_iff_not.mp hb
        rw [UInt64.lt_iff_toNat_lt] at hn
        exact (decide_eq_true
          (UInt64.le_iff_toNat_le.mpr (by omega))).symm
  rw [k, nlt, nlt]

/-- The bounds' projection AGREES with the spec-level check: the u64
    comparison pair decides the same fact the Int bounds decide (the
    vacuous-floor and width side conditions are exactly what
    `u64Bounds?`'s guard checks; the negative floor's case is `0 ≤
    every u64`). -/
theorem Range.bounds_inRange_u64 (loI hiI : Int) (lo hi x : UInt64)
    (rb : Range.u64Bounds? ⟨.u64, loI, hiI⟩ = some (lo, hi)) :
    (lo ≤ x && x ≤ hi) = Range.inRange ⟨.u64, loI, hiI⟩ (Value.u64 x) := by
  simp only [Range.u64Bounds?] at rb
  split at rb
  · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at rb
      obtain ⟨rlo, rhi⟩ := rb
      subst rlo
      subst rhi
      simp only [Range.inRange, Range.valInt?, UInt64.le_iff_toNat_le,
        UInt64.toNat_ofNat_of_lt' hc.2.2]
      rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true,
        decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff,
        decide_eq_true_iff]
      have hh : ((hiI.toNat : Int)) = hiI := Int.toNat_of_nonneg hc.2.1
      have h0 : ((0:UInt64)).toNat = 0 := rfl
      rcases Int.lt_trichotomy loI 0 with hneg | hzero | hpos
      · -- negative floor: the max is 0, and loI ≤ 0 ≤ every u64
        have hmt : (((max loI 0 : Int).toNat : Nat).toUInt64 : UInt64) = 0 := by
          have hmx : max loI 0 = (0 : Int) := by
            rw [Int.max_def, if_pos (by omega)]
          rw [hmx]
          rfl
        rw [hmt, h0]
        omega
      · -- zero floor: the max IS loI (= 0), same fact both worlds
        rw [hzero]
        have hz : (((max 0 0 : Int).toNat : Nat).toUInt64 : UInt64).toNat = 0 := rfl
        rw [hz]
        omega
      · -- positive floor: the max IS loI, exact in both worlds
        have hmt : (((max loI 0 : Int).toNat : Nat).toUInt64 : UInt64)
            = loI.toNat.toUInt64 := by
          have hmx : max loI 0 = loI := by
            rw [Int.max_def, if_neg (by omega)]
          rw [hmx]
        rw [hmt]
        have hlo' : ((loI.toNat : Int)) = loI :=
          Int.toNat_of_nonneg (by omega)
        have hlt' : loI.toNat < UInt64.size := by omega
        rw [UInt64.toNat_ofNat_of_lt' hlt']
        omega
  · simp at rb

/-- The range check as a VExpr over a u64 field: `!(lo > x) && !(x >
    hi)` — `≥`/`≤` spelled in the CLOSED fragment (Validate owns the
    ctor set; no new node here — a range is not a new expression
    shape, it is a CONJUNCTION of the comparisons the fragment
    already has). The misspelled field fails at ELABORATION (the
    `HasCol` gate rides the `colOf` builder). -/
def Range.vexprU64 (lo hi : UInt64) (n : String) {s : List Field}
    [h : HasCol s n .u64] : VExpr s .bool :=
  .and (.not (.gt (.lit lo) (.colOf n)))
       (.not (.gt (.colOf n) (.lit hi)))

/-- The range's VExpr, when the bounds are u64-expressible (`none` =
    the loud refusal — the emit lane does not emit a check it cannot
    state). -/
def Range.vexpr? (r : Range) (n : String) {s : List Field}
    [h : HasCol s n .u64] : Option (VExpr s .bool) :=
  r.u64Bounds?.map fun (lo, hi) => Range.vexprU64 lo hi n

/-- THE AGREEMENT PIN: the validator lane's verdict on a row IS the
    construction lane's in-range check on the field's value — one
    fact, two readings, proved. The emitted validator and the
    construction gate cannot disagree. -/
theorem Range.validates_vexpr_u64 (loI hiI : Int) (lo hi : UInt64)
    (n : String) {s : List Field} [h : HasCol s n .u64] (row : RowVals s)
    (x : UInt64) (rowU : h.path.get row = Value.u64 x)
    (rb : Range.u64Bounds? ⟨.u64, loI, hiI⟩ = some (lo, hi)) :
    validates (Range.vexprU64 lo hi n) row
      = Range.inRange ⟨.u64, loI, hiI⟩ (Value.u64 x) := by
  rw [← Range.bounds_inRange_u64 loI hiI lo hi x rb]
  simp only [validates, evalB, Range.vexprU64, evalRaw, VExpr.colOf, rowU]
  rw [Range.rawCheck_u64]

/-! ## The monus tie (the canon row) -/

/-- monus — the saturating subtraction (the canon row's "floored
    stock / budget / quota" composition). The GUARD is the
    construction: machine sub would WRAP (the Tests pin `monusU64 5 9
    = 0`, not the wrap). -/
def Range.monusU64 (a b : UInt64) : UInt64 := if a ≥ b then a - b else 0

/-- monus never exceeds the stock (the range's UPPER half survives a
    spend: the result only goes DOWN). -/
theorem Range.monusU64_le (a b : UInt64) : Range.monusU64 a b ≤ a := by
  show (if a ≥ b then a - b else (0:UInt64)) ≤ a
  rw [UInt64.le_iff_toNat_le]
  split
  · next h =>
      rw [UInt64.toNat_sub_of_le _ _ h]
      exact Nat.sub_le _ _
  · next =>
      have h0 : ((0:UInt64)).toNat = 0 := rfl
      rw [h0]
      exact Nat.zero_le _

/-- THE CLOSURE LAW (the canon row's point): a spend from an in-range
    floored stock STAYS in range — the floor is nonneg BY CONSTRUCTION
    (monus cannot go below 0, and `lo ≤ 0` reads it), and the ceiling
    only loosens (the result is ≤ the stock, which was ≤ hi). The
    range check after a spend needs no re-check. -/
theorem Range.inRange_monus (loI hiI : Int) (a b : UInt64)
    (ha : Range.inRange ⟨.u64, loI, hiI⟩ (Value.u64 a)) (hlo : loI ≤ 0) :
    Range.inRange ⟨.u64, loI, hiI⟩ (Value.u64 (Range.monusU64 a b)) := by
  simp only [Range.inRange, Range.valInt?, Bool.and_eq_true,
    decide_eq_true_iff] at ha ⊢
  obtain ⟨halo, hahi⟩ := ha
  refine ⟨?_, ?_⟩
  · -- the floor: monus ≥ 0 ≥ loI
    have h1 := Range.monusU64_le a b
    rw [UInt64.le_iff_toNat_le] at h1
    omega
  · -- the ceiling: monus ≤ a ≤ hiI
    have h1 := Range.monusU64_le a b
    rw [UInt64.le_iff_toNat_le] at h1
    omega

end SchemaLang

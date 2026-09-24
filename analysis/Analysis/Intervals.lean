/-
# Analysis.Intervals — the worked domain: bounded intervals over ℤ

Owned by: the analysis agent (the mandate tree, `analysis/`).
Driving decisions: the reviews' verification-dimension addition (the
classic abstract domain — the future consumers are the overflow
analysis, the bounded-Nat lane, the fuel budgets) + notes/v3/01-core.md
§4 (the Abstraction grade: this domain's γ IS the kit's `conc` — the
instance rides `Analysis.Basic.intervalDomain` + `toAbstraction`) +
notes/v3/01-core.md §3 (the honest trichotomy: PROVED / REFUTED /
UNKNOWN — the escape discipline below) + notes/v3/15-patterns.md #1.

## The domain's exact shape (and the honest exclusions)

- `Iv`: endpoint pairs in ℤ, NO invariant. `γ iv c := iv.lo ≤ c ∧ c ≤
  iv.hi`. An interval with `lo > hi` concretizes to NOTHING — the
  empty interval is in the type honestly (γ is just false everywhere);
  no junk-freeing quotient, no invariant to maintain.
- The transfers: `point` (the abstraction function α — total: γ
  (point c) c holds for EVERY c), `negT` and `addT` (sound,
  total — the hull of an add may leave the cage, which is SOUND: the
  hull still covers the concrete sum), and `join` (the hull, with the
  cover law in both one-sided forms).
- THE CAGE: the finite lattice lives in the CAGED sub-universe —
  intervals whose endpoints lie in `[-B, B]` for the analysis's
  declared bound `B` (i32 bounds, Nat bounds, fuel budgets). The cage
  is a DISCIPLINE (lemmas over `Caged`), not an invariant: the
  transfers are sound over all of ℤ, and the cage is where termination
  and the overflow verdict live.
- THE HONEST TRICHOTOMY (01-core §3, the corrected R11 discipline):
  for caged operands, `addT` answers three ways — hull caged ⇒ every
  concrete sum is caged (PROVED safe); hull entirely below/above the
  cage ⇒ every concrete sum escapes (PROVED overflow, both directions
  proved); hull straddling the boundary ⇒ the imprecision case, and
  the framework says NOTHING (UNKNOWN — never silently a verdict).
- THE FINITE-HEIGHT DISCIPLINE (the widening's honesty): caged
  nonempty intervals have width in `[0, 2B]`, and strict ascent
  strictly increases width (`width_lt`) — an ascending chain of caged
  intervals stabilizes within 2B+1 strict steps. The doctrine's
  honesty about fixpoints: an iteration that has not yet stabilized is
  UNKNOWN, never a verdict; the fuel-bounded iterator lands with its
  first consumer (the leftover rule).
- Named exclusion — unbounded intervals (±∞ endpoints): the type here
  is deliberately finite-height; a top-interval covering all of ℤ
  would break the width bound. Domains needing it extend with a `Top`
  constructor and their own termination law.
- Named exclusion — multiplication, division: non-linearity needs its
  own transfer laws (and multiplication's soundness is NOT the hull of
  the endpoint products without the sign case split). Each lands with
  its named law.

The five questions (notes/v3/01-core.md):
- root: the crossing — the Universe side's concrete semantics (ℤ
  arithmetic) approximated by the Abstraction grade's canonical
  instance.
- carrier grade: Abstraction — `intervalDomain : AbstractDomain Int Iv`
  + `toAbstraction` at `α := point`.
- spine reading: none — the analysis lane's first worked domain.
- ladder rung: the transfer soundness fields are discharged by small
  hand theorems (01 §7's preferred foundation), cited by the domain
  instance's fields.
- gate row: none yet — Analysis is outside Gates.Packages' gated set;
  AnalysisTests.Axioms pins the axiom cones.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Analysis.Basic

namespace Analysis

/-! ## The interval type + the concretization -/

/-- The abstract value: an endpoint pair in ℤ. NO invariant — an
    interval with `lo > hi` concretizes to nothing (the empty
    interval), honestly. -/
structure Iv where
  /-- The lower endpoint. -/
  lo : Int
  /-- The upper endpoint. -/
  hi : Int
  deriving DecidableEq, BEq, Repr, Inhabited

/-- THE concretization: membership. `γ iv c` — concrete `c` is OF
    abstract `iv`. -/
abbrev Iv.mem (iv : Iv) (c : Int) : Prop := iv.lo ≤ c ∧ c ≤ iv.hi

/-- The γ-order at the interval domain: `Analysis.AbsLe` AT `Iv.mem` —
    the one spelling (no per-domain re-roll). -/
def Iv.le (a b : Iv) : Prop := AbsLe Iv.mem a b

/-- The interval's width — the finite-height discipline's measure
    (see `width_lt`, `width_bounds`). -/
def Iv.width (iv : Iv) : Int := iv.hi - iv.lo

/-- The γ-order's endpoint reading: for a nonempty `a`, `a ⊑ b` says
    `b`'s endpoints extend `a`'s. (Vacuous for an empty `a` — the
    honest reading of the order: the empty interval is below all.) -/
theorem Iv.le_endpoints {a b : Iv} (hne : a.lo ≤ a.hi) (h : Iv.le a b) :
    b.lo ≤ a.lo ∧ a.hi ≤ b.hi :=
  ⟨(h a.lo ⟨Int.le_refl a.lo, hne⟩).1, (h a.hi ⟨hne, Int.le_refl a.hi⟩).2⟩

theorem Iv.eq_of_lo_hi {a b : Iv} (h1 : a.lo = b.lo) (h2 : a.hi = b.hi) :
    a = b := by
  cases a; cases b
  simp_all

/-! ## The transfers -/

/-- The abstraction function α: the point interval. TOTAL — γ
    (point c) c holds for every c (the abstraction never refuses). -/
def point (c : Int) : Iv := ⟨c, c⟩

/-- The negation transfer: `-[lo, hi] = [-hi, -lo]`. -/
def negT (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩

/-- The addition transfer: the endpointwise sum (Minkowski). The hull
    may leave the cage — SOUND (it still covers the concrete sum); the
    cage discipline reads the escape off it (the trichotomy below). -/
def addT (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- A deliberately WRONG addition (the second endpoint DROPS `b.hi`):
    exists only as the teeth's specimen — `badAdd_unsound` shows the
    soundness field REFUSES it (the type-level refusal). -/
def badAdd (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi - b.hi⟩

/-- The join: the endpointwise hull — the widening point. -/
def join (a b : Iv) : Iv := ⟨min a.lo b.lo, max a.hi b.hi⟩

/-! ## The soundness theorems (the transfer fields' content) -/

theorem point_sound (c : Int) : (point c).mem c :=
  ⟨Int.le_refl c, Int.le_refl c⟩

theorem negT_sound : ∀ (a : Iv) (c : Int), a.mem c → (negT a).mem (-c) := by
  intro a c h
  show -a.hi ≤ -c ∧ -c ≤ -a.lo
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

theorem addT_sound : ∀ (a b : Iv) (c₁ c₂ : Int), a.mem c₁ → b.mem c₂ →
    (addT a b).mem (c₁ + c₂) := by
  intro a b c₁ c₂ h1 h2
  show a.lo + b.lo ≤ c₁ + c₂ ∧ c₁ + c₂ ≤ a.hi + b.hi
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  exact ⟨by omega, by omega⟩

theorem join_cover_left : ∀ (a b : Iv) (c : Int), a.mem c → (join a b).mem c := by
  intro a b c h
  show min a.lo b.lo ≤ c ∧ c ≤ max a.hi b.hi
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

theorem join_cover_right : ∀ (a b : Iv) (c : Int), b.mem c → (join a b).mem c := by
  intro a b c h
  show min a.lo b.lo ≤ c ∧ c ≤ max a.hi b.hi
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

theorem join_idem (a : Iv) : join a a = a := by
  cases a
  simp [join]

/-! ## The domain instance -/

/-- The interval domain: ℤ's negation + addition approximated by the
    bounded intervals. The soundness fields cite the theorems above —
    the construction refuses any unsound transfer. -/
def intervalDomain : AbstractDomain Int Iv where
  γ := Iv.mem
  unC := fun c => -c
  binC := fun c₁ c₂ => c₁ + c₂
  unA := ⟨negT, negT_sound⟩
  binA := ⟨addT, addT_sound⟩
  join := join
  join_cover_left := join_cover_left
  join_cover_right := join_cover_right

/-- The bridge to the kit's ONE carrier (01-core §4): the interval
    domain's γ IS the `Abstraction`'s `conc`; `point` is the
    abstraction function; its covering proof supplies the `sound`
    field — cited, not re-rolled. -/
def intervalAbstraction : Kit.Abstraction Int Iv :=
  intervalDomain.toAbstraction point point_sound

/-! ## The cage — the declared bound, the finite lattice -/

/-- A concrete value is caged: inside `[-B, B]` — the values the
    analysis's consumer cares about (i32 bounds, Nat bounds, fuel). -/
abbrev CagedValue (B : Int) (c : Int) : Prop := -B ≤ c ∧ c ≤ B

/-- An abstract value is caged: both endpoints in `[-B, B]`. The
    finite lattice's universe is the caged (nonempty) intervals. -/
abbrev Caged (B : Int) (iv : Iv) : Prop := -B ≤ iv.lo ∧ iv.hi ≤ B

/-- The cage's top: the whole cage as one interval. -/
def top (B : Int) : Iv := ⟨-B, B⟩

theorem top_caged (B : Int) : Caged B (top B) := by
  show -B ≤ -B ∧ B ≤ B
  exact ⟨Int.le_refl _, Int.le_refl _⟩

theorem top_covers (B : Int) : ∀ c, CagedValue B c → (top B).mem c := by
  intro c h
  show -B ≤ c ∧ c ≤ B
  exact h

theorem point_caged_iff (B : Int) (c : Int) :
    Caged B (point c) ↔ CagedValue B c := by
  show (-B ≤ c ∧ c ≤ B) ↔ (-B ≤ c ∧ c ≤ B)
  exact Iff.rfl

theorem negT_caged {B : Int} {a : Iv} (h : Caged B a) : Caged B (negT a) := by
  show -B ≤ -a.hi ∧ -a.lo ≤ B
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

theorem join_caged {B : Int} {a b : Iv} (h1 : Caged B a) (h2 : Caged B b) :
    Caged B (join a b) := by
  show -B ≤ min a.lo b.lo ∧ max a.hi b.hi ≤ B
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  exact ⟨by omega, by omega⟩

/-! ## The honest trichotomy over the addition transfer -/

/-- PROVED SAFE: a caged hull keeps every concrete sum in the cage. -/
theorem addT_caged_certifies {B : Int} {a b : Iv}
    (h : Caged B (addT a b)) {c₁ c₂ : Int} (h1 : a.mem c₁) (h2 : b.mem c₂) :
    CagedValue B (c₁ + c₂) := by
  obtain ⟨hc1, hc2⟩ := addT_sound a b c₁ c₂ h1 h2
  obtain ⟨hl, hh⟩ := h
  show -B ≤ c₁ + c₂ ∧ c₁ + c₂ ≤ B
  exact ⟨by omega, by omega⟩

/-- PROVED OVERFLOW, the upper face: a hull entirely above the cage
    certifies every concrete sum escapes above. -/
theorem addT_over {B : Int} {a b : Iv}
    (h : B < (addT a b).lo) {c₁ c₂ : Int} (h1 : a.mem c₁) (h2 : b.mem c₂) :
    B < c₁ + c₂ := by
  obtain ⟨hc1, _⟩ := addT_sound a b c₁ c₂ h1 h2
  omega

/-- PROVED OVERFLOW, the lower face: a hull entirely below the cage
    certifies every concrete sum escapes below. -/
theorem addT_under {B : Int} {a b : Iv}
    (h : (addT a b).hi < -B) {c₁ c₂ : Int} (h1 : a.mem c₁) (h2 : b.mem c₂) :
    c₁ + c₂ < -B := by
  obtain ⟨_, hc2⟩ := addT_sound a b c₁ c₂ h1 h2
  omega

-- The fourth case — the hull straddles the cage's edge without being
-- caged — is the imprecision case: the framework says NOTHING (UNKNOWN,
-- 01-core §3's discipline: never silently a verdict). No lemma lands
-- for it; the absence is the honesty.

/-! ## The finite-height discipline (the widening's termination note) -/

/-- Strict ascent strictly increases the width (for a nonempty left
    operand). With `width_bounds` this caps ascending chains at 2B+1
    strict steps — the finite-height discipline. -/
theorem width_lt {a b : Iv} (hne : a.lo ≤ a.hi) (h : Iv.le a b)
    (hab : a ≠ b) : a.width < b.width := by
  have ⟨h1, h2⟩ := Iv.le_endpoints hne h
  have hd : b.lo < a.lo ∨ a.hi < b.hi := by
    by_cases hc : b.lo < a.lo
    · exact Or.inl hc
    · by_cases hc' : a.hi < b.hi
      · exact Or.inr hc'
      · exact absurd (Iv.eq_of_lo_hi (by omega) (by omega)) hab
  show a.hi - a.lo < b.hi - b.lo
  omega

/-- Caged nonempty intervals have width in `[0, 2B]` — the finite
    height (at most `2B+1` strict steps of `width_lt`). -/
theorem width_bounds {B : Int} {a : Iv} (hne : a.lo ≤ a.hi)
    (hc : Caged B a) : 0 ≤ a.width ∧ a.width ≤ 2 * B := by
  show 0 ≤ a.hi - a.lo ∧ a.hi - a.lo ≤ 2 * B
  obtain ⟨h1, h2⟩ := hc
  exact ⟨by omega, by omega⟩

end Analysis

/-
# AnalysisTests — the pins, the teeth, the negative controls

Per the discipline: positive pins + the MANDATORY negative controls
(notes/v3/15-patterns.md #5). Suites:

1. `pins` — the interval arithmetic's known answers, as values: the
   point, the add/neg/join hulls, the empty interval's refusal, the
   membership verdicts.
2. `soundness` — the transfer soundness fields + the checker's THE
   theorem exercised at concrete expressions: the abstract result's γ
   covers the concrete result (`abstract_sound` — the relational
   engine's generic theorem, cited); the cage's certified/overflow
   faces (the honest trichotomy at work).
3. `teeth` — the type-level refusal: a WRONG transfer function
   (`badAdd`) does not construct a `Transfer2` — the soundness field's
   ¬∃ pin; the wrong join cover's ¬∀ pin; the unsound claims' decidability
   pins (each is refuse-able, so the refusals are real).
4. `sweep` — the LCG-seeded property sweep over drawn intervals (the
   transfer soundness + the join covers + the checker agreement,
   re-checked executably as a regression) with the mandatory negative
   controls: the bad-add sabotage, the empty-interval sabotage, and the
   checker-refutation sabotage — each must be CAUGHT on every instance
   (fixed counterexamples: a control that only sometimes fires proves
   nothing).

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the soundness theorems — the core triple at most.
-/

import Analysis
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import AnalysisTests.Axioms

open Analysis TestingKit Kit

/-! ## Suite 1: the known-answer pins -/

-- the abstraction function: the point interval
theorem point_pin : point 3 = ⟨3, 3⟩ := rfl

-- the addition transfer: the endpointwise hull
theorem add_pin : addT ⟨1, 2⟩ ⟨3, 4⟩ = ⟨4, 6⟩ := rfl

-- the negation transfer: the mirrored interval
theorem neg_pin : negT ⟨1, 2⟩ = ⟨-2, -1⟩ := rfl

-- the join: the endpointwise hull of the two operands
theorem join_pin : join ⟨1, 3⟩ ⟨5, 7⟩ = ⟨1, 7⟩ := by decide

-- the join is idempotent (the widening's stability)
theorem join_idem_pin : join ⟨2, 5⟩ ⟨2, 5⟩ = ⟨2, 5⟩ := by decide

-- membership verdicts (γ as data)
theorem mem_pin : (addT ⟨1, 2⟩ ⟨3, 4⟩).mem 5 := by decide
theorem mem_out_pin : ¬ ((addT ⟨1, 2⟩ ⟨3, 4⟩).mem 7) := by decide

-- the empty interval (lo > hi) concretizes to NOTHING — honestly in
-- the type, honestly empty; and it is BELOW everything (the γ-order's
-- vacuous reading)
theorem empty_pin : ¬ ((⟨2, 1⟩ : Iv).mem 0) := by decide
theorem empty_le_pin : Iv.le ⟨2, 1⟩ ⟨0, 5⟩ := by
  intro c h
  have h1 : (2 : Int) ≤ c := h.1
  have h2 : c ≤ (1 : Int) := h.2
  exact ⟨by omega, by omega⟩

/-! ## Suite 2: the soundness exercised -/

-- the binary transfer's soundness field, at values
theorem add_sound_pin : (addT ⟨1, 2⟩ ⟨3, 4⟩).mem 5 :=
  addT_sound ⟨1, 2⟩ ⟨3, 4⟩ 2 3 (by decide) (by decide)

-- the unary transfer's soundness field, at values
theorem neg_sound_pin : (negT ⟨1, 2⟩).mem (-2) :=
  negT_sound ⟨1, 2⟩ 2 (by decide)

-- the join's cover fields, at values (both one-sided forms)
theorem join_cover_left_pin : (join ⟨1, 3⟩ ⟨5, 7⟩).mem 2 :=
  join_cover_left ⟨1, 3⟩ ⟨5, 7⟩ 2 (by decide)
theorem join_cover_right_pin : (join ⟨1, 3⟩ ⟨5, 7⟩).mem 6 :=
  join_cover_right ⟨1, 3⟩ ⟨5, 7⟩ 6 (by decide)

-- the domain instance's fields ARE the theorems (cited at construction,
-- not re-rolled — the projections close by rfl)
theorem domain_gamma_pin (iv : Iv) (c : Int) :
    intervalDomain.γ iv c = iv.mem c := rfl
theorem domain_binA_step : intervalDomain.binA.step = addT := rfl
theorem domain_unA_step : intervalDomain.unA.step = negT := rfl
theorem domain_join : intervalDomain.join = join := rfl

/-! ### the checker: the two evaluations, tied by ONE theorem -/

/-- `2 + (-3)` — the concrete value is `-1`, the abstract result is
    exactly the point interval `[-1, -1]`. -/
def eSmall : Expr Int := .bin (.prim 2) (.un (.prim 3))

/-- `(10 + (-3)) + 5` — the abstract result is exactly `[12, 12]`. -/
def eBig : Expr Int := .bin (.bin (.prim 10) (.un (.prim 3))) (.prim 5)

/-- `8 + 8` — the concrete value leaves the 10-cage. -/
def eOver : Expr Int := .bin (.prim 8) (.prim 8)

theorem eSmall_concrete : concreteEval eSmall = -1 := rfl
theorem eSmall_abstract : abstractEval eSmall = ⟨-1, -1⟩ := by decide

theorem eBig_concrete : concreteEval eBig = 12 := rfl
theorem eBig_abstract : abstractEval eBig = ⟨12, 12⟩ := by decide

-- THE SOUNDNESS THEOREM at the pins: the abstract result's γ covers
-- the concrete result — the engine's theorem, no new induction
theorem eBig_certified : (abstractEval eBig).mem (concreteEval eBig) :=
  abstract_sound eBig

theorem eBig_certified_endpoints :
    (abstractEval eBig).lo ≤ concreteEval eBig
    ∧ concreteEval eBig ≤ (abstractEval eBig).hi :=
  abstractEval_certifies eBig

-- the bundle-level agreement (the same theorem at the interpretation)
theorem eBig_bundle : intervalPair.R (intervalPair.eval₁ eBig) (intervalPair.eval₂ eBig) :=
  intervalPair_agrees eBig

-- the cage's certified face: a caged abstract result certifies the
-- concrete value inside the cage
theorem eBig_caged : CagedValue 20 (concreteEval eBig) :=
  caged_result_certified eBig (by decide)

-- the cage's overflow face: the concrete value outside the cage forces
-- the abstract result out — the analysis's overflow FLAG (the loud
-- answer, never a silent pass)
theorem eOver_flagged : ¬ Caged 10 (abstractEval eOver) := by
  intro hc
  -- the certificate would put the concrete 16 inside the 10-cage — it
  -- does not fit (the decidability pin below is the refutation)
  exact (by decide : ¬ CagedValue 10 (concreteEval eOver))
    (caged_result_certified (B := 10) eOver hc)

-- the trichotomy's proved-overflow faces, at values
theorem over_face_pin : (10 : Int) < 8 + 8 :=
  addT_over (B := 10) (a := ⟨8, 8⟩) (b := ⟨8, 8⟩) (c₁ := 8) (c₂ := 8)
    (by decide) (by decide) (by decide)

/-! ## Suite 3: the teeth — the type-level refusal -/

-- THE refusal: the wrong transfer function does not construct a
-- `Transfer2` — the soundness field refuses (an unsound transfer does
-- not elaborate into the framework)
theorem badAdd_unsound :
    ¬ ∃ t : Transfer2 (fun a c => a.mem c) (fun c₁ c₂ : Int => c₁ + c₂),
      t.step = badAdd := by
  rintro ⟨t, hstep⟩
  have hs := t.sound ⟨1, 1⟩ ⟨1, 1⟩ 1 1 (by decide) (by decide)
  rw [hstep] at hs
  obtain ⟨_, h2⟩ := hs
  have h3 : (2 : Int) ≤ (0 : Int) := h2
  omega

-- the wrong join cover: returning the left operand does NOT satisfy
-- the cover law (the empty interval is below everything — including
-- the operand it drops)
def badJoin (a _b : Iv) : Iv := a

-- the wrong join cover: returning the LEFT operand drops the RIGHT
-- operand's coverage — the cover law refuses it
theorem badJoin_unsound :
    ¬ ∀ (a b : Iv) (c : Int), b.mem c → (badJoin a b).mem c := by
  intro h
  have hh := h ⟨0, 0⟩ ⟨5, 5⟩ 5 (by decide)
  have h2 : (5 : Int) ≤ (0 : Int) := hh.2
  omega

-- the wrong claims are REFUSE-ABLE at the value level (the controls
-- below only mean something because these fail)
theorem badAdd_example_fails : ¬ ((badAdd ⟨1, 1⟩ ⟨1, 1⟩).mem 2) := by decide

/-! ## Suite 4: the LCG-seeded sweep + the mandatory negative controls -/

/-- Draw one nonempty interval with endpoints in `[0, 6]`. -/
def drawIv (t : Tape) : Iv × Tape :=
  let (x, t) := t.below 4
  let (w, t) := t.below 3
  let i : Int := (x : Int)
  (⟨i, i + (w : Int)⟩, t)

/-- Draw a value OF the interval (in `[iv.lo, iv.hi]`). -/
def drawVal (t : Tape) (iv : Iv) : Int × Tape :=
  let (d, t) := t.below (UInt64.ofNat (iv.hi - iv.lo + 1).toNat)
  (iv.lo + (d : Int), t)

def propTransfers (t : Tape) : CheckResult := do
  let (a, t) := drawIv t
  let (b, t) := drawIv t
  let (c₁, t) := drawVal t a
  let (c₂, _) := drawVal t b
  -- the addition transfer's soundness (the Minkowski hull covers the sum)
  assert ((addT a b).mem (c₁ + c₂)) "addT soundness broke"
  -- the negation transfer's soundness
  assert ((negT a).mem (-c₁)) "negT soundness broke"
  -- the join covers BOTH operands
  assert ((join a b).mem c₁) "join cover left broke"
  assert ((join a b).mem c₂) "join cover right broke"
  -- the abstraction function's covering proof
  assert ((point c₁).mem c₁) "point covering broke"
  -- the checker's agreement, executably (the regression face of
  -- abstract_sound at a drawn expression)
  let e : Expr Int := .bin (.prim c₁) (.un (.prim c₂))
  assert ((abstractEval e).lo ≤ concreteEval e && concreteEval e ≤ (abstractEval e).hi)
    "the checker's soundness broke"

def controlBadAdd (_ : Tape) : CheckResult := do
  -- SABOTAGE: claims the dropped-endpoint add still covers the sum.
  assert ((badAdd ⟨1, 1⟩ ⟨1, 1⟩).mem 2) "bad-add sabotage not caught"

def controlEmptyTop (_ : Tape) : CheckResult := do
  -- SABOTAGE: claims the empty interval covers a value.
  assert (((⟨2, 1⟩ : Iv)).mem 3) "empty-interval sabotage not caught"

def controlCheckerRefutes (_ : Tape) : CheckResult := do
  -- SABOTAGE: claims the checker REFUTES its own sound certificate
  -- (2 + 3 abstracts to exactly [5, 5] — the refutation is false, so
  -- the sweep's teeth are real).
  let e : Expr Int := .bin (.prim 2) (.prim 3)
  assert (!(abstractEval e).mem (concreteEval e)) "checker-refutation sabotage not caught"

def specTransfers : Spec := Spec.ofList "analysis-transfers"
  propTransfers
  [ ("bad-add", controlBadAdd),
    ("empty-top", controlEmptyTop),
    ("checker-refutes", controlCheckerRefutes) ]
  12 20250715

def main : IO UInt32 := do
  mainOfSuites [("Analysis", [specTransfers])]

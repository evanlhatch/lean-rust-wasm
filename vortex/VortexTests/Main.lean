/-
# VortexTests — the pins, the teeth, the negative controls

Per the discipline: positive pins + the MANDATORY negative controls
(notes/v3/15-patterns.md #5). Suites:

1. `pins` — the selection's known answers: every boundary-`Ty` shape →
   its encoding (each decision-tree ROW exercised — the design's
   coverage obligation), the declared-fact rows (sorted+fixed-step →
   Sequence; the low-card/key/constant/FoR order), the key-position
   lane, the retention exemplars' round trips.
2. `totality` — the closed-universe discipline: one representative per
   `Ty` constructor, every one selects (the compiler owns the
   exhaustiveness — 15-patterns #15; the pins prove the cover's rows
   land and the fallback row exists).
3. `teeth` — the MANDATORY negative controls: each encoding's
   applicability guard has its REFUSAL pin (a wrong width, an inferred
   sortedness, an unguarded dict — the tree is not vacuous); the
   selection law CATCHES a mis-wired tree (the sabotaged `selectBad`);
   the constant encoding's LOSS on a non-constant column is pinned
   (the admissible-subdomain honesty — never a silent lie).

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the laws — the core triple at most.
-/

import Vortex
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import VortexTests.Axioms

open Vortex SchemaCore Kit TestingKit

/-! ## The fixture (the registered slice, mined to the lane's shapes) -/

def fixtureItems : List SchemaCore.Item :=
  [{ name := "Event", fields :=
    [ { name := "flag", ty := .bool }
    , { name := "count", ty := .u64 }
    , { name := "delta", ty := .i64 }
    , { name := "label", ty := .string }
    , { name := "maybe", ty := .option .u64 }
    , { name := "capped", ty := .bounded 100 }
    , { name := "unitCap", ty := .bounded 1 }
    , { name := "tags", ty := .set .u64 }
    , { name := "seq", ty := .list .u64 }
    , { name := "either", ty := .result .u64 .string } ] }]

def fixtureReg : DataRegistry SchemaCore.Item :=
  { items := fixtureItems, nameOf := fun it => it.name, nodup := by decide }

/-! ## Suite 1: the known-answer pins (each tree row exercised) -/

-- the fallback row: a fixed-width scalar, no facts → bitpacked at its
-- declared width. A bool is a TWO-VALUED ENUM (staticCard? 2 ≤ the
-- low-card ceiling) → the dict row per the locked order — the enum row
-- beats the fallback (pinned next).
theorem bool_pin : layoutOf .bool = ⟨.dict, false⟩ := rfl
theorem u64_pin : layoutOf .u64 = ⟨.bitPacked 64, false⟩ := rfl
theorem i64_pin : layoutOf .i64 = ⟨.bitPacked 64, false⟩ := rfl

-- no fixed-width layout → the identity fallback
theorem string_pin : layoutOf .string = ⟨.identity, false⟩ := rfl
theorem list_pin : layoutOf (.list .u64) = ⟨.identity, false⟩ := rfl
theorem result_pin : layoutOf (.result .u64 .string) = ⟨.identity, false⟩ := rfl
theorem map_pin : layoutOf (.map .u64 .string) = ⟨.identity, false⟩ := rfl

-- the option wrapper peels to the VALIDITY layer; the element selects
theorem option_pin : layoutOf (.option .u64) = ⟨.bitPacked 64, true⟩ := rfl

-- the set's element rides the key sub-universe → dict (isKey)
theorem set_pin : layoutOf (.set .u64) = ⟨.dict, false⟩ := rfl

-- low static card (100 ≤ 256) → the dict row (flatland's locked order:
-- enum/low-card beats FoR)
theorem bounded_lowcard_pin : layoutOf (.bounded 100) = ⟨.dict, false⟩ := rfl

-- a static card ABOVE the dict ceiling, within the FoR ceiling → FoR
-- over the bound's width (bitsFor 1000 = log2 1000 + 1 = 10)
theorem bounded_for_pin : layoutOf (.bounded 1000) = ⟨.foR 10, false⟩ := rfl

-- above the FoR ceiling → the fallback (the ceiling's refusal face)
theorem bounded_big_pin : layoutOf (.bounded 70000) = ⟨.bitPacked 64, false⟩ := rfl

-- a static card of EXACTLY one → the constant row (is-constant beats
-- every other guard — the tree's first row)
theorem bounded_one_pin : layoutOf (.bounded 1) = ⟨.constant, false⟩ := rfl

-- the constant row beats the key row (the guard ORDER is the policy)
theorem order_constant_beats_dict (t : Ty) :
    select t { cardBound := some 1, isKey := true, sorted? := none,
               fixedStep := false, nullable := false } = .constant := rfl

-- the DECLARED rows: sorted + fixed-step → Sequence (declared only —
-- nothing infers it)
theorem sequence_pin :
    select .u64 { cardBound := none, isKey := false, sorted? := some .asc,
                  fixedStep := true, nullable := false } = .sequence := rfl

-- the declared low-card row: 8 ≤ 256 → dict
theorem lowcard_pin :
    select .u64 { cardBound := some 8, isKey := false, sorted? := none,
                  fixedStep := false, nullable := false } = .dict := rfl

-- the key-position lane: EVERY key → dict (the design's FK → Dict),
-- total over the closed key sub-universe
theorem key_bool : select .bool (keyFacts .bool) = .dict := keyFacts_dict .bool
theorem key_u64 : select .u64 (keyFacts .u64) = .dict := keyFacts_dict .u64
theorem key_i64 : select .i64 (keyFacts .i64) = .dict := keyFacts_dict .i64
theorem key_string : select .string (keyFacts .string) = .dict := keyFacts_dict .string

-- the width arithmetic (the FoR row's offsets fit the bound)
theorem bitsFor_pin : bitsFor (some 8) = 4 ∧ bitsFor (some 100) = 7 := by decide

/-! ## Suite 2: the totality discipline (the closed universe) -/

/-- ONE representative per `Ty` constructor — the closed universe's
    cover (10 ctors; 15-patterns #15: a new ctor breaks this list's
    exhaustiveness AND every fold's — the compiler drives it). -/
def universeCover : List Ty :=
  [ .bool, .u64, .i64, .string
  , .option .u64, .list .u64, .result .u64 .string
  , .map .u64 .string, .set .u64, .bounded 100 ]

-- every covered ctor selects (the cover's rows land — the selection is
-- total over the universe, the fallback row always exists)
theorem cover_total :
    (universeCover.map fun t => (layoutOf t).encoding).length = 10 := rfl

-- every covered ctor's layout is APPLICABLE (the law over the whole
-- cover — `select_applicable` at each)
theorem cover_applicable :
    (universeCover.all fun t =>
      applicable (layoutOf t).encoding (columnOf t).1 (factsOfColumn t)) = true :=
  List.all_eq_true.mpr fun t _ => layoutOf_applicable t

-- the emitter's law over the fixture registry (the certified lane's
-- discharge — one citation)
theorem fixture_law : layoutLaw fixtureReg := layoutLaw_discharged fixtureReg

/-! ## Suite 3: the negative controls (the tree is not vacuous) -/

-- each guard's REFUSAL face: a wrong width is inapplicable
theorem wrong_width_refused :
    applicable (.bitPacked 32) .u64
      { cardBound := none, isKey := false, sorted? := none,
        fixedStep := false, nullable := false } = false := rfl

-- dict without a key position or a card bound is inapplicable
theorem unguarded_dict_refused :
    applicable .dict .string
      { cardBound := none, isKey := false, sorted? := none,
        fixedStep := false, nullable := false } = false := rfl

-- a FoR width that does not name the bound is inapplicable (8 ≠
-- bitsFor 8 = 4)
theorem wrong_for_width_refused :
    applicable (.foR 8) .u64
      { cardBound := some 8, isKey := false, sorted? := none,
        fixedStep := false, nullable := false } = false := rfl

-- FoR on a non-integer shape is inapplicable
theorem nonint_for_refused :
    applicable (.foR 1) .string
      { cardBound := some 2, isKey := false, sorted? := none,
        fixedStep := false, nullable := false } = false := rfl

-- sortedness is NEVER inferred: an undeclared sortedness refuses the
-- sequence row even with the fixed-step declared
theorem inferred_sortedness_refused :
    applicable .sequence .u64
      { cardBound := none, isKey := false, sorted? := none,
        fixedStep := true, nullable := false } = false := rfl

-- a two-valued column refuses the constant row
theorem nonconstant_const_refused :
    applicable .constant .bool
      { cardBound := some 2, isKey := false, sorted? := none,
        fixedStep := false, nullable := false } = false := rfl

-- THE LAW'S TEETH: a mis-wired tree (a sabotaged selection that picks
-- a wrong width) is CAUGHT by the applicability law — the law has
-- teeth, the negative control fires
def selectBad (t : Ty) (f : ShapeFacts) : EncodingSpec := .bitPacked 32

theorem selectBad_caught :
    applicable (selectBad .u64
      { cardBound := none, isKey := false, sorted? := none,
        fixedStep := false, nullable := false }) .u64
      { cardBound := none, isKey := false, sorted? := none,
        fixedStep := false, nullable := false } = false := rfl

-- THE RETENTION HONESTY: the constant encoding LOSES on a non-constant
-- column — the admissible-subdomain discipline, pinned (never a silent
-- universal-law lie)
theorem constant_loses_off_subdomain :
    constRead (constEncode [1, 2]) ≠ [1, 2] := by decide

-- the retention exemplars' round trips (the semantic core, exercised)
theorem for_roundtrip : forRead (forEncode [3, 5, 2]) = [3, 5, 2] :=
  forRead_forEncode [3, 5, 2]

theorem constant_roundtrip : constRead (constEncode [7, 7, 7]) = [7, 7, 7] :=
  constRead_constEncode 7 [7, 7] (by decide)

/-! ## The emitter row (the in-test byte-tie golden) -/

-- the one-writer discipline, data-level
theorem emitter_outputs_nodup : layoutEmitter.outputs.Nodup := by decide

-- THE GOLDEN TIE: the emitter's run over the fixture registry IS the
-- pinned artifact body, kernel-discharged (the byte-tie's in-test face
-- — the committed-file face + the GenCheck/Ownership wiring land with
-- the write path, the named follow-up)
def goldenBody : String :=
  "-- vortex layout spec — the encoding plan per column\n"
    ++ "-- selected by Vortex.select from the static shape facts (pure, total;\n"
    ++ "-- never a runtime search — notes/design-vortex-encodings.md)\n"
    ++ "Event.flag: bool -> dict\n"
    ++ "Event.count: u64 -> bitpacked<64>\n"
    ++ "Event.delta: i64 -> bitpacked<64>\n"
    ++ "Event.label: string -> identity\n"
    ++ "Event.maybe: option<u64> -> validity+bitpacked<64>\n"
    ++ "Event.capped: u64 -> dict\n"
    ++ "Event.unitCap: u64 -> constant\n"
    ++ "Event.tags: list<u64> -> dict\n"
    ++ "Event.seq: list<u64> -> identity\n"
    ++ "Event.either: result<u64, string> -> identity\n"

set_option maxRecDepth 100000 in
theorem layout_artifact :
    layoutEmitter.run fixtureReg
      = [{ path := "gen/vortex-layout.txt", contents := goldenBody }] := rfl

/-! ## The runtime regression suite (the exe's executable face) -/

/-- The no-facts baseline (the fallback row's domain). -/
def noFacts : ShapeFacts :=
  { cardBound := none, isKey := false, sorted? := none,
    fixedStep := false, nullable := false }

def propPins (_ : Tape) : CheckResult := do
  -- the closed-universe cover's applicability, executably
  assert ((universeCover.all fun t =>
    applicable (layoutOf t).encoding (columnOf t).1 (factsOfColumn t)) = true)
    "the cover's applicability broke"
  -- the golden tie, executably
  assertEq "golden" ((layoutEmitter.run fixtureReg).map (·.contents))
    [goldenBody]
  -- the refusal faces, executably
  assert ((applicable (.bitPacked 32) .u64 noFacts) = false)
    "a wrong width was not refused"
  assert ((applicable .sequence .u64 noFacts) = false)
    "an inferred sortedness was not refused"

def controlGoldenDrift (_ : Tape) : CheckResult :=
  -- SABOTAGE: a hand-edited artifact body must be CAUGHT by the tie.
  assertEq "golden-drift" goldenBody
    (goldenBody.replace "Event.flag: bool -> dict" "Event.flag: bool -> bitpacked<1>")

def controlBadTree (_ : Tape) : CheckResult :=
  -- SABOTAGE: the mis-wired tree's applicability must be CAUGHT false.
  assert ((applicable (selectBad .u64 noFacts) .u64 noFacts) = true)
    "the mis-wired tree was not caught"

def controlConstantUniversal (_ : Tape) : CheckResult :=
  -- SABOTAGE: the constant encoding's universal-law claim must be
  -- CAUGHT (it loses off the admissible subdomain).
  assert ((constRead (constEncode [1, 2])) == [1, 2])
    "the constant loss was not pinned"

def specVortex : Spec := Spec.ofList "vortex-selection"
  propPins
  [ ("golden-drift", controlGoldenDrift)
  , ("bad-tree", controlBadTree)
  , ("constant-universal", controlConstantUniversal) ]
  8 20250922

def main : IO UInt32 := do
  mainOfSuites [("Vortex", [specVortex])]

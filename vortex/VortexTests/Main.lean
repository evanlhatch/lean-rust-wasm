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
4. `compute` — COMPUTE-ON-COMPRESSED (`Vortex.Compute`): the
   per-(encoding, op) agreement (the encoded evaluation IS the decoded
   filter — the retention discipline at the compute grade), the
   fragment's refusal faces (an off-fragment raw predicate on foR; a
   corrupted dict carrier), the LCG-swept columns, and the fusion
   teeth (the probe account: dict = the distinct-value count, constant
   = one probe — independent of the row count).
5. `arith` — THE AFFINE KERNEL (the flatland absorbables, E3): the
   per-(encoding, op) agreement for the ARITHMETIC ops pushed INTO the
   encoding (add-const / mul-const), the checked-overflow refusals
   (constant / FoR / dict — the exact-on-range class), the corruption
   gate, the O(|dict|) + zero-row-work account teeth, and the
   f64-exactness hazard law note's pins (no f53 cliff — the integer
   lane stays exact; an inexact pushdown refuses, never rounds).
6. `proto` — the DType proto face (`Vortex.DTypeProto`): the
   round-trip sweep (a representative per constructor, both
   nullability faces), the ASCII-gate refusal teeth (a non-ASCII
   struct field name / extension id), the truncation + trailing-byte
   refusals, and the null body's known-answer byte vector.

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
-- THE SIGNED ROW (i* via FoR — the E3 dtype-policy face): a signed
-- scalar without a static bound rides the full-width rebase face
-- (the zigzag-or-rebase discipline — the offsets are unsigned either
-- way); the unsigned scalar keeps the BitPacked terminal
theorem i64_pin : layoutOf .i64 = ⟨.foR 64, false⟩ := rfl
theorem u64_terminal_pin : layoutOf .u64 = ⟨.bitPacked 64, false⟩ := rfl

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

-- the dict semantic codec's round trip (the UNCONDITIONAL law, exercised
-- — no domain premise to sabotage, the byte layer pins the 2^64 atom check)
theorem dict_roundtrip : dictDecode (dictEncode [3, 1, 3, 2]) = [3, 1, 3, 2] :=
  dictRetention [3, 1, 3, 2]

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
    ++ "Event.delta: i64 -> for+bitpacked<64>\n"
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

/-! ## Suite 3.5: the SPARSE outer layer (the nesting face) -/

-- the outer-only pin: the static tree never selects sparse (sparsity
-- is a DATA fact — the runEnd exclusion's tier; the host applies the
-- layer over a child encoding)
theorem select_ne_sparse_u64 (c : EncodingSpec) :
    select .u64 noFacts ≠ .sparse c := select_ne_sparse .u64 noFacts c
theorem select_ne_sparse_bounded (c : EncodingSpec) :
    select (.bounded 100) noFacts ≠ .sparse c :=
  select_ne_sparse _ noFacts c

-- THE NESTING TOOTH: sparse over foR over bitpacked — encoded inside
-- encoded (flatland §E6: every child independently compressible; §E2:
-- bitmap + FoR delta values). The patch values [105, 107] ride foR 2
-- (base 105, offsets [0, 2] fit the 2-bit stream).
def nestedSpec : EncodingSpec := .sparse (.foR 2)
def nestedCol : List Nat := [105, 105, 107, 105, 105]

theorem nested_inDomain : inDomain nestedSpec nestedCol = true := by decide

-- the dispatch law AT the nested spec: the sparse case cites the
-- child's own dispatch case — the recursive citation IS the nesting
-- discipline (one theorem, no re-proof at depth)
theorem nested_roundtrip (rest : List UInt8) :
    decodeColumn nestedSpec (encodeColumn nestedSpec nestedCol ++ rest)
      = some (nestedCol, rest) :=
  decodeColumn_encodeColumn_append nestedSpec nestedCol nested_inDomain rest

-- a second depth-1 shape: sparse over bitpacked (the terminal child)
def nestedSpec2 : EncodingSpec := .sparse (.bitPacked 4)
def nestedCol2 : List Nat := [3, 3, 3, 7, 3, 3]

theorem nested_inDomain2 : inDomain nestedSpec2 nestedCol2 = true := by decide

theorem nested_roundtrip2 (rest : List UInt8) :
    decodeColumn nestedSpec2 (encodeColumn nestedSpec2 nestedCol2 ++ rest)
      = some (nestedCol2, rest) :=
  decodeColumn_encodeColumn_append nestedSpec2 nestedCol2 nested_inDomain2 rest

-- the CHILD's off-domain patches refuse the sparse row (the nesting
-- discipline: the child's admissibility rides the parent's domain —
-- the offsets [0, 5] do not fit foR 2's 2-bit stream)
theorem sparse_child_domain_refused :
    inDomain (.sparse (.foR 2)) [10, 10, 20, 25, 10] = false := by decide

/-! ## Suite 4: the DATA lane — the selected encodings APPLIED (the real
    emission: the layout drives the bytes) -/

/-- The fixture columns' data: one row per emitted column, the layout
    FROM THE SELECTION (`layoutOf` at the boundary `Ty`), the values
    u64-ranged. The foR/sequence rows are the declared-fact lanes (the
    schema's `bounded 1000` range / the declared sorted+fixed-step). -/
def fixtureColumns : List Vortex.ColumnData :=
  [ { name := "Event.count", layout := layoutOf .u64
      validity := [], values := [42, 42, 7] }
  , { name := "Event.capped", layout := layoutOf (.bounded 100)
      validity := [], values := [3, 1, 3, 2] }
  , { name := "Event.unitCap", layout := layoutOf (.bounded 1)
      validity := [], values := [0, 0, 0] }
  , { name := "Event.range", layout := layoutOf (.bounded 1000)
      validity := [], values := [1000, 1003, 1000] }
  , { name := "Event.tick", layout := ⟨.sequence, false⟩
      validity := [], values := [10, 13, 16, 19] }
  , { name := "Event.raw", layout := ⟨.identity, false⟩
      validity := [], values := [300, 5] }
  , { name := "Event.maybe", layout := layoutOf (.option .u64)
      validity := [true, false, true], values := [5, 0, 9] }
  , { name := "Event.overlay", layout := ⟨.sparse (.foR 2), false⟩
      validity := [], values := nestedCol } ]
-- the overlay row is the HOST-applied outer layer (flatland §E2's
-- overlay read): sparse never comes from `layoutOf` — the layout is
-- the host's nesting choice over the foR child

/-- Every fixture column is in its own layout's domain (the emission
    boundary's check, decided once for the fixture). -/
theorem fixture_domains :
    (fixtureColumns.all fun c => inDomain c.layout.encoding c.values) = true :=
  by decide

/-- The emission law over the WHOLE fixture: every column's bytes read
    back to its values (the dispatch law at each fixture row — the
    kernel-discharged composition). -/
theorem fixture_emission_law :
    (fixtureColumns.all fun c =>
      readColumnData c (emitColumnData c) = some (c.values, [])) = true := by
  have hdom := fixture_domains
  refine List.all_eq_true.mpr fun c hc => ?_
  have h := readColumnData_emitColumnData_append c
    (List.all_eq_true.mp hdom c hc) []
  rw [List.append_nil] at h
  exact decide_eq_true h

/-! ### The known-answer byte vectors (the kernel pins — each encoding's
    wire shape pinned byte-for-byte) -/

-- bitPacked 4: count 2, then the stream 3 + 16·1 = 19, one byte
theorem kab_bitpacked : encBitPacked 4 [3, 1] = [2, 19] := rfl
-- foR 10: base 1000 (varint [232, 7]), offsets [0,3,0] → stream 3072
-- over 4 bytes little-endian [0, 12, 0, 0]
theorem kab_for : encFoR 10 [1000, 1003, 1000] = [232, 7, 3, 0, 12, 0, 0] := rfl
-- dict [3,1,3,2]: dedup [1,3,2], values [1,3,2], codes [1,0,1,2] at
-- width bitsFor 3 = 2 → stream 145, one byte
theorem kab_dict : encDict [3, 1, 3, 2] = [3, 1, 3, 2, 4, 145] := rfl
-- sequence: start 10 (zigzag 20), step 3 (zigzag 6), count 4
theorem kab_seq : encSeqData [10, 13, 16, 19] = [20, 6, 4] := rfl
-- constant: the shared value 7, count 3
theorem kab_const : encConst [7, 7, 7] = [7, 3] := rfl
-- identity: count 2, then the varints [172, 2] (= 300) and [5]
theorem kab_identity : encIdentity [300, 5] = [2, 172, 2, 5] := rfl
-- the validity bitmap: 1 bit per row, LSB-first — [t,f,t] → stream 5
theorem kab_validity :
    encBitPacked 1 ([true, false, true].map (fun b => if b then 1 else 0))
      = [3, 5] := rfl

/-- The emission law's executable face over every fixture column. -/
def propData (_ : Tape) : CheckResult := do
  for c in fixtureColumns do
    assertEq s!"{c.name} round trip"
      (readColumnData c (emitColumnData c)) (some (c.values, []))
  -- the nesting teeth, executably (encoded-inside-encoded)
  assertEq "nested sparse-over-foR"
    (decodeColumn nestedSpec (encodeColumn nestedSpec nestedCol))
    (some (nestedCol, []))
  assertEq "nested sparse-over-bitpacked"
    (decodeColumn nestedSpec2 (encodeColumn nestedSpec2 nestedCol2))
    (some (nestedCol2, []))
  -- the sparse wire's shape: count [5], default [105], mask bytes [5, 4]
  -- (bits [0,0,1,0,0] → stream 4), then the foR child's payload [107, 1, 0]
  assertEq "kab sparse" (encodeColumn nestedSpec nestedCol)
    [5, 105, 5, 4, 107, 1, 0]
  -- the known answers, executably (the kernel pins' runtime face)
  assertEq "kab bitpacked" (encBitPacked 4 [3, 1]) [2, 19]
  assertEq "kab for" (encFoR 10 [1000, 1003, 1000]) [232, 7, 3, 0, 12, 0, 0]
  assertEq "kab dict" (encDict [3, 1, 3, 2]) [3, 1, 3, 2, 4, 145]
  assertEq "kab seq" (encSeqData [10, 13, 16, 19]) [20, 6, 4]
  assertEq "kab identity" (encIdentity [300, 5]) [2, 172, 2, 5]

def controlBitpackDomain (_ : Tape) : CheckResult :=
  -- SABOTAGE: the off-domain claim (a 5 does not fit 4 bits) must be
  -- CAUGHT — the codec's loss is pinned, never silent
  assertEq "bitpack-domain" (decBitPacked? 4 (encBitPacked 4 [17]))
    (some ([17], []))

def controlSeqDomain (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming sequence retention OFF the progression — the
  -- regenerated rows [10, 13, 16] differ from the data [10, 13, 15]
  assertEq "seq-domain" (decSeq? (encSeqData [10, 13, 15]))
    (some ([10, 13, 15], []))

def controlFoRDomain (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming FoR retention when the range exceeds the width —
  -- the offset 5 truncates to 1 at 2 bits
  assertEq "for-domain" (decFoR? 2 (encFoR 2 [0, 5])) (some ([0, 5], []))

def controlTruncation (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the TRUNCATED payload decodes to the full values
  -- — the missing byte must refuse, never a silent short read
  assertEq "truncation" (decBitPacked? 4 [2]) (some ([3, 1], []))

def controlSparseChildDomain (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming sparse retention when the CHILD's domain is
  -- violated — the offsets truncate (5 at 2 bits → 1) and the values
  -- come back wrong; the loss is pinned, never silent
  assertEq "sparse-child-domain"
    (decodeColumn (.sparse (.foR 2)) (encodeColumn (.sparse (.foR 2)) [10, 10, 20, 25, 10]))
    (some ([10, 10, 20, 25, 10], []))

def controlSparseTruncation (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the TRUNCATED sparse payload decodes — only the
  -- count byte present, the default byte missing: the decoder must
  -- refuse, never a silent short read
  assertEq "sparse-truncation" (decodeColumn nestedSpec [5])
    (some (nestedCol, []))

def specVortexData : Spec := Spec.ofList "vortex-data"
  propData
  [ ("bitpack-domain", controlBitpackDomain)
  , ("seq-domain", controlSeqDomain)
  , ("for-domain", controlFoRDomain)
  , ("truncation", controlTruncation)
  , ("sparse-child-domain", controlSparseChildDomain)
  , ("sparse-truncation", controlSparseTruncation) ]
  8 20250922

/-! ## Suite 5: COMPUTE-ON-COMPRESSED (the encoded evaluation) -/

-- the compute columns: one per landed carrier row (the matrix's data
-- face; each in its spec's domain — asserted in the sweep)
def computeCols : List (String × EncodingSpec × List Nat) :=
  [ ("identity", .identity, [300, 5, 300])
  , ("bitPacked", .bitPacked 4, [3, 1, 3, 0])
  , ("foR", .foR 4, [10, 12, 10, 15])
  , ("dict", .dict, [3, 1, 3, 2])
  , ("constant", .constant, [7, 7, 7]) ]

-- the op column: the named fragment (eq / thresholds / complement) +
-- the off-fragment raw escape hatch (admits the pointwise rows,
-- REFUSED by the foR pushdown — the fragment boundary, exercised)
def computePreds : List VPred :=
  [ .eqVal 3, .ltVal 11, .gtVal 2, .notP (.ltVal 12), .notP (.eqVal 3)
  , .raw (fun x => x % 2 == 0) ]

/-! ### the per-(encoding, op) kernel pins (each matrix row's law) -/

-- identity × pointwise (the tie row: nothing compressed) — the
-- filter's known answer (only 300 clears the 100 threshold)
theorem compute_identity_pin :
    evalEncoded (.gtVal 100) (.rawVals [300, 5, 300]) = some ([300, 300], 3) := rfl

-- bitPacked × threshold (the fused peel — selection without the
-- materialized decode)
theorem compute_bitpacked_threshold :
    evalEncoded (.ltVal 2) (.bitPackData 2 3 (packStream 2 [1, 3, 0]))
      = some ([1, 0], 3) := by
  simp only [evalEncoded]
  rw [evalBitPack_ok]
  rfl

-- foR × equality (the pointwise shift: off == t - base)
theorem compute_foR_eq :
    evalEncoded (.eqVal 12) (.forData { base := 10, offsets := [0, 2, 0, 5] })
      = some ([12], 4) := by
  simp only [evalEncoded]
  rw [evalFor?_ok _ _ (by simp [shiftFoR])]
  rfl

-- foR × threshold (the exact shift: off < t - base)
theorem compute_foR_threshold :
    evalEncoded (.ltVal 12) (.forData { base := 10, offsets := [0, 2, 0, 5] })
      = some ([10, 10], 4) := by
  simp only [evalEncoded]
  rw [evalFor?_ok _ _ (by simp [shiftFoR])]
  rfl

-- foR × the complement (notP maps through the shift: ¬<12 is ≥12)
theorem compute_foR_not :
    evalEncoded (.notP (.ltVal 12))
      (.forData { base := 10, offsets := [0, 2, 0, 5] })
      = some ([12, 15], 4) := by
  simp only [evalEncoded]
  rw [evalFor?_ok _ _ (by simp [shiftFoR])]
  rfl

-- constant × eq (the landslide case: ONE probe, the replicate)
theorem compute_const_eq :
    evalEncoded (.eqVal 7) (.constData (constEncode [7, 7, 7]))
      = some ([7, 7, 7], 1) := by
  simp only [evalEncoded]
  rw [evalConst_ok]
  rfl

-- constant × the complement (one probe, the empty selection)
theorem compute_const_not :
    evalEncoded (.notP (.eqVal 7)) (.constData (constEncode [7, 7, 7]))
      = some ([], 1) := by
  simp only [evalEncoded]
  rw [evalConst_ok]
  rfl

-- dict × threshold (the classic trick: the values table probed ONCE,
-- the codes' selection vector re-indexes it)
theorem compute_dict_threshold :
    evalEncoded (.gtVal 1) (.dictData (dictEncode [3, 1, 3, 2]))
      = some ([3, 3, 2], 3) := by
  simp only [evalEncoded]
  rw [evalDict_ok _ _ (by decide)]
  rfl

-- the dict carrier over a REAL column: the column law's instance
-- (the carrier's decoded face IS the column — `decodeOf_carrier`)
theorem compute_column_dict :
    evalEncoded (.gtVal 1) (.dictData (dictEncode [3, 1, 3, 2]))
      = some ([3, 3, 2], 3) :=
  compute_dict_threshold

-- the foR carrier over a real column (the base is the column's min —
-- the byte codec's own; the shift rides it)
def realForCol : List Nat := [10, 12, 10, 15]

theorem compute_real_for_carrier :
    carrierOf? (.foR 4) realForCol
      = some (.forData { base := 10, offsets := [0, 2, 0, 5] }) := rfl

theorem compute_real_for_law :
    evalEncoded (.ltVal 12) (.forData { base := 10, offsets := [0, 2, 0, 5] })
      = some (realForCol.filter (VPred.ltVal 12).holds, 4) :=
  compute_foR_threshold

/-! ### the refusal faces (the fragment's boundary + the corruption gate) -/

-- an off-fragment (opaque) predicate REFUSES the foR pushdown: no
-- projection onto the offset domain without widening — `f (base + off)`
-- is decode in disguise
theorem computeOk_raw_for (f : Nat → Bool) (d : FoRCompute) :
    computeOk (.raw f) (.forData d) = false := rfl

theorem compute_raw_for_refused (f : Nat → Bool) (d : FoRCompute) :
    evalEncoded (.raw f) (.forData d) = none := rfl

-- a corrupted dict carrier (a code out of the values table's range)
-- REFUSES — never a fabricated row
theorem compute_corrupt_dict_refused :
    evalEncoded (.eqVal 1) (.dictData ⟨[1, 3], [0, 9, 1]⟩) = none :=
  evalDict_corrupt _ _ [0, 9, 1] 9 (by simp) (by simp)

-- the named gaps: sequence/sparse build NO compute carrier (each lands
-- with its first consumer — the leftover rule)
theorem compute_sequence_gap : carrierOf? .sequence [10, 13, 16] = none := rfl
theorem compute_sparse_gap :
    carrierOf? (.sparse (.foR 2)) nestedCol = none := rfl

/-! ### the fusion teeth (the probe account — the discipline's shape) -/

-- the dict account: the DISTINCT-VALUE count, independent of the rows
def smallLowCard : DictData := ⟨[1, 0], [0, 1, 0, 1, 0]⟩

theorem compute_dict_account :
    encodedProbes (.dictData smallLowCard) = 2
    ∧ decodeProbes (.gtVal 0) (.dictData smallLowCard) = 5 := by
  refine ⟨rfl, ?_⟩
  rw [decodeProbes_eq]; rfl

theorem compute_dict_win :
    encodedProbes (.dictData smallLowCard)
      < decodeProbes (.gtVal 0) (.dictData smallLowCard) :=
  dict_probes_win _ _ (by decide)

-- the constant account: ONE probe against the row count (the landslide)
theorem compute_const_account :
    encodedProbes (.constData { count := 1000, value := some 7 }) = 1
    ∧ decodeProbes (.gtVal 0) (.constData { count := 1000, value := some 7 })
        = 1000 := by
  refine ⟨rfl, ?_⟩
  rw [decodeProbes_eq, decodeOf, constRead, List.length_replicate]

theorem compute_const_win :
    encodedProbes (.constData { count := 1000, value := some 7 })
      < decodeProbes (.gtVal 0) (.constData { count := 1000, value := some 7 }) :=
  const_probes_win _ _ 1000 (by decide)

-- the honest ties: the pointwise rows' account IS the row count, both
-- sides (the encoded path wins nothing there — the law is the claim)
theorem compute_tie_raw :
    encodedProbes (.rawVals [300, 5, 300])
      = decodeProbes (.gtVal 0) (.rawVals [300, 5, 300]) :=
  account_tie_raw _ _
theorem compute_tie_bitpack :
    encodedProbes (.bitPackData 4 4 (packStream 4 [3, 1, 3, 0]))
      = decodeProbes (.ltVal 2) (.bitPackData 4 4 (packStream 4 [3, 1, 3, 0])) :=
  account_tie_bitPack _ _ _ _
theorem compute_tie_for :
    encodedProbes (.forData { base := 10, offsets := [0, 2, 0, 5] })
      = decodeProbes (.ltVal 12)
          (.forData { base := 10, offsets := [0, 2, 0, 5] }) :=
  account_tie_for _ _

/-! ### the executable face (the sweep + the teeth, at runtime) -/

-- the LCG drawer: a short column of 4-bit values (the seeded sweep —
-- same seed, same sweep, byte-identically)
def drawComputeCol (t : Tape) : List Nat × Tape :=
  let (n, t) := t.below 8
  drawMany (n + 1) (fun t => t.below 16) t

-- one (column, carrier, op) agreement instance: the encoded evaluation
-- IS the decoded filter, with the encoded account — and every refusal
-- is NAMED by the gate
def checkCompute (nm : String) (_spec : EncodingSpec) (vals : List Nat)
    (c : Encoded) (p : VPred) : CheckResult :=
  match evalEncoded p c with
  | none => assert (!computeOk p c) s!"{nm}: refusal without the gate naming it"
  | some (res, probes) => do
      assert (computeOk p c) s!"{nm}: success without the gate"
      assert (res == vals.filter p.holds) s!"{nm}: agreement broke"
      assert (probes == encodedProbes c) s!"{nm}: account broke"

def propCompute (_ : Tape) : CheckResult := do
  -- the fixture columns: every (encoding, op) cell, both faces
  for (nm, spec, vals) in computeCols do
    assert (inDomain spec vals) s!"{nm}: fixture column off-domain"
    match carrierOf? spec vals with
    | none => assert false s!"{nm}: carrier refused"
    | some c =>
        for p in computePreds do
          checkCompute nm spec vals c p
  -- the LCG sweep: drawn columns over every in-domain spec
  let (cols, _) := drawMany 12 drawComputeCol (Tape.ofSeed 20250922)
  for vals in cols do
    for (nm, spec, _) in computeCols do
      if inDomain spec vals then
        match carrierOf? spec vals with
        | none => assert false s!"{nm}: carrier refused an in-domain column"
        | some c =>
            for p in computePreds do
              checkCompute s!"{nm}-sweep" spec vals c p
  -- the fusion teeth, executably: 1000 rows over a 2-value dictionary —
  -- the encoded account is the DISTINCT-VALUE count, not the row count
  let bigDict : DictData := dictEncode ((List.range 1000).map (fun i => i % 2))
  assertEq "dict-probes-enc"
    ((evalEncoded (.gtVal 0) (.dictData bigDict)).map (·.2))
    (some bigDict.vals.length)
  assert (bigDict.vals.length
      < decodeProbes (.gtVal 0) (.dictData bigDict))
    "dict: no probe win over the decoded baseline"
  -- the constant landslide: a MILLION rows, one probe
  let bigConst : ConstantData Nat := { count := 1000000, value := some 7 }
  assertEq "const-probes-enc"
    ((evalEncoded (.gtVal 0) (.constData bigConst)).map (·.2))
    (some 1)
  assert (1 < decodeProbes (.gtVal 0) (.constData bigConst))
    "constant: no probe win over the decoded baseline"
  -- the fused peel runs WITHOUT the materialized decode: the bitPacked
  -- agreement at 1000 stream positions (the result is the only list built)
  let longBits : List Nat := (List.range 1000).map (fun i => i % 16)
  let e := Encoded.bitPackData 4 1000 (packStream 4 longBits)
  match evalEncoded (.gtVal 5) e with
  | none => assert false "bitpacked: the fused peel refused in-domain data"
  | some (res, _) =>
      assert (res == longBits.filter (VPred.gtVal 5).holds)
        "bitpacked: the fused peel's agreement broke"

def controlRawFor (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the off-fragment predicate evaluates on foR —
  -- the pushdown must refuse it (no projection without widening)
  assert ((computeOk (.raw (fun x => x % 2 == 0))
      (.forData { base := 10, offsets := [0, 2, 0, 5] })) = true)
    "the raw predicate was not refused by the foR pushdown"

def controlCorruptDict (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the corrupted carrier (code 9 over 2 values)
  -- evaluates — the corruption gate must refuse
  assertEq "corrupt-dict"
    (evalEncoded (.eqVal 1) (.dictData ⟨[1, 3], [0, 9, 1]⟩))
    (some ([1, 1], 2))

def controlDictAccount (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the dict account is PER-ROW (5) — the trick's
  -- whole point is the distinct-value count (2)
  assertEq "dict-account"
    ((evalEncoded (.gtVal 0) (.dictData smallLowCard)).map (·.2))
    (some 5)

def controlConstAccount (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the constant account is PER-ROW (1000) — the
  -- landslide case probes ONCE
  assertEq "const-account"
    (encodedProbes (.constData { count := 1000, value := some 7 }))
    1000

def specVortexCompute : Spec := Spec.ofList "vortex-compute"
  propCompute
  [ ("raw-for", controlRawFor)
  , ("corrupt-dict", controlCorruptDict)
  , ("dict-account", controlDictAccount)
  , ("const-account", controlConstAccount) ]
  8 20250922

/-! ## Suite 6: THE AFFINE KERNEL (the flatland absorbables — the
    arithmetic ops pushed INTO the encoding, E3) -/

-- the op column: add-const and mul-const (floats rejected by policy —
-- the hazard law note). The third op CROSSES the f53 horizon — the
-- integer lane stays exact (the hazard teeth exercise it).
def arithOps : List AOp :=
  [ AOp.addC 3, AOp.mulC 2, AOp.addC 9007199254740993, AOp.mulC 3 ]

/-- One (column, carrier, op) agreement instance: the absorbed
    carrier's decode IS the decoded column's map, with the absorb's
    own account — and every refusal is NAMED by the gate (the
    `checkCompute` shape, at the arithmetic grade). -/
def checkArith (nm : String) (c : Encoded) (op : AOp) : CheckResult :=
  match evalArith op c with
  | none => assert (!arithOk op c) s!"{nm}: refusal without the gate naming it"
  | some (res, probes) => do
      assert (arithOk op c) s!"{nm}: success without the gate"
      assert (res == (decodeOf c).map (AOp.eval op)) s!"{nm}: agreement broke"
      assert (probes == arithProbes op c) s!"{nm}: account broke"

/-! ### the per-(encoding, op) kernel pins (each matrix row's law) -/

-- rawVals × addC (the primitive wrapping row loop — the honest
-- fallback: the wrapping class, never a refusal)
theorem arith_raw_add :
    evalArith (AOp.addC 5) (.rawVals [300, 5, 300])
      = some ([305, 10, 305], 3) := rfl

-- bitPacked × mulC (the fused peel+op walk — the terminal's row loop)
theorem arith_bitpack_mul :
    evalArith (AOp.mulC 2) (.bitPackData 4 3 (packStream 4 [3, 1, 3]))
      = some ([6, 2, 6], 3) :=
  (evalArith_law _ _ (by rfl)).trans rfl

-- foR × addC — THE REF-BUMP: the offsets untouched, the account ZERO
-- (the study's "zero row work", pinned)
theorem arith_for_refbump :
    evalArith (AOp.addC 5) (.forData { base := 10, offsets := [0, 2, 0, 5] })
      = some ([15, 17, 15, 20], 0) :=
  (evalArith_law _ _ (by rfl)).trans rfl

-- foR × mulC — the REBASE+BUMP: base·3, offsets·3 (row work: the map)
theorem arith_for_rebase :
    evalArith (AOp.mulC 3) (.forData { base := 10, offsets := [0, 2] })
      = some ([30, 36], 2) :=
  (evalArith_law _ _ (by rfl)).trans rfl

-- dict × addC — the VALUES-MAP: the table [1,3,2] → [2,4,3] once, the
-- codes untouched; the account is the TABLE's length (3, not 4 rows)
theorem arith_dict_valuesmap :
    evalArith (AOp.addC 1) (.dictData (dictEncode [3, 1, 3, 2]))
      = some ([4, 2, 4, 3], 3) :=
  (evalArith_law _ _ (by decide)).trans rfl

-- constant × mulC — the scalar rewrite, checked (ONE application)
theorem arith_const_rewrite :
    evalArith (AOp.mulC 2) (.constData { count := 3, value := some 7 })
      = some ([14, 14, 14], 1) :=
  (evalArith_law _ _ (by rfl)).trans rfl

/-! ### the refusal faces (the checked-overflow + integrity gates) -/

-- inexact arithmetic REFUSES the constant rewrite (checked overflow —
-- never a silent wrap through a rewrite arm)
theorem arith_const_overflow_refused :
    evalArith (AOp.addC 1)
        (.constData { count := 1, value := some (2 ^ 64 - 1) }) = none :=
  hazard_refused_not_rounded _ _ (by rfl)

-- inexact arithmetic REFUSES the FoR pushdown (the exact-on-range
-- class: the offset 1 overflows the base 2^64−1)
theorem arith_for_overflow_refused :
    evalArith (AOp.addC 1)
        (.forData { base := 2 ^ 64 - 1, offsets := [0, 1] }) = none := rfl

-- the corrupted dict carrier (a code out of the table's range)
-- REFUSES the values-map — the integrity gate (computeOk's mirror)
theorem arith_dict_corrupt_refused :
    evalArith (AOp.addC 1) (.dictData ⟨[1, 3], [0, 9]⟩) = none := rfl

/-! ### the account teeth (the O(|dict|) + zero-row-work discipline) -/

/-- The 1000-row two-value dictionary (the O(|dict|) tooth's RUNTIME
    column — the kernel teeth below use the small twin, the compile-time
    account stays cheap). -/
def bigDictData : DictData :=
  dictEncode ((List.range 1000).map (fun i => i % 2))

/-- The kernel-tooth twin (6 rows, 2 values — the same shape). -/
def midDictData : DictData := dictEncode [1, 0, 1, 0, 1, 0]

-- THE O(|dict|) TOOTH: the values-map's account is the TABLE's length
-- (2) — the code count (6) never enters
theorem arith_dict_account :
    arithProbes (AOp.addC 1) (.dictData midDictData) = 2
      ∧ midDictData.codes.length = 6 := ⟨rfl, rfl⟩

theorem arith_dict_account_win :
    arithProbes (AOp.addC 1) (.dictData midDictData)
      < arithDecodeProbes (AOp.addC 1) (.dictData midDictData) :=
  dict_arith_win _ _ (by decide)

-- THE FoR REF-BUMP TOOTH: the add absorb's account is ZERO against
-- the 4-row baseline (the offsets are untouched)
theorem arith_for_zero_account :
    arithProbes (AOp.addC 5) (.forData { base := 10, offsets := [0, 2, 0, 5] })
        = 0
      ∧ arithDecodeProbes (AOp.addC 5)
          (.forData { base := 10, offsets := [0, 2, 0, 5] }) = 4 :=
  ⟨rfl, rfl⟩

theorem arith_for_zero_win :
    arithProbes (AOp.addC 5) (.forData { base := 10, offsets := [0, 2, 0, 5] })
      < arithDecodeProbes (AOp.addC 5)
          (.forData { base := 10, offsets := [0, 2, 0, 5] }) :=
  for_add_win _ _ (by decide)

-- the constant landslide: ONE application against a million rows
theorem arith_const_account :
    arithProbes (AOp.mulC 2)
        (.constData { count := 1000000, value := some 7 }) = 1
      ∧ arithDecodeProbes (AOp.mulC 2)
          (.constData { count := 1000000, value := some 7 }) = 1000000 := by
  refine ⟨rfl, ?_⟩
  show (List.replicate 1000000 7).length = 1000000
  exact List.length_replicate

-- the honest tie: the primitive row loop's account IS the row count
theorem arith_raw_tie :
    arithProbes (AOp.addC 1) (.rawVals [300, 5, 300])
      = arithDecodeProbes (AOp.addC 1) (.rawVals [300, 5, 300]) :=
  raw_arith_tie _ _

/-! ### the hazard law note's teeth (vortex-fork.md:299-303) -/

-- NO f53 cliff: a u64 value ABOVE the horizon rides the integer lane
-- EXACTLY — where an f64 hop (the fused-kernel hazard) rounds silently
theorem arith_hazard_no_cliff :
    AOp.eval (AOp.addC 0) (2 ^ 60 + 1) = 2 ^ 60 + 1 :=
  hazard_above_f53_exact _ (by decide) (by decide)

-- the wrapping kernel NEVER leaves the u64 domain (the integer lane's
-- face — no float exists in the path)
theorem arith_hazard_no_float_laneway (op : AOp) (x : Nat) :
    AOp.eval op x < 2 ^ 64 := hazard_no_f53_cliff op x

/-! ### the executable face (the sweep + the teeth, at runtime) -/

def propArith (_ : Tape) : CheckResult := do
  -- the fixture columns: every (encoding, op) cell, both faces
  for (nm, spec, vals) in computeCols do
    assert (inDomain spec vals) s!"{nm}: fixture column off-domain"
    match carrierOf? spec vals with
    | none => assert false s!"{nm}: carrier refused"
    | some c =>
        for op in arithOps do
          checkArith nm c op
  -- the LCG sweep: drawn columns over every in-domain spec
  let (cols, _) := drawMany 12 drawComputeCol (Tape.ofSeed 20250922)
  for vals in cols do
    for (nm, spec, _) in computeCols do
      if inDomain spec vals then
        match carrierOf? spec vals with
        | none => assert false s!"{nm}: carrier refused an in-domain column"
        | some c =>
            for op in arithOps do
              checkArith s!"{nm}-sweep" c op
  -- the hazard teeth, executably: the f53-horizon op rides the integer
  -- lane EXACTLY (an f64 hop would round above 2^53)
  let (res, _) := match evalArith (AOp.addC 9007199254740993)
      (.rawVals ((List.range 100).map (fun i => 2 ^ 60 + i))) with
  | some (res, _) => (res, ())
  | none => unreachable!
  assert (res == (List.range 100).map (fun i => 2 ^ 60 + i + 9007199254740993))
    "hazard: the f53-horizon op lost exactness"

def controlArithConstWrap (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the CONSTANT rewrite wraps (the wrapping class
  -- is the primitive arms' alone) — the checked overflow must refuse
  assertEq "const-checked-overflow"
    (evalArith (AOp.addC 1)
      (.constData { count := 1, value := some (2 ^ 64 - 1) }))
    (some ([0], 1))

def controlArithDictAccount (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the values-map's account is PER-CODE (1000) —
  -- the O(|dict|) discipline: the account is the table's length (2)
  assertEq "dict-arith-account"
    ((evalArith (AOp.addC 1) (.dictData bigDictData)).map (·.2)) (some 1000)

def controlArithForAccount (_ : Tape) : CheckResult :=
  -- SABOTAGE: claiming the ref-bump walks the rows (4 probes) — the
  -- account is ZERO (the offsets are untouched)
  assertEq "for-arith-account"
    ((evalArith (AOp.addC 5)
        (.forData { base := 10, offsets := [0, 2, 0, 5] })).map (·.2))
    (some 4)

def specVortexArith : Spec := Spec.ofList "vortex-arith"
  propArith
  [ ("const-checked-overflow", controlArithConstWrap)
  , ("dict-arith-account", controlArithDictAccount)
  , ("for-arith-account", controlArithForAccount) ]
  8 20250922

/-! ## Suite 5: the DType proto face (`Vortex.DTypeProto`) -/

-- the sweep list: a representative per DType constructor (both
-- nullability faces where the variant carries the flag)
def protoSweep : List DType :=
  [ .null, .bool true, .bool false, .primitive .u64 true,
    .decimal 10 2 false, .utf8 true, .binary false,
    .list (.primitive .u64 true) true,
    .fixedSizeList (.primitive .i32 false) 3 false,
    .map true (.utf8 false) (.primitive .u64 false) false,
    .struct [("a", .primitive .u64 false), ("b", .utf8 true)] true,
    .union [.primitive .u64 false, .utf8 false] true, .variant false,
    .extension "my.ext" (.primitive .u64 true) (some [1, 2]) true,
    .extension "my.ext" (.primitive .u64 false) none false,
    .fixedSizeTensor .f32 [2, 3] true ]

/-- The round-trip executability: the full face reads back every
    representative at the law's fuel (the decDType?_encDType law's
    compute face). -/
def propDTypeProto (_ : Tape) : CheckResult := do
  for d in protoSweep do
    assert ((decDType? ((encDTypeBody d).length + 1) (encDTypeBody d)) == some d)
      "proto: the round trip broke"
  -- the null body's known answer (field 1, length-delimited, empty
  -- payload: tag 10, length 0)
  assertEq "null-body" (encDTypeBody .null) [10, 0]

-- SABOTAGE: claiming the gate ADMITS the non-ASCII struct field name
-- (the emission boundary's refusal must fire, never a silent write)
def controlProtoAsciiName (_ : Tape) : CheckResult :=
  assert (inDomainDType (.struct [("\u00e9", .bool false)] false))
    "proto: the non-ASCII field name was ADMITTED"

-- SABOTAGE: claiming the gate ADMITS the non-ASCII extension id
def controlProtoAsciiExt (_ : Tape) : CheckResult :=
  assert (inDomainDType (.extension "\u00e9" (.bool false) none false))
    "proto: the non-ASCII extension id was ADMITTED"

-- SABOTAGE: claiming the bare tag (no length varint) DECODES — the
-- truncation refusal must fire, never a silent short read
def controlProtoTruncated (_ : Tape) : CheckResult :=
  assert ((decDType? 10 [10]).isSome)
    "proto: the truncated body DECODED"

-- SABOTAGE: claiming the canonical dialect ACCEPTS a trailing byte
def controlProtoTrailing (_ : Tape) : CheckResult :=
  assert ((decDType? 10 (encDTypeBody (.bool true) ++ [7])).isSome)
    "proto: the trailing byte was ACCEPTED"

-- SABOTAGE: claiming the null body's golden DRIFTED (a nonempty
-- payload) — the byte tie must catch it
def controlProtoGolden (_ : Tape) : CheckResult :=
  assertEq "null-body-drift" (encDTypeBody .null) [10, 1]

def specVortexProto : Spec := Spec.ofList "vortex-dtype-proto"
  propDTypeProto
  [ ("ascii-name", controlProtoAsciiName)
  , ("ascii-ext", controlProtoAsciiExt)
  , ("truncated", controlProtoTruncated)
  , ("trailing", controlProtoTrailing)
  , ("golden-null", controlProtoGolden) ]
  8 20250922

def main : IO UInt32 := do
  mainOfSuites [("Vortex", [specVortex, specVortexData, specVortexCompute,
    specVortexArith, specVortexProto])]


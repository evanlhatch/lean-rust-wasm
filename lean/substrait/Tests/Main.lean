/-
# Substrait Tests

Golden-file test driver (lean-linq pattern):

- Builds a typed `units |> filter (health > 0) |> project [health + regen]`
  plan, lowers it to `Proto.Plan`, and emits canonical substrait-explain text.
- Compares the text byte-for-byte with `Tests/golden/filter_project.substrait`.
- `--update` regenerates the golden.

Additional checks (all inside `main`, so they count as test results):

- `HasCol` head/tail instance search resolves both columns (by name).
- Consecutive `.filter` calls fuse into a single `Filter` rel (canonicalization
  at construction).
- The read-side evaluator: `filter` then `project` over an in-memory table.

Run from the package root:
    lake build SubstraitTests
    .lake/build/bin/SubstraitTests [--update]
-/
import Substrait

import TestKit
import Lean

open Substrait
open Substrait.Typed

/-- The units relation: health, regen — both nullable i32. -/
abbrev units : Schema :=
  [("health", .i32, true), ("regen", .i32, true)]

/-- Join test schemas: a left key and a right key, both nullable i32. -/
abbrev joinLeft : Schema := [("lk", .i32, true)]
abbrev joinRight : Schema := [("rk", .i32, true)]

/-- The join input schema: the concatenation of both sides (written out so
`HasCol` instance search reduces it; definitionally `joinLeft ++ joinRight`). -/
abbrev joinS : Schema :=
  [("lk", .i32, true), ("rk", .i32, true)]

/-- Aggregate input schema: a single nullable i32 value. -/
abbrev aggS : Schema := [("v", .i32, true)]

/-- The golden projection: total := health + regen (both polymorphic i32). -/
abbrev goldenOut : List (Projection units) :=
  [⟨"total", .i32, true, (col "health" .i32 true +. col "regen" .i32 true)⟩]

/-- The typed golden plan: `units |> filter (health > 0) |> project [health + regen]`. -/
abbrev goldenPlan : Rel units (projectOut units goldenOut) :=
  ((Builder.read "units" units
    |> Builder.filter (col "health" .i32 true >. litI32 0)
    |> Builder.project goldenOut).rel)

/-- The emitted canonical text of the golden plan. -/
def goldenText : Except String String :=
  Emit.Text.emit goldenPlan.toPlan

/-- The `Tests/` directory, resolved from an env override or the cwd. -/
def testDir : IO String := do
  let envDir ← IO.getEnv "LEAN_SUBSTRAIT_TEST_DIR"
  pure (envDir.getD "Tests")

def goldenPath : IO String := do
  pure ((← testDir) ++ "/golden/filter_project.substrait")

/- Property sweep: `decode ∘ emit = id` over GENERATED types (LSpec/plausible).
   SPEC §11.4: infinite-domain model properties get sampled sweeps; the type
   grammar is what the parked inversion proofs (Decode.lean) cover
   analytically — until the WF rewrite lands, this is the witness.
   LSpec gives what the hand-rolled loop lacked: a PINNED SEED (CI failures
   replay byte-identically) and SHRINKING (a failure minimizes itself — the
   `struct<>` decode bug found 2026-08 would have shrunk to `struct<>`
   automatically). -/
namespace PropSweep

open Plausible
open Substrait.Proto
open Substrait.Decode

/-- Random nullability (unspecified excluded — the typed layer never emits it). -/
def genNull : Gen Nullability := do
  let n ← Gen.chooseNat
  pure (if n % 2 == 0 then .nullable else .required)

/-- Sized random PType over the emit-able grammar (no userDefined — Emit.Text
    hard-errors there by design; the sweep stays inside the supported fragment). -/
def genType : Nat → Gen PType
  | 0 => do
    let n ← genNull
    Gen.oneOfWithDefault (pure (.bool n))
      [pure (.i8 n), pure (.i16 n), pure (.i32 n), pure (.i64 n),
       pure (.fp32 n), pure (.fp64 n), pure (.string n), pure (.binary n)]
  | fuel + 1 => do
    let n ← genNull
    let branch ← Gen.chooseNat
    match branch % 5 with
    | 0 => do pure (.list (← genType fuel) n)
    | 1 => do pure (.map (← genType fuel) (← genType fuel) n)
    | 2 => do
      let len ← Gen.chooseNat
      let rec go : Nat → Gen (List PType)
        | 0 => pure []
        | k + 1 => do pure ((← genType fuel) :: (← go k))
      pure (.struct (← go (len % 4)) n)
    | 3 => do
      let p ← Gen.chooseNat
      let s ← Gen.chooseNat
      pure (.decimal (p % 30 + 1) (s % 10) n)
    | _ =>
      Gen.oneOfWithDefault (pure (.bool n))
        [pure (.i32 n), pure (.i64 n), pure (.string n)]

/-- The plausible instance: fueled generation driven by the size parameter. -/
instance : ArbitraryFueled PType where
  arbitraryFueled := genType

instance : Arbitrary PType where
  arbitrary := Gen.sized (ArbitraryFueled.arbitraryFueled ·)

/-- Shrink toward subterms — a failing nested type minimizes to the smallest
    failing fragment (list → element, map → key/value, struct → fields). -/
partial def shrinkType : PType → List PType
  | .list e _ => e :: shrinkType e
  | .map k v _ => k :: v :: (shrinkType k ++ shrinkType v)
  | .struct fs _ => fs ++ fs.flatMap shrinkType
  | t => [t]

instance : Shrinkable PType where
  shrink t := (shrinkType t).filter (· != t)

/-- The round-trip property as a decidable check. -/
def roundtripOk (t : PType) : Bool :=
  match Substrait.Emit.Text.typeText t with
  | .error _ => false
  | .ok txt =>
    match parseType (txt.length + 1) txt.toList with
    | some (t', []) => t' == t
    | _ => false

/-- The suite: 2000 instances, PINNED SEED — a CI failure replays
    byte-identically, and plausible's shrinker minimizes any counterexample. -/
def suite : TestSeq :=
  checkPlausibleIO "decode∘emit = id (generated types)"
    (∀ t : PType, roundtripOk t = true)
    .done { numInst := 2000, randomSeed := some 20260819 }

/-- The negative control (TestKit.PropSpec discipline): rejects every `list`
    type. Caught only if the generator actually produces list constructors —
    verified 2026-08 (fails with a minimal `list<i64?>` counterexample). -/
def controlSuite : TestSeq :=
  checkPlausibleIO "sabotaged: lists rejected (must be caught)"
    (∀ t : PType, (match t with | .list .. => false | _ => true) = true)
    .done { numInst := 2000, randomSeed := some 20260819 }

/-- The property spec: sweep + its mandatory negative control. -/
def spec : TestKit.PropSpec :=
  { name := "decode∘emit round-trip"
  , suite := suite
  , control := controlSuite
  , controlName := "reject-all-lists" }

/- ── The expression sweep (5.3) ───────────────────────────────────────────

`decode ∘ emit = id` over GENERATED expressions.  The generator covers
exactly the TOTAL fragment of the `Emit.Text.expr`/`parseExpr` pair — the
domain is shrunk to the fragment, the property is not weakened:

- literals: bool, i8/i16/i32/i64 ints, strings (escaper exercised), EMPTY
  binary payloads, `null:t` — minus floats (`parseLiteral` has no float
  syntax: `toString 1.5` scans back as `.i64 1` with `.5` unconsumed) and
  minus non-empty binaries (`Emit.Text.literal` renders every binary as
  `{{binary}}`, payload dropped), and `null` always `nullable := true`
  (the parser sets it unconditionally).
- field refs with `segment := none` (the text grammar has no segment rule).
- calls over the fixed `fnNames` table with ≥ 1 argument (the grammar
  cannot parse `f()`), any emittable output type.
- `if_then` with ≥ 1 pair (the emitter's empty-pairs form `if_then(, _ -> …)`
  has no parse rule).
- casts with `returnNull`/`throwException` (the parser rejects the bare
  `::type` form — `unspecified` is unemittable by design).
- subqueries are unemittable; excluded. -/

/-- The fixed function table: emitter `Ctx` and decoder `FnCtx` agree on
    these anchors; colon-free unique names mean the emitter suppresses the
    `#anchor` and the parse resolves by bare name. -/
def fnNames : FnCtx := [("add", 1), ("gt", 2), ("sub", 3)]

/-- The emitter-side view of `fnNames` (kind 0 = function). -/
def exprEmitCtx : Substrait.Emit.Text.Ctx :=
  { urns := [], extensions := fnNames.map fun (n, a) => (1, 0, a, n) }

/-- Small literal-character alphabet: exercises the escaper (quote, backslash)
    without blowing up sample size (`unescape_escape` covers the rest). -/
def genLitChar : Gen Char :=
  Gen.oneOfWithDefault (pure 'a')
    [pure 'b', pure '9', pure '_', pure ' ', pure '\'', pure '\\']

/-- Strings of exactly `k` alphabet characters. -/
def genLitString : Nat → Gen String
  | 0 => pure ""
  | k + 1 => do pure (toString (← genLitChar) ++ (← genLitString k))

/-- Small-magnitude signed int. -/
def genInt : Gen Int := do
  let v ← Gen.chooseNat
  let s ← Gen.chooseNat
  pure (if s % 2 == 0 then (v % 97 : Int) else -((v % 97 : Int)))

/-- Random literal over the round-trippable fragment (see the boundary note
    above: no floats, empty binary only, `null` forced nullable). -/
def genLiteral (tfuel : Nat) : Gen Proto.Literal := do
  let branch ← Gen.chooseNat
  match branch % 5 with
  | 0 => do
    let v ← Gen.chooseNat; let n ← Gen.chooseNat
    pure { literalType := .bool (v % 2 == 0), nullable := n % 2 == 0 }
  | 1 => do
    let v ← genInt; let n ← Gen.chooseNat; let k ← Gen.chooseNat
    let lt : Proto.LiteralType := match k % 4 with
      | 0 => .i8 v | 1 => .i16 v | 2 => .i32 v | _ => .i64 v
    pure { literalType := lt, nullable := n % 2 == 0 }
  | 2 => do
    let len ← Gen.chooseNat; let n ← Gen.chooseNat
    pure { literalType := .string (← genLitString (len % 5)), nullable := n % 2 == 0 }
  | 3 => do
    let n ← Gen.chooseNat
    pure { literalType := .binary [], nullable := n % 2 == 0 }
  | _ =>
    pure { literalType := .null (← genType tfuel), nullable := true }

/-- A leaf expression: a field ref or a literal. -/
def genExprLeaf : Gen Proto.Expression := do
  let branch ← Gen.chooseNat
  if branch % 2 == 0 then do
    let n ← Gen.chooseNat
    pure (.field { ordinal := n % 8, segment := none })
  else
    pure (.literal (← genLiteral 1))

/-- Sized random expression over the total round-trippable fragment. -/
def genExpr : Nat → Gen Proto.Expression
  | 0 => genExprLeaf
  | fuel + 1 => do
    let branch ← Gen.chooseNat
    match branch % 7 with
    | 0 => do
      let f ← Gen.chooseNat
      let (_, anchor) := fnNames[f % fnNames.length]?.getD ("add", 1)
      let argc ← Gen.chooseNat
      let rec goArgs : Nat → Gen (List Proto.Expression)
        | 0 => pure []
        | k + 1 => do pure ((← genExpr fuel) :: (← goArgs k))
      pure (.scalarFunction anchor (← goArgs (argc % 3 + 1)) (← genType 2))
    | 1 => do
      let pc ← Gen.chooseNat
      let rec goPairs : Nat → Gen (List (Proto.Expression × Proto.Expression))
        | 0 => pure []
        | k + 1 => do pure ((← genExpr fuel, ← genExpr fuel) :: (← goPairs k))
      pure (.ifThen (← goPairs (pc % 2 + 1)) (← genExpr fuel))
    | 2 => do
      let fb ← Gen.chooseNat
      pure (.cast (← genExpr fuel) (← genType 2)
        (if fb % 2 == 0 then .returnNull else .throwException))
    | _ => genExprLeaf

/-- The plausible instance: fueled generation driven by the size parameter. -/
instance : ArbitraryFueled Proto.Expression where
  arbitraryFueled := genExpr

instance : Arbitrary Proto.Expression where
  arbitrary := Gen.sized (ArbitraryFueled.arbitraryFueled ·)

/-- Shrink toward subterms — a failing call/if_then/cast minimizes to the
    smallest failing fragment. -/
partial def shrinkExpr : Proto.Expression → List Proto.Expression
  | .scalarFunction _ args _ => args ++ args.flatMap shrinkExpr
  | .ifThen ifs els =>
    let subs := els :: (ifs.map (·.1) ++ ifs.map (·.2))
    subs ++ subs.flatMap shrinkExpr
  | .cast i _ _ => i :: shrinkExpr i
  | _ => []

instance : Shrinkable Proto.Expression where
  shrink := shrinkExpr

/-- The expression round-trip property as a decidable check: emit with the
    fixed context, parse at `length + 1` fuel, require full consumption and
    value equality. -/
def exprRoundtripOk (e : Proto.Expression) : Bool :=
  match Substrait.Emit.Text.expr exprEmitCtx e with
  | .error _ => false
  | .ok txt =>
    match parseExpr (txt.length + 1) fnNames txt.toList with
    | some (e', []) => e' == e
    | _ => false

/-- The suite: 1000 instances, pinned seed (CI failures replay
    byte-identically; the shrinker minimizes any counterexample). -/
def exprSuite : TestSeq :=
  checkPlausibleIO "decode∘emit = id (generated expressions)"
    (∀ e : Proto.Expression, exprRoundtripOk e = true)
    .done { numInst := 1000, randomSeed := some 20260909 }

/-- The mandatory negative controls (TestKit.PropSpec discipline), one per
    recursive form: each sabotaged suite is caught only if the generator
    actually reaches that constructor — the coverage witness for calls,
    if_then, and casts respectively. -/
def exprControl (name : String) (sabotage : Proto.Expression → Bool) : TestSeq :=
  checkPlausibleIO s!"sabotaged: {name} rejected (must be caught)"
    (∀ e : Proto.Expression, sabotage e = true)
    .done { numInst := 1000, randomSeed := some 20260909 }

def exprSpecCalls : TestKit.PropSpec :=
  { name := "expr decode∘emit round-trip"
  , suite := exprSuite
  , control := exprControl "calls" (fun e => match e with | .scalarFunction .. => false | _ => true)
  , controlName := "reject-all-calls" }

def exprSpecIfThen : TestKit.PropSpec :=
  { name := "expr decode∘emit round-trip"
  , suite := exprSuite
  , control := exprControl "if_then" (fun e => match e with | .ifThen .. => false | _ => true)
  , controlName := "reject-all-ifthen" }

def exprSpecCast : TestKit.PropSpec :=
  { name := "expr decode∘emit round-trip"
  , suite := exprSuite
  , control := exprControl "casts" (fun e => match e with | .cast .. => false | _ => true)
  , controlName := "reject-all-casts" }

end PropSweep

/-- Run the check suite via TestKit.CheckM: named checks accumulate;
    hard errors on intermediate IO (eval failures feeding later checks)
    `errorAbort` — the remaining sections are skipped with the error
    recorded (TestKit's abort channel; the driver collects via
    `runCheckMCollect` for the LSpec display). -/
def runChecks : TestKit.CheckM Unit := do
  -- 1. HasCol resolves by name, head and tail.
  TestKit.check "hasCol head" (TestKit.assert
    ((HasCol.index (s := units) (name := "health") (t := .i32) (n := true)) == 0) "")
  TestKit.check "hasCol tail" (TestKit.assert
    ((HasCol.index (s := units) (name := "regen") (t := .i32) (n := true)) == 1) "")

  -- 2. Consecutive filters fuse into a single Filter rel.
  let fused : Rel units units :=
    ((Builder.read "units" units
      |> Builder.filter (col "health" .i32 true >. litI32 0)
      |> Builder.filter (col "regen" .i32 true >. litI32 0)).rel)
  let fusedIsOne : Bool :=
    match fused with
    | .filter input _ => (match input with | .read _ _ => true | _ => false)
    | _ => false
  TestKit.check "filter fusion" (TestKit.assert fusedIsOne "")

  -- 3. The read-side evaluator: filter + project over an in-memory table.
  let src : Table units :=
    [![ some (Sigma.mk SType.i32 (Cell.i32 5)),  some (Sigma.mk SType.i32 (Cell.i32 2)) ],
     ![ some (Sigma.mk SType.i32 (Cell.i32 0)),  some (Sigma.mk SType.i32 (Cell.i32 2)) ],
     ![ some (Sigma.mk SType.i32 (Cell.i32 7)),  some (Sigma.mk SType.i32 (Cell.i32 3)) ]]
  let reader : Reader units := fun _ => pure src
  let filtered ←
    match eval reader (Builder.read "units" units |> Builder.filter (col "health" .i32 true >. litI32 0)).rel src with
    | .ok rows => pure rows
    | .error e => TestKit.errorAbort "eval filter" s!"eval error: {e}"
  TestKit.check "eval filter keeps alive rows only" (TestKit.assert (filtered.length == 2) "")
  let cellAt {s : Schema} (r : Row s) (k : Nat) (v : Int) : Bool :=
    match r.get k with
    | some (Sigma.mk SType.i32 (some (Cell.i32 x))) => x == v
    | _ => false
  let cellAtI64 {s : Schema} (r : Row s) (k : Nat) (v : Int) : Bool :=
    match r.get k with
    | some (Sigma.mk SType.i64 (some (Cell.i64 x))) => x == v
    | _ => false
  TestKit.check "eval filter keeps row 0 and 2" (TestKit.assert
    (match filtered with
     | [r0, r1] => cellAt r0 0 5 && cellAt r1 0 7
     | _ => false) "")

  -- 4. The typed projection evaluates.
  let projected ←
    match evalProject [(⟨"total", .i32, true, (col "health" .i32 true +. col "regen" .i32 true)⟩ : Projection units)]
        (filtered : Table units) with
    | .ok rows => pure rows
    | .error e => TestKit.errorAbort "eval project" s!"evalProject error: {e}"
  TestKit.check "eval project computes health + regen" (TestKit.assert
    (match projected with
     | [r0, r1] => cellAt r0 2 7 && cellAt r1 2 10
     | _ => false) "")

  -- 5. The emitter rejects Write / Extension rels (grammar has no rules).
  let badWrite : Proto.Plan :=
    { version := none, extensionUrns := [], extensions := [],
      relations := [.rel (.write { tableName := "t", op := "INSERT", tableSchema := none,
                                   input := .read { readType := .namedTable ["t"],
                                                    baseSchema := none, common := none },
                                   common := none })] }
  TestKit.check "emitter hard-fails on WriteRel" (TestKit.assert
    (match Emit.Text.emit badWrite with | .error _ => true | .ok _ => false) "")

  -- 6. A rel with no extensions emits no `=== Extensions` section.
  let plain : Proto.Plan :=
    { version := none, extensionUrns := [], extensions := [],
      relations := [.rel (.read { readType := .namedTable ["units"],
                                  baseSchema := some { fields := [.i32 .nullable, .i32 .nullable], names := ["health", "regen"] },
                                  common := none })] }
  let plainText ←
    match Emit.Text.emit plain with
    | .ok t => pure t
    | .error e => TestKit.errorAbort "plain emit" s!"plain emit error: {e}"
  TestKit.check "no extensions ⇒ no Extensions section" (TestKit.assert (!plainText.contains "=== Extensions") "")
  TestKit.check "plain Read renders canonically" (TestKit.assert
    (plainText.startsWith "=== Plan\nRead[units => health:i32?, regen:i32?]\n") "")

  -- 7. Join: inner join over a 2x2 product with a single match (2 == 2).
  let jsrc : Table joinS :=
    [![ some (Sigma.mk SType.i32 (Cell.i32 1)), some (Sigma.mk SType.i32 (Cell.i32 2)) ],
     ![ some (Sigma.mk SType.i32 (Cell.i32 2)), some (Sigma.mk SType.i32 (Cell.i32 3)) ]]
  let jreader : Reader joinS := fun _ => pure jsrc
  let jcond : Expr joinS .bool true :=
    col "lk" .i32 true ==. col "rk" .i32 true
  let jplan : Rel joinS joinS :=
    .join (Rel.read "L" joinLeft) (Rel.read "R" joinRight) jcond .inner
  let joined ←
    match eval jreader jplan jsrc with
    | .ok rows => pure rows
    | .error e => TestKit.errorAbort "eval join inner" s!"eval join error: {e}"
  TestKit.check "eval join inner keeps the single match" (TestKit.assert (joined.length == 1) "")
  TestKit.check "eval join inner row is [2,2]" (TestKit.assert
    (match joined with
     | [r0] => cellAt r0 0 2 && cellAt r0 1 2
     | _ => false) "")

  -- 8. Join: left join pads the unmatched left row with a `none` right cell.
  let jlplan : Rel joinS joinS :=
    .join (Rel.read "L" joinLeft) (Rel.read "R" joinRight) jcond .left
  let lj ←
    match eval jreader jlplan jsrc with
    | .ok rows => pure rows
    | .error e => TestKit.errorAbort "eval join left" s!"eval left join error: {e}"
  TestKit.check "eval join left emits matched then padded row" (TestKit.assert (lj.length == 2) "")
  TestKit.check "eval join left row 0 is the match, row 1 is [1,none]" (TestKit.assert
    (match lj with
     | [r0, r1] =>
         cellAt r0 0 2 && cellAt r0 1 2 &&
         cellAt r1 0 1 &&
         (match r1.get 1 with
          | some (Sigma.mk SType.i32 none) => true
          | _ => false)
     | _ => false) "")

  -- 9. Aggregate: two groups (keys 1 vs 2), count + sum measures.
  let asrc : Table aggS :=
    [![ some (Sigma.mk SType.i32 (Cell.i32 1)) ],
     ![ some (Sigma.mk SType.i32 (Cell.i32 2)) ],
     ![ some (Sigma.mk SType.i32 (Cell.i32 1)) ],
     ![ some (Sigma.mk SType.i32 (Cell.i32 3)) ]]
  let areader : Reader aggS := fun _ => pure asrc
  let countM : Measure aggS :=
    { sig := FunctionSig.mkSig "count" "extension:io.substrait:functions_aggregate" [] .i64 true true,
      args := [] }
  let sumM : Measure aggS :=
    { sig := FunctionSig.mkSig "sum" "extension:io.substrait:functions_aggregate" [(.i32, true)] .i32 true true,
      args := [pack (col "v" .i32 true)] }
  let aplan : Rel aggS (aggregateOut aggS [pack (col "v" .i32 true)] [countM, sumM]) :=
    .aggregate (Rel.read "agg" aggS) [pack (col "v" .i32 true)] [countM, sumM]
  let aggd ←
    match eval areader aplan asrc with
    | .ok rows => pure rows
    | .error e => TestKit.errorAbort "eval aggregate" s!"eval aggregate error: {e}"
  TestKit.check "eval aggregate emits three buckets (first-seen key order)" (TestKit.assert (aggd.length == 3) "")
  TestKit.check "eval aggregate counts and sums per group" (TestKit.assert
    (match aggd with
     | [r1, r2, r3] =>
         cellAt r1 0 1 && cellAtI64 r1 1 2 && cellAt r1 2 2 &&
         cellAt r2 0 2 && cellAtI64 r2 1 1 && cellAt r2 2 2 &&
         cellAt r3 0 3 && cellAtI64 r3 1 1 && cellAt r3 2 3
     | _ => false) "")

  -- 9.5. Text wire round trip (lean-v3 step 8, D6): decode(emit(golden))
  --    is the plan, and re-emitting it is byte-identical.
  match goldenText with
  | .error msg => TestKit.errorAbort "round-trip emit" s!"round-trip: emit failed: {msg}"
  | .ok rtt => do
      TestKit.check "decode∘emit = id (golden plan)" (TestKit.assert
        (Decode.parsePlan rtt == some goldenPlan.toPlan) "")
      match Decode.parsePlan rtt with
      | some p =>
          TestKit.check "emit∘decode is byte-identical (golden text)" (TestKit.assert
            (match Emit.Text.emit p with | .ok s => s == rtt | .error _ => false) "")
      | none => TestKit.errorAbort "round-trip parse" "round-trip: parse failed"

  -- 9.6. Type round-trip sweep (the executable witness for the type layer —
  --    the proved inversion is the fuel-monotonicity chunk; see Decode.lean).
  let testTypes : List (String × Proto.PType) :=
    [ ("boolean", .bool .required), ("boolean?", .bool .nullable)
    , ("i8", .i8 .required), ("i16?", .i16 .nullable), ("i32", .i32 .required)
    , ("i64?", .i64 .nullable), ("fp32", .fp32 .required), ("fp64?", .fp64 .nullable)
    , ("string?", .string .nullable), ("binary", .binary .required)
    , ("decimal<10,2>", .decimal 10 2 .required)
    , ("list<i32?>", .list (.i32 .nullable) .required)
    , ("map<i8, string?>", .map (.i8 .required) (.string .nullable) .required)
    , ("struct<i32, list<i64?>?>", .struct [.i32 .required, .list (.i64 .nullable) .nullable] .required) ]
  for (txt, ty) in testTypes do
    TestKit.check s!"type round-trip: {txt}" (TestKit.assert
      (match Decode.parseType (txt.length + 1) txt.toList with
       | some (t', []) => t' == ty
       | _ => false) "")

  -- 9.6b. The master type-inversion theorem (parseType_typeText) witnessed on
  -- the same 14 sweep types: re-emit each type, then parse it back at the
  -- theorem's exact fuel (`typeDepth ty`), not the convenient `length+1`.
  -- The result must be the original type with everything consumed — the
  -- proposition the theorem proves, evaluated.  The emitted text must also
  -- equal the sweep's hand-written text (the two are definitionally tied at
  -- the grammar level).
  for (txt, ty) in testTypes do
    TestKit.check s!"type inversion master (golden): {txt}" (TestKit.assert
      (match Emit.Text.typeText ty with
       | .ok b =>
           Decode.parseType (Decode.typeDepth ty) b.toList == some (ty, []) && b == txt
       | .error _ => false) "")

  -- 9.7. Expression round-trip sweep (refs, calls, literals, if_then, cast).
  let fnCtx : Decode.FnCtx := [("gt", 1), ("add", 2)]
  let testExprs : List String :=
    [ "$0", "add($0, $1):i32?", "gt($0, 0:i32):boolean?"
    , "if_then(gt($0, 0:i32):boolean? -> $1, _ -> 0:i32)"
    , "'hello'", "42", "-7:i16?", "true", "null:string" ]
  for txt in testExprs do
    TestKit.check s!"expr parses: {txt}" (TestKit.assert
      ((Decode.parseExpr (txt.length + 1) fnCtx txt.toList).isSome) "")

  -- 10. Wire round-trip (D12): SKIPPED — ProtoGen/protobuf excluded from v1.
  --    Re-add with the protobuf dep when binary Substrait interchange is needed.
  pure ()

/-- The golden test proper + CLI driver (TestKit harness: LSpec reporting,
    TestKit.Golden for the byte-tie). -/
def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  match goldenText with
  | .error msg =>
    IO.eprintln s!"FAIL: golden plan failed to emit: {msg}"
    return 1
  | .ok text => do
    let path ← goldenPath
    let gr ← TestKit.Golden.checkAgainstGolden "golden filter_project" text path update
    match gr with
    | .error e => IO.eprintln e; return 1
    | .ok () =>
      if update then
        IO.println s!"golden regenerated: {path}"
        return 0
      else do
        let results ← TestKit.runCheckMCollect runChecks
        let code ← TestKit.mainOfSuites [("Substrait", TestKit.suiteOf results)]
        if code != 0 then return code
        IO.println "all green"
        -- the property sweep WITH its mandatory negative control
        -- (TestKit.PropSpec: the property must pass AND the sabotaged sibling
        -- must be caught — a sweep whose generator never reaches the failing
        -- fragment is flagged as vacuous)
        TestKit.runSpecs [PropSweep.spec, PropSweep.exprSpecCalls,
          PropSweep.exprSpecIfThen, PropSweep.exprSpecCast]

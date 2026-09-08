/-
# LeanSubstrait Tests

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
    lake build LeanSubstraitTests
    .lake/build/bin/LeanSubstraitTests [--update]
-/
import LeanSubstrait

import LSpec
import TestKit
import Lean

open LeanSubstrait
open LeanSubstrait.Typed

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

open Plausible LSpec
open LeanSubstrait.Proto
open LeanSubstrait.Decode.Text

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
  match LeanSubstrait.Emit.Text.typeText t with
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

end PropSweep

/-- Run the check suite, collecting (name, result) pairs. Hard errors on
    intermediate IO (eval failures feeding later checks) abort the remaining
    sections with the error recorded — the old driver's fail-fast, kept. -/
def runChecks : IO (List (String × TestKit.CheckResult)) := do
  let mut results : List (String × TestKit.CheckResult) := []
  -- 1. HasCol resolves by name, head and tail.
  results := results ++ [("hasCol head", TestKit.assert
    ((HasCol.index (s := units) (name := "health") (t := .i32) (n := true)) == 0) "")]
  results := results ++ [("hasCol tail", TestKit.assert
    ((HasCol.index (s := units) (name := "regen") (t := .i32) (n := true)) == 1) "")]

  -- 2. Consecutive filters fuse into a single Filter rel.
  let fused : Rel units units :=
    ((Builder.read "units" units
      |> Builder.filter (col "health" .i32 true >. litI32 0)
      |> Builder.filter (col "regen" .i32 true >. litI32 0)).rel)
  let fusedIsOne : Bool :=
    match fused with
    | .filter input _ => (match input with | .read _ _ => true | _ => false)
    | _ => false
  results := results ++ [("filter fusion", TestKit.assert fusedIsOne "")]

  -- 3. The read-side evaluator: filter + project over an in-memory table.
  let src : Table units :=
    [![ some (Sigma.mk SType.i32 (Cell.i32 5)),  some (Sigma.mk SType.i32 (Cell.i32 2)) ],
     ![ some (Sigma.mk SType.i32 (Cell.i32 0)),  some (Sigma.mk SType.i32 (Cell.i32 2)) ],
     ![ some (Sigma.mk SType.i32 (Cell.i32 7)),  some (Sigma.mk SType.i32 (Cell.i32 3)) ]]
  let reader : Reader units := fun _ => pure src
  let filtered ←
    match eval reader (Builder.read "units" units |> Builder.filter (col "health" .i32 true >. litI32 0)).rel src with
    | .ok rows => pure rows
    | .error e => return results ++ [("eval filter", (.error s!"eval error: {e}" : TestKit.CheckResult))]
  results := results ++ [("eval filter keeps alive rows only", TestKit.assert (filtered.length == 2) "")]
  let cellAt {s : Schema} (r : Row s) (k : Nat) (v : Int) : Bool :=
    match r.get k with
    | some (Sigma.mk SType.i32 (some (Cell.i32 x))) => x == v
    | _ => false
  let cellAtI64 {s : Schema} (r : Row s) (k : Nat) (v : Int) : Bool :=
    match r.get k with
    | some (Sigma.mk SType.i64 (some (Cell.i64 x))) => x == v
    | _ => false
  results := results ++ [("eval filter keeps row 0 and 2", TestKit.assert
    (match filtered with
     | [r0, r1] => cellAt r0 0 5 && cellAt r1 0 7
     | _ => false) "")]

  -- 4. The typed projection evaluates.
  let projected ←
    match evalProject [(⟨"total", .i32, true, (col "health" .i32 true +. col "regen" .i32 true)⟩ : Projection units)]
        (filtered : Table units) with
    | .ok rows => pure rows
    | .error e => return results ++ [("eval project", (.error s!"evalProject error: {e}" : TestKit.CheckResult))]
  results := results ++ [("eval project computes health + regen", TestKit.assert
    (match projected with
     | [r0, r1] => cellAt r0 2 7 && cellAt r1 2 10
     | _ => false) "")]

  -- 5. The emitter rejects Write / Extension rels (grammar has no rules).
  let badWrite : Proto.Plan :=
    { version := none, extensionUrns := [], extensions := [],
      relations := [.rel (.write { tableName := "t", op := "INSERT", tableSchema := none,
                                   input := .read { readType := .namedTable ["t"],
                                                    baseSchema := none, common := none },
                                   common := none })] }
  results := results ++ [("emitter hard-fails on WriteRel", TestKit.assert
    (match Emit.Text.emit badWrite with | .error _ => true | .ok _ => false) "")]

  -- 6. A rel with no extensions emits no `=== Extensions` section.
  let plain : Proto.Plan :=
    { version := none, extensionUrns := [], extensions := [],
      relations := [.rel (.read { readType := .namedTable ["units"],
                                  baseSchema := some { fields := [.i32 .nullable, .i32 .nullable], names := ["health", "regen"] },
                                  common := none })] }
  let plainText ←
    match Emit.Text.emit plain with
    | .ok t => pure t
    | .error e => return results ++ [("plain emit", (.error s!"plain emit error: {e}" : TestKit.CheckResult))]
  results := results ++ [("no extensions ⇒ no Extensions section", TestKit.assert (!plainText.contains "=== Extensions") "")]
  results := results ++ [("plain Read renders canonically", TestKit.assert
    (plainText.startsWith "=== Plan\nRead[units => health:i32?, regen:i32?]\n") "")]

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
    | .error e => return results ++ [("eval join inner", (.error s!"eval join error: {e}" : TestKit.CheckResult))]
  results := results ++ [("eval join inner keeps the single match", TestKit.assert (joined.length == 1) "")]
  results := results ++ [("eval join inner row is [2,2]", TestKit.assert
    (match joined with
     | [r0] => cellAt r0 0 2 && cellAt r0 1 2
     | _ => false) "")]

  -- 8. Join: left join pads the unmatched left row with a `none` right cell.
  let jlplan : Rel joinS joinS :=
    .join (Rel.read "L" joinLeft) (Rel.read "R" joinRight) jcond .left
  let lj ←
    match eval jreader jlplan jsrc with
    | .ok rows => pure rows
    | .error e => return results ++ [("eval join left", (.error s!"eval left join error: {e}" : TestKit.CheckResult))]
  results := results ++ [("eval join left emits matched then padded row", TestKit.assert (lj.length == 2) "")]
  results := results ++ [("eval join left row 0 is the match, row 1 is [1,none]", TestKit.assert
    (match lj with
     | [r0, r1] =>
         cellAt r0 0 2 && cellAt r0 1 2 &&
         cellAt r1 0 1 &&
         (match r1.get 1 with
          | some (Sigma.mk SType.i32 none) => true
          | _ => false)
     | _ => false) "")]

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
    | .error e => return results ++ [("eval aggregate", (.error s!"eval aggregate error: {e}" : TestKit.CheckResult))]
  results := results ++ [("eval aggregate emits three buckets (first-seen key order)", TestKit.assert (aggd.length == 3) "")]
  results := results ++ [("eval aggregate counts and sums per group", TestKit.assert
    (match aggd with
     | [r1, r2, r3] =>
         cellAt r1 0 1 && cellAtI64 r1 1 2 && cellAt r1 2 2 &&
         cellAt r2 0 2 && cellAtI64 r2 1 1 && cellAt r2 2 2 &&
         cellAt r3 0 3 && cellAtI64 r3 1 1 && cellAt r3 2 3
     | _ => false) "")]

  -- 9.5. Text wire round trip (lean-v3 step 8, D6): decode(emit(golden))
  --    is the plan, and re-emitting it is byte-identical.
  match goldenText with
  | .error msg => return results ++ [("round-trip emit", (.error s!"round-trip: emit failed: {msg}" : TestKit.CheckResult))]
  | .ok rtt => do
    results := results ++ [("decode∘emit = id (golden plan)", TestKit.assert
      (Decode.Text.parsePlan rtt == some goldenPlan.toPlan) "")]
    match Decode.Text.parsePlan rtt with
    | some p =>
      results := results ++ [("emit∘decode is byte-identical (golden text)", TestKit.assert
        (match Emit.Text.emit p with | .ok s => s == rtt | .error _ => false) "")]
    | none => return results ++ [("round-trip parse", (.error "round-trip: parse failed" : TestKit.CheckResult))]

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
    results := results ++ [(s!"type round-trip: {txt}", TestKit.assert
      (match Decode.Text.parseType (txt.length + 1) txt.toList with
       | some (t', []) => t' == ty
       | _ => false) "")]

  -- 9.6b. The master type-inversion theorem (parseType_typeText) witnessed on
  -- the same 14 sweep types: re-emit each type, then parse it back at the
  -- theorem's exact fuel (`typeDepth ty`), not the convenient `length+1`.
  -- The result must be the original type with everything consumed — the
  -- proposition the theorem proves, evaluated.  The emitted text must also
  -- equal the sweep's hand-written text (the two are definitionally tied at
  -- the grammar level).
  for (txt, ty) in testTypes do
    results := results ++ [(s!"type inversion master (golden): {txt}", TestKit.assert
      (match Emit.Text.typeText ty with
       | .ok b =>
           Decode.Text.parseType (Decode.Text.typeDepth ty) b.toList == some (ty, []) && b == txt
       | .error _ => false) "")]

  -- 9.7. Expression round-trip sweep (refs, calls, literals, if_then, cast).
  let fnCtx : Decode.Text.FnCtx := [("gt", 1), ("add", 2)]
  let testExprs : List String :=
    [ "$0", "add($0, $1):i32?", "gt($0, 0:i32):boolean?"
    , "if_then(gt($0, 0:i32):boolean? -> $1, _ -> 0:i32)"
    , "'hello'", "42", "-7:i16?", "true", "null:string" ]
  for txt in testExprs do
    results := results ++ [(s!"expr parses: {txt}", TestKit.assert
      ((Decode.Text.parseExpr (txt.length + 1) fnCtx txt.toList).isSome) "")]

  -- 10. Wire round-trip proof-of-life (lean-v3 D12): semantic plan → bridge →
  --    protobuf bytes → decode → re-encode. Byte-identity is the assertion:
  --    deterministic encode makes byte-equality equivalent to field-wise
  --    value equality, and it pins determinism itself.
  -- 10. Wire round-trip (D12): SKIPPED — ProtoGen/protobuf excluded from v1.
  --    Re-add with the protobuf dep when binary Substrait interchange is needed.

  return results

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
        let results ← runChecks
        let code ← TestKit.mainOfSuites [("LeanSubstrait", TestKit.suiteOf results)]
        if code != 0 then return code
        IO.println "all green"
        -- the property sweep WITH its mandatory negative control
        -- (TestKit.PropSpec: the property must pass AND the sabotaged sibling
        -- must be caught — a sweep whose generator never reaches the failing
        -- fragment is flagged as vacuous)
        TestKit.runSpecs [PropSweep.spec]

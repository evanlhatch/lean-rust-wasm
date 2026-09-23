/-
# GuestlangStd Tests

Doctrine $4 test suite for the std intrinsics (GuestlangStd.StrOps):

- ofName? resolves every expected Lean declaration name to the correct
  Intrinsic constructor (GuestlangStd.strlen, GuestlangStd.strcat,
  GuestlangStd.streq, SchemaLang.string_len, and the string-`==`
  LCNF spellings String.decEq / instBEqString.beq).
- ofName? rejects unknown names (none).
- strlen/strcat/streq oracle semantics on known ASCII inputs produce
  known outputs (the differential oracle).
- Intrinsic metadata: runtimeName and resultWasmTy return the expected
  wasm-level strings.
- Negative control: a deliberately-wrong equality that MUST fail -
  proves the test harness catches failures.
- Exhaustiveness: the metadata folds (ofName?/runtimeName/resultWasmTy)
  cover all constructors (compiled by Lean's match-exhaustiveness check).
- Axiom gate via Tests/Axioms.lean (pre-existing).

No LSpec import - TestKit is the blessed surface.
-/

import GuestlangStd
import TestKit

open GuestlangStd

-- ToString instances needed by TestKit.assertEq (the type derives Repr
-- but not ToString).
instance : ToString Intrinsic where
  toString
    | .strlen => "strlen"
    | .strcat => "strcat"
    | .streq => "streq"
    | .strof => "strof"

instance : ToString (Option Intrinsic) where
  toString
    | none => "none"
    | some i => "some (" ++ toString i ++ ")"

/-- A named check sequence accumulating into a TestSeq. -/
def runChecks : TestKit.CheckM Unit := do

  -- 1. ofName? resolves GuestlangStd.strlen -> .strlen.
  TestKit.check "ofName? GuestlangStd.strlen"
    (TestKit.assertEq "GuestlangStd.strlen"
      (Intrinsic.ofName? `GuestlangStd.strlen) (some .strlen))

  -- 2. ofName? resolves GuestlangStd.strcat -> .strcat.
  TestKit.check "ofName? GuestlangStd.strcat"
    (TestKit.assertEq "GuestlangStd.strcat"
      (Intrinsic.ofName? `GuestlangStd.strcat) (some .strcat))

  -- 3. ofName? resolves SchemaLang.string_len -> .strlen (the raw
  --    evaluator's wire-up contract name).
  TestKit.check "ofName? SchemaLang.string_len"
    (TestKit.assertEq "SchemaLang.string_len"
      (Intrinsic.ofName? `SchemaLang.string_len) (some .strlen))

  -- 4. ofName? rejects unknown names.
  TestKit.check "ofName? rejects unknown"
    (TestKit.assertEq "unknown name"
      (Intrinsic.ofName? `GuestlangStd.unknown) none)

  -- 4b. ofName? resolves the streq spellings: the wrapper name + the
  --      LCNF spellings a string `==` compiles to (the W9.6 gap-3
  --      lowering — the backend emitted `call String.decEq`).
  TestKit.check "ofName? GuestlangStd.streq"
    (TestKit.assertEq "GuestlangStd.streq"
      (Intrinsic.ofName? `GuestlangStd.streq) (some .streq))
  TestKit.check "ofName? String.decEq"
    (TestKit.assertEq "String.decEq"
      (Intrinsic.ofName? `String.decEq) (some .streq))
  TestKit.check "ofName? instBEqString.beq"
    (TestKit.assertEq "instBEqString.beq"
      (Intrinsic.ofName? `instBEqString.beq) (some .streq))

  -- 5. strlen oracle: known ASCII strings.
  TestKit.check "strlen oracle: empty string"
    (TestKit.assertEq "strlen(\"\")" (strlen "") 0)
  TestKit.check "strlen oracle: short ASCII"
    (TestKit.assertEq "strlen(\"hello\")" (strlen "hello") 5)
  TestKit.check "strlen oracle: multi-byte ASCII"
    (TestKit.assertEq "strlen(\"hello world\")" (strlen "hello world") 11)

  -- 6. strcat oracle: known ASCII strings.
  TestKit.check "strcat oracle: empty + empty"
    (TestKit.assertEq "strcat(\"\", \"\")" (strcat "" "") "")
  TestKit.check "strcat oracle: non-empty + empty"
    (TestKit.assertEq "strcat(\"a\", \"\")" (strcat "a" "") "a")
  TestKit.check "strcat oracle: empty + non-empty"
    (TestKit.assertEq "strcat(\"\", \"b\")" (strcat "" "b") "b")
  TestKit.check "strcat oracle: two non-empty"
    (TestKit.assertEq "strcat(\"hello\", \" world\")" (strcat "hello" " world") "hello world")

  -- 6b. streq oracle: known ASCII pairs (reflexivity, length mismatch,
  --      content mismatch, empty pairs).
  TestKit.check "streq oracle: reflexive"
    (TestKit.assertEq "streq(\"hello\", \"hello\")" (streq "hello" "hello") true)
  TestKit.check "streq oracle: length mismatch"
    (TestKit.assertEq "streq(\"hello\", \"hell\")" (streq "hello" "hell") false)
  TestKit.check "streq oracle: same length, different bytes"
    (TestKit.assertEq "streq(\"hello\", \"hella\")" (streq "hello" "hella") false)
  TestKit.check "streq oracle: both empty"
    (TestKit.assertEq "streq(\"\", \"\")" (streq "" "") true)
  TestKit.check "streq oracle: empty vs non-empty"
    (TestKit.assertEq "streq(\"\", \"a\")" (streq "" "a") false)
  TestKit.check "streq oracle: shared prefix"
    (TestKit.assertEq "streq(\"abcdef\", \"abcxyz\")" (streq "abcdef" "abcxyz") false)

  -- 7. resultWasmTy is correct for each intrinsic.
  TestKit.check "resultWasmTy .strlen"
    (TestKit.assertEq "strlen -> i64" (Intrinsic.resultWasmTy .strlen) "i64")
  TestKit.check "resultWasmTy .strcat"
    (TestKit.assertEq "strcat -> i32" (Intrinsic.resultWasmTy .strcat) "i32")
  TestKit.check "resultWasmTy .streq"
    (TestKit.assertEq "streq -> i32" (Intrinsic.resultWasmTy .streq) "i32")

  -- 7b. strof oracle: the W9.6 decode lane.s string atom (ASCII rows).
  TestKit.check "strof oracle: ascii run"
    (TestKit.assertEq "strof([p, q])" (strof (String.toList "pq")) "pq")
  TestKit.check "strof oracle: empty"
    (TestKit.assertEq "strof([])" (strof []) "")

  -- 7c. ofName? resolves the decode lane.s spelling.
  TestKit.check "ofName? String.ofList"
    (TestKit.assertEq "String.ofList"
      (Intrinsic.ofName? `String.ofList) (some .strof))

  -- 8. runtimeName is the wasm-level primitive name.
  TestKit.check "runtimeName .strlen"
    (TestKit.assertEq "strlen -> string_len" (Intrinsic.runtimeName .strlen) "string_len")
  TestKit.check "runtimeName .strcat"
    (TestKit.assertEq "strcat -> string_cat" (Intrinsic.runtimeName .strcat) "string_cat")
  TestKit.check "runtimeName .streq"
    (TestKit.assertEq "streq -> string_eq" (Intrinsic.runtimeName .streq) "string_eq")
  TestKit.check "runtimeName .strof"
    (TestKit.assertEq "strof -> string_oflist" (Intrinsic.runtimeName .strof) "string_oflist")

  pure ()

/-- The negative control: a deliberately wrong assertion that MUST fail.
    If this passes, the test harness is broken (vacuous-green detection). -/
def negativeControl : TestKit.CheckM Unit := do
  TestKit.check "NEGATIVE CONTROL: strlen(\"hello\") = 42 (deliberately wrong)"
    (TestKit.assertEq "strlen(\"hello\")" (strlen "hello") 42)

/-- The driver: run checks (must pass), run negative control (must fail),
    report both as one suite. -/
def main : IO UInt32 := do
  -- Run the real checks.
  let checks <- TestKit.runCheckMCollect runChecks
  -- Run the negative control: it must fail (vacuous-green check).
  let controlResults <- TestKit.runCheckMCollect negativeControl
  let controlCaught : Bool :=
    match controlResults with
    | [(_, .error _)] => true
    | _ => false
  let controlCheckResult : TestKit.CheckResult :=
    if controlCaught then .ok ()
    else .error "NEGATIVE CONTROL NOT CAUGHT - test harness is vacuous"
  let allChecks : List (String × TestKit.CheckResult) :=
    checks ++ [("negative-control (caught=" ++ toString controlCaught ++ ")", controlCheckResult)]
  TestKit.mainOfChecks "GuestlangStd" allChecks
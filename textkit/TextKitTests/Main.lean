/-
# TextKitTests.Main — the behavior pins + the negative controls

1. The leaf scanners' positive pins (pchar/tok/satisfy/eof/peek/lookAhead).
2. The combinator pins (many/some/sepBy/TextKit.optional/between, save/jump
   backtracking, <|> best-error by farthest position + the tie's
   expected-set union, label, withSuggest).
3. The mined scanners' pins (scanNat/scanIdent/expect/startsWith) +
   the scan-then-print round-trips.
4. The error-shape pins: malformed input refuses with the RIGHT
   ParseError shape — position, expected-set, context, suggest.

The runner is TestKit's (`mainOfSuites` — doctrine 12 §9: tests are
data folds). Two Specs: the leaf scanners (scanners + mined) and the
combinators (combinators + alternation + labels + the error shapes).
The SABOTAGE cases are the Specs' NEGATIVES — each must FAIL, guarded
by TestKit's vacuity tripwire (a control that stops failing is louder
than a broken pin; the old exactly-once check is its instance).

Proof-side pins (the reduction checks + the axiom gate's #print axioms
lines) live in TextKitTests.Axioms.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import TextKit
import TestKit.Harness
import TextKitTests.Axioms

open TextKit
open TestKit

/-- Two parse outcomes agree (value or error shape). -/
def exceptEq [BEq α] (a b : Except ParseError (α × List Char)) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error e, .error e' => e == e'
  | _, _ => false

/-- Extract the error (the negative controls' face). -/
def errOf (r : Except ParseError (α × List Char)) : Option ParseError :=
  match r with
  | .error e => Option.some e
  | .ok _ => none

/-- The default error shape (comparing against constructed values). -/
def plainErr (pos : Nat) (expected : List String) : ParseError :=
  { pos, expected, context := [], suggest := none }

/-! ## Sabotage fixtures — the negatives' producers -/

/-- SABOTAGED literal: a `pchar` that accepts ANY char (never refuses). -/
def sabAnyChar (c : Char) : GParser Char := satisfy s!"'{c}'" (fun _ => true)

/-- SABOTAGED optional: on a non-matching input it fabricates a match
    instead of yielding `none`. -/
def sabOptional : GParser (Option Char) :=
  orElse (do let c ← pchar 'a'; pure (Option.some c)) (pure (Option.some 'z'))

/-- SABOTAGED backtrack: the `save`d position never jumped back to —
    the consumed input stays consumed. -/
def sabNoJump : GParser Char :=
  do let _ ← pchar 'a'
     let _ ← pchar 'a'
     pchar 'a'

/-! ## The specs (TestKit's data folds) -/

/-- The leaf scanners (the scanner + mined pins) + their sabotage
    controls. -/
def scannerSpec : Spec :=
  Spec.ofList "TextKit.leaf scanners — pchar/tok/satisfy/eof/peek/lookAhead + the mined scanners"
    (fun _ => do
      assert (exceptEq (runG (pchar 'a') "abc".toList) (.ok ('a', "bc".toList)))
        "pchar consumes"
      assert (exceptEq (runG (tok "ab") "abc".toList) (.ok ("ab", ['c'])))
        "tok consumes"
      assert (exceptEq (runG (satisfy "digit" Char.isDigit) "7x".toList) (.ok ('7', ['x'])))
        "satisfy consumes"
      assert (exceptEq (runG eof ([] : List Char)) (.ok ((), [])))
        "eof ok"
      assert (exceptEq (runG peek "ab".toList) (.ok (Option.some 'a', "ab".toList)))
        "peek no consume"
      assert (exceptEq (runG (do let _ ← lookAhead (pchar 'a'); pchar 'a') "ab".toList)
          (.ok ('a', ['b'])))
        "lookAhead rewinds"
      assert ((scanNat "42,".toList) == Option.some (42, [',']))
        "scanNat digits"
      assert ((scanNat "x".toList) == none)
        "scanNat empty refuses"
      assert ((scanIdent "abc+".toList) == Option.some ("abc", ['+']))
        "scanIdent bare"
      assert ((scanIdent "1abc".toList) == none)
        "scanIdent non-alpha refuses"
      assert ((expect "ab" "abc".toList) == Option.some ['c'])
        "expect prefix"
      assert ((expect "ab" "xc".toList) == none)
        "expect non-prefix refuses"
      assert ((startsWith "abc".toList "ab") == true)
        "startsWith true"
      assert ((startsWith "xc".toList "ab") == false)
        "startsWith false"
      -- the round-trips (the print ∘ parse shape: scan back what was printed)
      assert ((scanNat (toString 12345).toList) == Option.some (12345, []))
        "nat round trip"
      assert ((scanIdent (("ok1" ++ "!").toList)) == Option.some ("ok1", ['!']))
        "ident round trip")
    [ ("the sabotaged literal refuses a wrong char",
        fun _ =>
          assert (errOf (runG (sabAnyChar 'a') "z".toList)
            == Option.some (plainErr 0 ["'a'"]))
            "control fired: the sabotaged literal accepted a wrong char")
    , ("the sabotaged scanNat folds past the stop",
        fun _ =>
          assert ((scanNat "1a".toList) == Option.some (11, ['a']))
            "control fired: the scan-stop sabotage") ]
    4 42

/-- The combinators (combinator + alternation + label pins + the
    error-shape pins) + their sabotage controls. -/
def combinatorSpec : Spec :=
  Spec.ofList "TextKit.combinators — many/some/sepBy/optional/between/backtrack/<|>/label + the error shapes"
    (fun _ => do
      assert (exceptEq (runG (many (pchar 'a')) "aab".toList) (.ok (['a','a'], ['b'])))
        "many consumes"
      assert (exceptEq (runG (many (pchar 'a')) "bbb".toList) (.ok ([], "bbb".toList)))
        "many zero"
      assert (exceptEq (runG (many (TextKit.optional (pchar 'a'))) "bbb".toList)
          (.ok ([none], "bbb".toList)))
        "many zero-progress stop"
      assert (exceptEq (runG (some (pchar 'a')) "aa".toList) (.ok (['a','a'], [])))
        "some consumes"
      assert (exceptEq (runG (sepBy (pchar 'a') (pchar ',')) "a,a,b".toList)
          (.ok (['a','a'], [',', 'b'])))
        "sepBy consumes (failed sep attempt rewinds)"
      assert (exceptEq (runG (sepBy (pchar 'a') (pchar ',')) "b".toList)
          (.ok ([], "b".toList)))
        "sepBy zero"
      assert (exceptEq (runG (TextKit.optional (pchar 'a')) "ab".toList)
          (.ok (Option.some 'a', ['b'])))
        "optional some"
      assert (exceptEq (runG (TextKit.optional (pchar 'a')) "b".toList)
          (.ok (none, "b".toList)))
        "optional none"
      assert (exceptEq (runG (between (pchar '(') (pchar ')') (tok "ab")) "(ab)x".toList)
          (.ok ("ab", ['x'])))
        "between"
      assert (exceptEq (runG (do
              let saved ← save
              let _ ← pchar 'a'
              let _ ← pchar 'a'
              jump saved
              pchar 'a') "aab".toList)
          (.ok ('a', ['a', 'b'])))
        "save/jump backtrack"
      assert ((recognize (pchar 'a') "ab".toList) == Option.some ('a', ['b'])
          ∧ (recognize (pchar 'a') "b".toList) == none)
        "recognize bridge"
      -- left consumes then fails deeper; right fails shallower: the
      -- DEEPER error wins
      assert ((errOf (runG (orElse (do let _ ← tok "a"; tok "b") (tok "cd")) "ax".toList))
          == Option.some (plainErr 1 ["'b'"]))
        "farthest wins"
      -- same position: the expected-sets UNION (left's order first)
      assert ((errOf (runG (orElse (pchar 'x') (pchar 'y')) "z".toList))
          == Option.some (plainErr 0 ["'x'", "'y'"]))
        "tie unions expected"
      -- left success wins outright
      assert (exceptEq (runG (orElse (pchar 'a') (pchar 'b')) "ab".toList) (.ok ('a', ['b'])))
        "left success wins"
      assert ((errOf (runG (label "item" (pchar 'x')) "y".toList))
          == Option.some { pos := 0, expected := ["item"], context := ["item"], suggest := none })
        "label sets expected + context"
      assert (
          match errOf (runG (label "outer" (label "inner" (pchar 'x'))) "y".toList) with
          | Option.some e => e.context == ["outer", "inner"]
          | none => false)
        "label stacks context"
      assert (
          match errOf (runG (withSuggest "did you mean 'x'?" (pchar 'x')) "y".toList) with
          | Option.some e => e.suggest == Option.some "did you mean 'x'?"
          | none => false)
        "withSuggest fills the hook"
      -- the error shapes: malformed input refuses with the RIGHT shape
      assert ((errOf (runG (do let _ ← tok "ab"; tok "cd") "abXc".toList))
          == Option.some (plainErr 2 ["'cd'"]))
        "wrong literal refuses at the right pos"
      assert ((errOf (runG (do let _ ← pchar 'a'; eof) "ax".toList))
          == Option.some (plainErr 1 ["<end of input>"]))
        "eof refuses leftover input"
      assert ((errOf (runG (pchar 'a') "".toList)) == Option.some (plainErr 0 ["'a'"]))
        "empty input refuses pchar"
      assert ((errOf (runG (some (pchar 'a')) "b".toList)) == Option.some (plainErr 0 ["'a'"]))
        "some refuses zero matches")
    [ ("the sabotaged optional still yields none",
        fun _ =>
          assert (exceptEq (runG sabOptional "b".toList) (.ok (none, "b".toList)))
            "control fired: the sabotaged optional fabricated a match")
    , ("the dropped-jump sequence still rewinds",
        fun _ =>
          assert (exceptEq (runG sabNoJump "aab".toList) (.ok ('a', ['a', 'b'])))
            "control fired: the consumed input did NOT rewind (the jump was dropped)") ]
    4 42

def main : IO UInt32 := do
  TestKit.mainOfSuites
    [ ("TextKit.scanners", [scannerSpec])
    , ("TextKit.combinators", [combinatorSpec]) ]

/-
# TextKit Tests — the lifted parser core's pins

1. Behavioral pins of the moved surface (the byte-tie face: the scanners'
   accept/reject behavior is pinned HERE in TextKit too, not only by
   substrait's goldens): scanNat/scanInt/scanIdent/scanName over positive
   inputs, expect/startsWith over the prefix kit.
2. The failure paths (the negative controls): the scanners MUST reject —
   empty digits, non-alpha heads, bare backslashes, non-prefixes.
3. The inversion kit runs: unescape∘escape = some on real text.
4. THE SUPER-POWER PINS (the wave's deliverables):
   - Grammar: emit→parseTokens ROUND TRIPS (byte-exact emission
     recognized back into the token list, the inversion-law shape
     `pOfLift g ((emit g) ++ rest) = some (tokensOf g, rest)`), the
     ordered alt, the GWF checker + its negative control;
   - Diag: the farthest-failure driver reports the DEEPEST labeled
     expectation's consumed position + set, the renderer's bytes;
   - FormatLaws: the rendering-level append associativity on concrete
     bytes + the hard-line indent atom.
5. DetSpec sabotage control (the DetSpec discipline): a deliberately wrong
   scanner pin that MUST be caught — proves these checks bite.
-/
import TextKit
import TestKit

open TextKit TestKit

/-- The sample GWF grammar for the round-trip pins: a header token, a
    repetition, a trailer token (the `invert_rep_behind_tok` shape). -/
def sampleGrammar : Grammar.Grammar :=
  Grammar.Grammar.seq
    [ Grammar.Grammar.tok "begin"
    , Grammar.Grammar.rep (Grammar.Grammar.tok "x")
    , Grammar.Grammar.tok "end" ]

/-- The Grammar pins: emit→parseTokens round trips (byte-exact emission
    recognized back, payload = the token list), the ordered alt, the GWF
    checker + the negative controls. -/
def grammarChecks : CheckResult := do
  -- the round trip: parseTokens of the emission recovers the tokens
  _ ← assertEq "grammar round trip"
    (Grammar.parseTokens sampleGrammar ("beginxendZZ".toList))
    (some (["begin", "x", "end"], ['Z', 'Z']))
  -- the inversion-law shape: pOfLift g ((emit g) ++ rest) = some (tokensOf g, rest)
  _ ← assertEq "grammar invert shape"
    (Grammar.pOfLift sampleGrammar (Grammar.emit sampleGrammar ++ "rest").toList)
    (some (Grammar.tokensOf sampleGrammar, "rest".toList))
  -- alt: ordered (first-success) choice
  _ ← assertEq "grammar alt"
    (Grammar.parseTokens (Grammar.Grammar.alt [Grammar.Grammar.tok "a", Grammar.Grammar.tok "b"]) "bzz".toList)
    (some (["b"], ['z', 'z']))
  -- GWF + the checker agree on the sample
  _ ← assertEq "grammar GWF" (Grammar.checkGWF sampleGrammar) true
  -- negative: a wrong head token refuses
  _ ← assertEq "grammar negative"
    (Grammar.parseTokens sampleGrammar "bogus".toList)
    none
  -- negative: a nullable rep body is not GWF (the fuel rule)
  _ ← assertEq "grammar GWF negative"
    (Grammar.checkGWF (Grammar.Grammar.seq [Grammar.Grammar.rep (Grammar.Grammar.tok "")]))
    false
  .ok ()

/-- The Diag pins: the farthest-failure driver reports the deepest
    labeled expectation (position = the consumed length at it, the
    expected set), the renderer's bytes, and the success lane. -/
def diagChecks : CheckResult := do
  -- a labeled failure at a DEFERRED point (after 'a' consumed from "ax!"):
  -- the driver reports the consumed position + the expectation
  let (pos, expected) : Nat × List String :=
    match Diag.farthestFailure (do
        Diag.DParser.consumeCharD 'a' "expected 'a'"
        Diag.DParser.labels "expected 'b'"
          (fun cs => match cs with | 'b' :: rest => (some ((), rest), []) | _ => (none, [])))
        "ax!".toList with
    | .fail p e => (p, e)
    | .ok _ => (0, [])
  _ ← assertEq "farthestFailure pos" pos 1
  _ ← assertEq "farthestFailure expected" expected ["expected 'b'"]
  -- the renderer's bytes (column = pos + 1)
  _ ← assertEq "renderDiag"
    (Diag.renderDiag 7 (Diag.Diag.fail 1 ["a", "b"] : Diag.Diag Unit))
    "line 7, col 2: expected 'a', 'b'"
  -- a success reports .ok
  _ ← assertEq "farthestFailure ok"
    (match Diag.farthestFailure (fun cs => (some (42, cs), [])) "xy".toList with
      | .ok a => some a
      | .fail _ _ => none)
    (some 42)
  .ok ()

/-- The FormatLaws pins: the rendering-level append associativity on
    concrete bytes (the `render_assoc` bytes) and the hard-line indent
    atom. -/
def formatChecks : CheckResult := do
  _ ← assertEq "format assoc render"
    (FormatLaws.renderFmt ((Std.Format.text "ab" ++ Std.Format.text "c") ++ Std.Format.text "d"))
    (FormatLaws.renderFmt (Std.Format.text "ab" ++ (Std.Format.text "c" ++ Std.Format.text "d")))
  _ ← assertEq "format assoc bytes"
    (FormatLaws.renderFmt (Std.Format.text "ab" ++ Std.Format.text "c"))
    "abc"
  -- a hard line at indent 2 renders as newline + the indent spaces
  _ ← assertEq "format line atom"
    (FormatLaws.renderGo 2 (Std.Format.line ++ Std.Format.text "x"))
    ("\n" ++ FormatLaws.spaces 2 ++ "x")
  .ok ()

/-- The positive pins. -/
def pinChecks : CheckResult := do
  -- the monad + scanners over real input
  _ ← assertEq "scanNat 42" (scanNat "42,".toList) (some (42, [',']))
  _ ← assertEq "scanInt -7" (scanInt "-7x".toList) (some (-7, ['x']))
  _ ← assertEq "scanIdent bare" (scanIdent "abc+".toList) (some ("abc", ['+']))
  _ ← assertEq "scanName quoted" (scanName ("\"a b\";".toList)) (some ("a b", [';']))
  _ ← assertEq "expect prefix" (expect "ab" "abc".toList) (some ['c'])
  _ ← assertEq "startsWith" (startsWith "abc".toList "ab") true
  -- the text primitives (lifted from Emit.Text)
  _ ← assertEq "escape table" (escape "a\nb") "a\\nb"
  _ ← assertEq "name bare" (name "abc") "abc"
  _ ← assertEq "name quoted" (name "a b") "\"a b\""
  -- the inversions RUN
  _ ← assertEq "unescape∘escape" (unescape (escape "a\"b\nc")) (some "a\"b\nc")
  .ok ()

/-- The failure paths — the scanners reject what the grammar rejects. -/
def rejectChecks : CheckResult := do
  _ ← assertEq "scanNat empty" (scanNat "x".toList) none
  _ ← assertEq "scanIdent non-alpha" (scanIdent "1abc".toList) none
  _ ← assertEq "unescape bare backslash" (unescape "a\\") none
  _ ← assertEq "expect non-prefix" (expect "ab" "xc".toList) none
  _ ← assertEq "startsWith non-prefix" (startsWith "xc".toList "ab") false
  _ ← assertEq "scanQuotedRaw unclosed" (scanQuotedRaw '"' [] "abc".toList) none
  .ok ()

/-- The deterministic pair: the true pin (scanNat stops at the non-digit,
    yielding 1 with rest "a") + the sabotage control (MUST be caught:
    scanNat does NOT fold past the stop into 11) — proves the pins bite. -/
def sabotageSpec : DetSpec :=
  { name := "scanNat \"1a\" = some (1, [a])"
  , check := assertEq "stop-at-nondigit" (scanNat "1a".toList) (some (1, ['a']))
  , control := assertEq "sabotage" (scanNat "1a".toList) (some (11, ['a']))
  , controlName := "scanNat \"1a\" == 11 (wrong — must fail)" }

-- Axiom tripwires on the headline inversions (build-time prints; the
-- axiom gate's TextKit section flags the surface).
#print axioms TextKit.unescape_escape
#print axioms TextKit.scanName_name
#print axioms TextKit.scanIdent_of_identifier
#print axioms TextKit.scanQuotedRaw_escape
#print axioms TextKit.expect_self
#print axioms TextKit.startsWith_self
#print axioms TextKit.Grammar.invert_tok
#print axioms TextKit.Grammar.invert_core
#print axioms TextKit.Grammar.invert_rep
#print axioms TextKit.Grammar.invert_rep_behind_tok
#print axioms TextKit.Grammar.checkGWF_eq_true_iff_GWF
#print axioms TextKit.Diag.farthestFailure_ok
#print axioms TextKit.FormatLaws.render_assoc
#print axioms TextKit.FormatLaws.fmtAppend_inj

def main : IO UInt32 := do
  let code ← mainOfChecks "TextKit"
    [ ("pins", pinChecks)
    , ("rejections", rejectChecks)
    , ("grammar", grammarChecks)
    , ("diag", diagChecks)
    , ("format", formatChecks)
    ]
  if code != 0 then return code
  TestKit.runDets [sabotageSpec]

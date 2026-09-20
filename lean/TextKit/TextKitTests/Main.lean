/-
# TextKit Tests — the lifted parser core's pins

1. Behavioral pins of the moved surface (the byte-tie face: the scanners'
   accept/reject behavior is pinned HERE in TextKit too, not only by
   substrait's goldens): scanNat/scanInt/scanIdent/scanName over positive
   inputs, expect/startsWith over the prefix kit.
2. The failure paths (the negative controls): the scanners MUST reject —
   empty digits, non-alpha heads, bare backslashes, non-prefixes.
3. The inversion kit runs: unescape∘escape = some on real text.
4. DetSpec sabotage control (the DetSpec discipline): a deliberately wrong
   scanner pin that MUST be caught — proves these checks bite.
-/
import TextKit
import TestKit

open TextKit TestKit

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

def main : IO UInt32 := do
  let code ← mainOfChecks "TextKit"
    [ ("pins", pinChecks)
    , ("rejections", rejectChecks)
    ]
  if code != 0 then return code
  TestKit.runDets [sabotageSpec]

/-
# TextKitTests.Axioms — the axiom gate's pins

`#print axioms` over the headline lemmas + the proof-side reduction pins.
Expected (verified): every line reports the CORE TRIPLE ONLY —
[propext, Classical.choice, Quot.sound] (pulled through core's List/
String lemmas), `scanIdent_none_of_not_alpha` even fewer. Anything
beyond the core triple — a sorryAx, a native_decide, a new axiom — is a
gate failure, not a style note.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

module

import TextKit

/-! the reduction pins (proof-side, kernel-checked) -/

/-- scanNat reads a decimal literal. -/
example : TextKit.scanNat "42,".toList = some (42, [',']) := by decide

/-- scanIdent scans a bare identifier up to the delimiter. -/
example : TextKit.scanIdent "abc+".toList = some ("abc", ['+']) := by decide

/-- expect consumes the literal prefix. -/
example : TextKit.expect "ab" "abc".toList = some ['c'] := by decide

/-- the combinator surface: many's fuel engine is STRUCTURAL on the fuel
    (no wf opacity — the kernel reduces it; the behavior pins live in
    Main.lean's runtime group). -/
example : (TextKit.manyGo (TextKit.pchar 'a') 2 ⟨0, "aab".toList⟩)
    = .ok (['a', 'a'], ⟨2, ['b']⟩) := by rfl

/-! the axiom pins (build-time prints; the gate's TextKit section) -/

#print axioms TextKit.startsWith_self
#print axioms TextKit.expect_self
#print axioms TextKit.startsWith_cons_ne
#print axioms TextKit.expect_cons_ne
#print axioms TextKit.scanIdent_none_of_not_alpha
#print axioms TextKit.scanNat_none_of_not_digit
#print axioms TextKit.scanIdent_of_identifier

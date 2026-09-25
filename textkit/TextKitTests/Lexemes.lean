/-
# TextKitTests.Lexemes — the shared lexeme constructors' teeth

TextKit.Grammar.Lexemes' constructors (`constCharLex`/`identAtom`/
`natAtom`) each carry ~9 proof obligations discharged ONCE at the
generic shape — this file exercises every obligation at a concrete
instance (a theorem tooth per field, applied — a constructor that
grows a vacuous field fails HERE) and pins the mandatory negative
controls (15-patterns #5): the SABOTAGED shapes whose honest
constructor refuses — the accept-any-char scan (head_fail's witness),
the chain-drop scan (the ident-atom's `h → p` premise is what keeps a
success's run nonempty — `consumes`'), and the raw uncanonical scan
(the nat-atom's canonical guard — `scan_exact`'s).

The adopters' suites ride their own lanes (KitTests pins the
registry's `charLex`/`nameAtom`/`codeAtom` rows;
TextKitTests.GrammarSlice pins the slice's `boolLex`).

Core-only; the axiom pins are `#print axioms` at build time
(the GrammarSlice form — this file is NON-module).
-/

import TextKit.Grammar.Lexemes
import TestingKit.Harness

open TestingKit
open TextKit

namespace TextKit.LexemesSlice

/-! ## the test ident classes (the generic ident-atom's instantiation) -/

/-- An alphabetic head class. -/
def testHead (c : Char) : Bool := c.isAlpha

/-- An alphanumeric run class (a SUPERSET of the head class — the
    chain premise's honest shape). -/
def testRun (c : Char) : Bool := c.isAlpha || c.isDigit

theorem testHead_chain : ∀ c, testHead c = true → testRun c = true := by
  intro c hc
  show (c.isAlpha || c.isDigit) = true
  rw [show c.isAlpha = true from hc]
  simp

/-- The test ident-atom: the shared constructor at the test classes. -/
def testAtom : Lexeme String := TextKit.identAtom "<test>" testHead testRun testHead_chain

/-! ## the const-char lexeme's obligations (one tooth per field) -/

/-- `scan_exact` + `scan_off` + the value discipline, at a concrete
    instance: the scan eats exactly the printed char and yields the
    fixed value. -/
theorem charLex_scan_face (k : Nat) :
    (constCharLex 'a' ()).scan ⟨k, ['a', 'b']⟩ = .ok ((), ⟨k + 1, ['b']⟩) := rfl

/-- `print_scan`'s face: the print re-scans to the value over ANY
    suffix (the constructor's field, applied). -/
theorem charLex_print_scan_face (k : Nat) (sfx : List Char) :
    (constCharLex 'a' ()).scan
        ⟨k, ((constCharLex 'a' ()).print ()).toList ++ sfx⟩
      = .ok ((), ⟨k + ((constCharLex 'a' ()).print ()).length, sfx⟩) :=
  (constCharLex 'a' ()).print_scan k () sfx (by decide) rfl

/-- `head_fail`'s face: a head mismatch refuses (the constructor's
    field, applied). -/
theorem charLex_head_fail_face :
    ∃ e, (constCharLex 'a' ()).scan ⟨2, ['b']⟩ = .error e :=
  (constCharLex 'a' ()).head_fail ⟨2, ['b']⟩ (by decide)

/-- `consumes`' face. -/
theorem charLex_consumes_face :
    (⟨3, ['b']⟩ : Cursor).cs.length < (⟨2, ['a', 'b']⟩ : Cursor).cs.length :=
  (constCharLex 'a' ()).consumes _ _ _ (charLex_scan_face 2)

/-- `head_ne`'s face: the literal head fails the empty text (the
    tailOk-nil lemma's content). -/
theorem charLex_head_ne_face :
    HeadSpec.matches (constCharLex 'a' ()).head [] = false :=
  (constCharLex 'a' ()).head_ne

/-! ## the ident-atom's obligations -/

/-- The maximal-munch scan: the run stops at the first `p`-failing
    char, the head class gates the START. -/
theorem identAtom_scan_face :
    testAtom.scan ⟨0, ['a', 'b', '1', '+']⟩ = .ok ("ab1", ⟨3, ['+']⟩) := rfl

/-- The head refusal: a `p`-passing but `h`-failing lead char is a
    REFUSAL (the guard discipline — a bare maximal run would accept). -/
theorem identAtom_head_refusal :
    testAtom.scan ⟨0, ['1', 'a']⟩ = .error (ParseError.base 0 ["<test>"]) := rfl

/-- The empty refusal. -/
theorem identAtom_nil_refusal :
    testAtom.scan ⟨0, []⟩ = .error (ParseError.base 0 ["<test>"]) := rfl

/-- `print_scan`'s face at the ident-atom. -/
theorem identAtom_print_scan_face :
    testAtom.scan ⟨0, (testAtom.print "ab1").toList ++ ['+']⟩
      = .ok ("ab1", ⟨3, ['+']⟩) :=
  testAtom.print_scan 0 "ab1" ['+'] (by
    show testAtom.pre "ab1" = true
    simp [testAtom, TextKit.identAtom, TextKit.identOk, testHead, testRun])
    (by
      show (Option.some testRun).all
        (fun p => (['+'] : List Char).head?.all (fun c => !p c)) = true
      simp [testRun])

/-- `consumes`' face at the ident-atom (the chain premise's payoff: the
    run is never empty on a success). -/
theorem identAtom_consumes_face :
    (⟨3, ['+']⟩ : Cursor).cs.length < (⟨0, ['a', 'b', '1', '+']⟩ : Cursor).cs.length :=
  testAtom.consumes _ _ _ identAtom_scan_face

/-- `head_ne`'s face at the ident-atom. -/
theorem identAtom_head_ne_face :
    HeadSpec.matches testAtom.head [] = false :=
  testAtom.head_ne

/-! ## the nat-atom's obligations -/

/-- The canonical scan: `42` scans back off its spelling, leaving the
    non-digit suffix (the munch's boundary). -/
theorem natAtom_scan_face :
    natAtom.scan ⟨0, ['4', '2', 'x']⟩ = .ok (42, ⟨2, ['x']⟩) := rfl

/-- THE canonical guard's tooth: a leading zero is a refusal — the raw
    `01` is not the spelling of the value it scans to, and
    `scan_exact` demands the raw. -/
theorem natAtom_leading_zero_refusal :
    natAtom.scan ⟨0, ['0', '1']⟩ = .error (ParseError.base 0 ["<nat>"]) := rfl

/-- The empty refusal (zero digits is `none` in the raw scan). -/
theorem natAtom_nil_refusal :
    natAtom.scan ⟨0, []⟩ = .error (ParseError.base 0 ["<nat>"]) := rfl

/-- `print_scan`'s face at the nat-atom. -/
theorem natAtom_print_scan_face (k : Nat) :
    natAtom.scan ⟨k, (natAtom.print 42).toList ++ ['x']⟩
      = .ok (42, ⟨k + (natAtom.print 42).length, ['x']⟩) :=
  natAtom.print_scan k 42 ['x'] rfl (by
    show (Option.some Char.isDigit).all
      (fun p => (['x'] : List Char).head?.all (fun c => !p c)) = true
    decide)

/-- `consumes`' face at the nat-atom. -/
theorem natAtom_consumes_face :
    (⟨2, ['x']⟩ : Cursor).cs.length < (⟨0, ['4', '2', 'x']⟩ : Cursor).cs.length :=
  natAtom.consumes _ _ _ natAtom_scan_face

/-! ## the negative controls (the sabotaged shapes the constructor refuses) -/

/-- SABOTAGE (the head-guard drop): an accept-any-char scan — the
    head-mismatch SUCCESS that `head_fail`/`scan_head` refuse. -/
def sabCharScan : GParser Unit := fun cur =>
  .ok ((), ⟨cur.off + 1, cur.cs.drop 1⟩)

/-- The witness: the head mismatches AND the sabotaged scan succeeds —
    the honest constructor's `head_fail` field exists to kill this. -/
theorem sabCharScan_control :
    (HeadSpec.lit "a").matches ['b'] = false ∧
    sabCharScan ⟨2, ['b']⟩ = .ok ((), ⟨3, []⟩) := ⟨rfl, rfl⟩

/-- SABOTAGE (the chain drop): an `h`-guarded scan whose run class was
    dropped — the `h`-led input scans to the EMPTY run (zero progress:
    the `consumes` violation the `h → p` premise kills). -/
def sabNoChainScan : GParser String := fun cur =>
  match cur.cs with
  | c :: _ =>
      if testHead c then .ok (String.ofList [], cur)  -- zero progress
      else .error (ParseError.base cur.off ["<sab>"])
  | [] => .error (ParseError.base cur.off ["<sab>"])

/-- The witness: the lead char passes the head class AND the sabotaged
    scan consumed nothing. -/
theorem sabNoChain_control :
    testHead 'a' = true ∧
    sabNoChainScan ⟨0, ['a', 'b']⟩ = .ok ("", ⟨0, ['a', 'b']⟩) := by
  refine ⟨by decide, ?_⟩
  rfl

/-- SABOTAGE (the canonical-guard drop): the RAW `scanNat` accepts the
    leading-zero spelling — the value whose print is NOT the raw text
    (the `scan_exact` violation the nat-atom's guard kills). -/
theorem sabUncanonicalNat_control :
    scanNat ['0', '1'] = .some (1, []) ∧ (toString 1).toList ≠ ['0', '1'] := by
  refine ⟨rfl, ?_⟩
  decide

/-! ## the runtime spec (the behavior pins + the controls) -/

/-- Two parse outcomes agree (value or error shape; `runG`'s face). -/
def exceptEq [BEq α] (a b : Except ParseError (α × List Char)) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error e, .error e' => e == e'
  | _, _ => false

/-- The shared constructors' spec: the scan faces at runtime + the
    three sabotages (each control must FAIL — the vacuity tripwire). -/
def lexemesSpec : Spec :=
  Spec.ofList "TextKit.lexemes — the shared constructors: const-char/ident/nat scans + the sabotages"
    (fun _ => do
      assert (exceptEq (runG (constCharScan 'a' ()) ['a', 'b'])
          (.ok ((), ['b'])))
        "const-char: consumes the char"
      assert (exceptEq (runG (constCharScan 'a' ()) ['b'])
          (.error (ParseError.base 0 ["'a'"])))
        "const-char: a wrong char refuses"
      assert (exceptEq (runG testAtom.scan ['a', 'b', '1', '+'])
          (.ok ("ab1", ['+'])))
        "ident-atom: the maximal munch stops at the run class"
      assert (exceptEq (runG testAtom.scan ['1', 'a'])
          (.error (ParseError.base 0 ["<test>"])))
        "ident-atom: the head class gates the start"
      assert (exceptEq (runG natAtom.scan ['4', '2', 'x'])
          (.ok (42, ['x'])))
        "nat-atom: the canonical scan + the munch boundary"
      assert (exceptEq (runG natAtom.scan ['0', '1'])
          (.error (ParseError.base 0 ["<nat>"])))
        "nat-atom: a leading zero refuses"
      assert (exceptEq (runG natAtom.scan [])
          (.error (ParseError.base 0 ["<nat>"])))
        "nat-atom: zero digits refuse")
    [ ("the accept-any-char sabotage still refuses a wrong char",
        fun _ =>
          assert (exceptEq (runG sabCharScan ['b'])
              (.error (ParseError.base 0 ["'a'"])))
            "control fired: the head-guard drop accepted a wrong char")
    , ("the chain-drop sabotage makes progress",
        fun _ =>
          assert (exceptEq (runG sabNoChainScan ['a', 'b'])
              (.ok ("ab", ['b'])))
            "control fired: the dropped chain premise consumed input")
    , ("the raw scanNat is canonical on a leading zero",
        fun _ =>
          assert ((match runG natAtom.scan ['0', '1'] with
            | .ok (n, _) => toString n == "01"
            | .error _ => false))
            "control fired: the canonical guard refused a non-canonical spelling") ]
    4 42

/-! ## the axiom pins -/

#print axioms charLex_scan_face
#print axioms charLex_print_scan_face
#print axioms charLex_head_fail_face
#print axioms identAtom_scan_face
#print axioms identAtom_print_scan_face
#print axioms natAtom_scan_face
#print axioms natAtom_leading_zero_refusal
#print axioms sabCharScan_control
#print axioms sabNoChain_control
#print axioms sabUncanonicalNat_control

end TextKit.LexemesSlice

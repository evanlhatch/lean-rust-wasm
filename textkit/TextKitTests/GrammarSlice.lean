/-
# TextKitTests.GrammarSlice — the grammar layer's proof-of-life slice

The design of record: `notes/design-grammar-layer-v2.md` §7. This is
the slice's FIX-FREE shape (the flat formats' face — the migration
blocker's answer): ONE tiny recursion-free format

    Toks := tok*          tok := 'x' (yielding `false`) | 'y' (yielding `true`)

— a `rep`-top value under a `rel` (the code-registry's flat row shape:
no `fix`, no `self` node anywhere) through grammar → certificate →
BOTH round-trip laws → negative controls. The recursion-shaped
sibling (`PTree`, the fix-topped face) is parked with its walls in
`notes/grammar-slice-wip.lean.txt` — there law 2's instance is
BLOCKED (the coherence conjunct is false for that fixture); HERE both
laws instantiate, because the atoms' scanners are VALUE-CONSTANT
(the scan yields a fixed `Bool`), so `pre` can be value-selective and
`altCoherent`'s branch-agreement conjunct is TRUE.

Honest notes:
1. The lexeme/codec rows live HERE (the slice's literals are
   single-char, so the `lit` row lands at its single-char core; the
   shared `Lexemes.lean` rows land with the first migration wave).
2. The certificate rides the PROVED `wfCheck_sound` route (`decide`
   discharges `wfCheck`); the law premises (`valueOk`/`tailOk`/the
   fuel bound) are `decide`-discharged per instance.
3. The rep's junction rows (WF-REP-2) are vacuous at this fixture
   (the token arms' munches are `none`, so the tail-munch fold is
   `some []`) — documented, not silent.
4. The axiom pins are `#print axioms` at build time (this file is
   NON-module — `TextKit.Grammar*` are non-module files, and a
   `module` file cannot import them; the module barrier, probed —
   so the pins cannot live in `TextKitTests.Axioms`).
5. Negative controls (15-patterns #5): sabotaged sibling grammars,
   each failing `wfCheck` with the NAMED row, pinned by `decide` (a
   control that stops failing fails the build) + the law-premise
   teeth (a coherence-false grammar is exactness-false).

-/

import TextKit.Grammar
import TextKit.Grammar.Lexemes
import TextKit.Grammar.Check
import TextKit.Grammar.Laws

namespace TextKit.GrammarSlice

/-! ## the fixture format: `Toks := tok*`, `tok := 'x' → false | 'y' → true` -/

/-- The value-constant scanner for a single-char token: on the char
    `c` it yields the FIXED value `v` — the shared
    `TextKit.constCharScan` (Lexemes' constructor; the
    value-constant discipline is the scan's, not the slice's). -/
def boolScan (c : Char) (v : Bool) : GParser Bool := TextKit.constCharScan c v

/-- The single-char token lexeme: the shared const-char lexeme at the
    slice's payload (prints the char, scans exactly it yielding the
    FIXED value `v`; the write-side gate is value-selective —
    `pre r ↔ r = v` — the constructor's `pre`). -/
def boolLex (c : Char) (v : Bool) : Lexeme Bool := TextKit.constCharLex c v

/-- The token lexemes: `'x'` owns `false`, `'y'` owns `true`. -/
def lexX : Lexeme Bool := boolLex 'x' false
def lexY : Lexeme Bool := boolLex 'y' true

open Grammar in
/-- The token grammar: the two-arm ordered choice. -/
def tokGrammar : Grammar Bool :=
  .alt (.atom lexX) (.atom lexY)

/-- The identity codec over the payload (the flat format's rel row:
    the raw IS the value list). -/
def listCodec : Kit.Codec (List Bool) (List Bool) := Kit.Codec.refl (List Bool)

open Grammar in
/-- THE fixture: a flat `rep`-top grammar under a `rel` — the
    code-registry's row shape, no `fix`/`self` anywhere. -/
def flatGrammar : Grammar (List Bool) :=
  .rel listCodec (fun _ => true) (fun _ _ _ => rfl)
    (fun _raw _r h => (Option.some.inj h).symm) "toks" [] (.rep tokGrammar)

/-! ## the certificate + the law premises' discharge -/

/-- THE certificate discharge (06 §7's build-time check): the
    fixture's WF rows hand-check green (WF-REP-1: the token alt is
    non-nullable; WF-REP-2: vacuous — the munches are `none`, note 3;
    WF-ALT-1: `lit "x"` vs `lit "y"` prefix-free). -/
theorem flatCert : Grammar.Predictive flatGrammar :=
  Grammar.wfCheck_sound flatGrammar (by decide)

/-- The fix-free fold discharges at the fixture (the rel → rep → alt
    walk). -/
theorem flatFixFree : Grammar.FixFree flatGrammar := ⟨trivial, trivial⟩

/-- Law 2's coherence premise: the two token arms' value classes are
    disjoint (`lexX` owns `false`, `lexY` owns `true` — the header's
    note: this is what the value-constant scanners buy). -/
theorem flatCoherent : Grammar.altCoherent flatGrammar := by
  have h1 : ∀ x : Bool, Grammar.valueOk (.atom lexX) x = true →
      Grammar.valueOk (.atom lexY) x = false := by
    intro x hx
    have h2 : lexX.pre x = true := hx
    simp only [lexX, boolLex, constCharLex] at h2
    have hx' : x = false := of_decide_eq_true h2
    show lexY.pre x = false
    simp [lexY, boolLex, constCharLex, hx']
  exact ⟨h1, trivial, trivial⟩

/-! ## the law instantiations -/

/-- Law 1 (the append form) at the fixture: parsing the print of a
    value-owned token list returns the value and leaves the suffix. -/
theorem flatParsePrint (fuel : Nat) (xs : List Bool) (sfx : List Char) (k : Nat)
    (hval : Grammar.valueOk flatGrammar xs = true)
    (htail : Grammar.tailOk flatGrammar xs sfx = true)
    (hfuel : ((Grammar.printG flatGrammar xs).toList ++ sfx).length
      + Grammar.guardSlack flatGrammar ≤ fuel) :
    Grammar.parseG flatGrammar fuel
      ⟨k, (Grammar.printG flatGrammar xs).toList ++ sfx⟩
      = .ok (xs, ⟨k + (Grammar.printG flatGrammar xs).length, sfx⟩) :=
  Grammar.parse_print_fixFree flatGrammar flatFixFree flatCert fuel xs sfx
    ⟨k, (Grammar.printG flatGrammar xs).toList ++ sfx⟩
    hval htail rfl hfuel

/-- The run corollary at the fixture. -/
theorem flatRunPrint (xs : List Bool) (hval : Grammar.valueOk flatGrammar xs = true) :
    Grammar.run flatGrammar (Grammar.print flatGrammar xs) = .ok xs :=
  Grammar.run_print_fixFree flatGrammar flatFixFree flatCert xs hval

/-- Law 2 (the exactness law) at the fixture: a successful parse
    consumed EXACTLY the print of its result. -/
theorem flatPrintParse (fuel : Nat) (ys : List Bool) (cur cur' : Cursor)
    (h : Grammar.parseG flatGrammar fuel cur = .ok (ys, cur')) :
    cur.cs = (Grammar.printG flatGrammar ys).toList ++ cur'.cs ∧
    cur'.off = cur.off + (Grammar.printG flatGrammar ys).length ∧
    Grammar.valueOk flatGrammar ys = true :=
  Grammar.print_parse flatGrammar fuel flatCoherent h

/-! ## the concrete pins -/

/-- The print of `[false, true]` is `"xy"`. -/
theorem flatPrint_xy : Grammar.print flatGrammar [false, true] = "xy" := rfl

/-- The printG twin (the parse face's rewrite form). -/
theorem flatPrintG_xy : Grammar.printG flatGrammar [false, true] = "xy" := rfl

/-- The run round trip at the concrete text. -/
theorem flatRun_xy : Grammar.run flatGrammar "xy" = .ok [false, true] := by
  have h := flatRunPrint [false, true] (by decide)
  rw [flatPrint_xy] at h
  exact h

/-- The parse round trip at the concrete text (law 1's parse face). -/
theorem flatParse_xy : Grammar.parseG flatGrammar 4 ⟨0, "xy".toList⟩
    = .ok ([false, true], ⟨2, ([] : List Char)⟩) := by
  have h := flatParsePrint 4 [false, true] [] 0 (by decide) (by decide) (by decide)
  rw [flatPrintG_xy] at h
  exact h

/-! ## the axiom pins (the axiom gate's replay face; the header's note 4) -/

#print axioms flatCert
#print axioms flatCoherent
#print axioms flatParsePrint
#print axioms flatRunPrint
#print axioms flatPrintParse

/-! ## the negative controls (the certificate's teeth) -/

/-- The identity-rel helper for the sabotaged siblings. -/
def idRel {Raw : Type} (sub : Grammar Raw) : Grammar Raw :=
  .rel (Kit.Codec.refl Raw) (fun _ => true) (fun _ _ _ => rfl)
    (fun _raw _r h => (Option.some.inj h).symm) "sab" [] sub

/-- SABOTAGE 1 (WF-REP-1): a nullable rep body. -/
def sabRepBody : Grammar (List (Option Bool)) :=
  idRel (Raw := List (Option Bool))
    (Grammar.rep (Grammar.opt (Grammar.atom lexX)))

/-- The named-row pin (WF-REP-1 progress + WF-REP-2: the opt's stop
    head collides with its own first). -/
theorem sabRepBody_row :
    Grammar.wfProblems [] sabRepBody
      = ["WF-REP-1 at []", "WF-REP-2 at []"] := by decide

/-- SABOTAGE 2 (WF-ALT-1): colliding alt heads — two `'x'` branches. -/
def sabAltHeads : Grammar Bool :=
  .alt (.atom lexX) (.atom (boolLex 'x' true))

theorem sabAltHeads_row :
    Grammar.wfProblems [] sabAltHeads = ["WF-ALT-1 at []"] := by decide

/-- The option codec (the rel-dam: a `rel` node's payload escapes the
    sub-grammar's raw type — the ONLY way to build a nullable
    `Grammar Bool` arm, since `opt`/`rep` change the payload). -/
def optCodec : Kit.Codec (Option Bool) Bool where
  encode := Option.some
  decode := fun raw => raw
  policy := fun _ => True
  decode_encode := by intro b; rfl
  decode_some_policy := by intro a b _h; trivial

/-- SABOTAGE 3 (WF-ALT-2): a nullable LEFT branch (through the rel dam). -/
def sabAltNullable : Grammar Bool :=
  .alt
    (.rel optCodec (fun _ => true) (fun _ _ _ => rfl) (fun raw _r h => h.symm)
      "sab" [] (Grammar.opt (.atom lexX)))
    (.atom lexY)

theorem sabAltNullable_row :
    Grammar.wfProblems [] sabAltNullable = ["WF-ALT-2 at []"] := by decide

/-- SABOTAGE 4 (WF-SEQ-1): the LEFT rep's stop head collides with the
    continuation's first (the atom's tail-firsts are empty — the rep
    must be the left arm for the row to fire). -/
def sabSeqHeads : Grammar (List Bool × Bool) :=
  .seq (.rep (.atom lexX)) (.atom lexX)

theorem sabSeqHeads_row :
    Grammar.wfProblems [] sabSeqHeads = ["WF-SEQ-1 at []"] := by decide

/-- SABOTAGE 5 (WF-OPT): a nullable opt body. -/
def sabOptBody : Grammar (Option (Option Bool)) :=
  .opt (Grammar.opt (.atom lexX))

theorem sabOptBody_row :
    Grammar.wfProblems [] sabOptBody = ["WF-OPT at []"] := by decide

/-- SABOTAGE 6 (law 2's coherence tooth): two first-DISJOINT arms
    whose value classes OVERLAP — passes `wfCheck` (the checker knows
    no coherence row), fails `altCoherent`. -/
def sabValueOverlap : Grammar Bool :=
  .alt (.atom lexX) (.atom (boolLex 'y' false))

theorem sabValueOverlap_wf : Grammar.wfCheck sabValueOverlap = true := by decide

theorem sabValueOverlap_notCoherent :
    ¬ Grammar.altCoherent sabValueOverlap := by
  intro h
  obtain ⟨hconj, -, -⟩ := h
  have h1 := hconj false (by rfl)
  simp [boolLex, constCharLex] at h1

end TextKit.GrammarSlice

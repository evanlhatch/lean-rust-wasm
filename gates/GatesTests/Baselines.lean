/-
# GatesTests.Baselines — the grammar-layer baselines' teeth (B3)

The four report baselines ride `Gates.Baselines`'s grammar values (the
CodeRegistry template's flat shape). The teeth:

1. THE LIVE BYTE-TIE (the main-level IO face): each committed baseline
   parses through its grammar and prints back to ITS OWN BYTES — the
   migration's proof at the spec of record (a hand-edited file fails
   the round trip).
2. THE PURE TEETH (the spec below): the drift refusals at the SMALL
   faces (the nat-atom's canonical-scan refusal of a leading zero; the
   climbs' prefix/canonicality refusals), + the row-byte pin.

The mandatory negative controls (15-patterns #5): the sabotaged
siblings the sweep MUST catch.
-/

-- STAYS PRE-MODULE (the C2/C3 module wave's note): the two `decide`
-- teeth below reduce `Gates.Baselines.elabRowLineG`'s `print` output
-- cross-module; in a module file that reduction sticks at the grammar
-- layer's match-auxiliary decls (`printList`'s aux / equations — the
-- probe §4 wall). Pre→module import is legal, so the file consumes the
-- now-module `Gates.Baselines` unchanged.
import TextKit.Grammar
import TextKit.Grammar.Lexemes
import Gates.Baselines
import TestingKit.Harness
import TestingKit.Spec

open TestingKit

namespace GatesTests.Baselines

/-! ## the pure teeth -/

/-- The elab row's sample (the committed file's first row's shape). -/
def sampleElabRows : List Gates.Baselines.ElabRow :=
  [⟨"Kit", 630, 186⟩, ⟨"ZSet", 210, 186⟩]

/-- The elab sample's valueOk premise (the module discipline at the
    concrete rows — decided). -/
theorem sampleElabOk : TextKit.Grammar.valueOk Gates.Baselines.elabGrammar sampleElabRows = true := by
  apply Gates.Baselines.valueOk_elab
  intro e he
  cases he with
  | head => decide
  | tail _ h2 =>
      cases h2 with
      | head => decide
      | tail _ habs => exact absurd habs List.not_mem_nil

/-- Law 1's instance: the sample prints to its canonical bytes and
    parses back EXACTLY (the generic theorem's instance — the
    compile-time pin). -/
theorem sampleElabRound :
    TextKit.Grammar.run Gates.Baselines.elabGrammar
        (TextKit.Grammar.print Gates.Baselines.elabGrammar sampleElabRows)
      = Except.ok sampleElabRows :=
  Gates.Baselines.elabRunPrint sampleElabRows sampleElabOk

/-- The row's byte pin: the row grammar's print spells the TSV row. -/
def sampleRowPrint : Bool :=
  (TextKit.Grammar.print Gates.Baselines.elabRowLineG
      ("Kit", ((), (630, ((), 186))))) == "Kit\t630\t186"

theorem sampleRowPrint_true : sampleRowPrint = true := by decide

/-- The nat-atom's canonicality tooth: a LEADING ZERO is a scan
    refusal (the hand-edited millisecond's face). -/
def natTeeth : Bool :=
  (match TextKit.natScan ⟨0, "630".toList⟩ with
    | .ok _ => true | .error _ => false)
  && (match TextKit.natScan ⟨0, ("0" ++ "630").toList⟩ with
    | .error _ => true | .ok _ => false)

theorem natTeeth_true : natTeeth = true := by decide

/-- The axiom report's climb teeth: the CANONICAL block's raw climbs to
    its data; a corrupted keyword prefix (`axioms uzed:`) is a REFUSAL
    (the climb's prefix-validation face). -/
def axiomTeeth : Bool :=
  (Gates.Baselines.axBlockClimb
      (⟨⟨(), ("Kit", ((), 1, ()))⟩, ()⟩,
        ((), (("axioms used: propext", ()),
          (("violations: none", ()), ((), ((), ()))))))
    == Option.some ⟨"Kit", 1, "propext", "none"⟩)
  && (Gates.Baselines.axBlockClimb
      (⟨⟨(), ("Kit", ((), 1, ()))⟩, ()⟩,
        ((), (("axioms uzed: propext", ()),
          (("violations: none", ()), ((), ((), ()))))))
    == Option.none)

theorem axiomTeeth_true : axiomTeeth = true := by decide

/-- The coverage's cell-canonicality tooth: a corrupted cell is a
    REFUSAL at the climb. -/
def covCellTeeth : Bool :=
  (Gates.Baselines.covCellClimb ((), ("y", ())) == Option.none)
  && (Gates.Baselines.covCellClimb ((), ("xx", ())) == Option.none)
  && (Gates.Baselines.covCellClimb (Gates.Baselines.covCellRawOf true)
      == Option.some true)
  && (Gates.Baselines.covCellClimb (Gates.Baselines.covCellRawOf false)
      == Option.some false)

theorem covCellTeeth_true : covCellTeeth = true := by decide

/-- The prefix-law teeth: the keyword prefixes' corrupted spellings
    fail the climb's prefix test. -/
def prefTeeth : Bool :=
  Gates.Baselines.prefOk Gates.Baselines.axPrefix "axioms used: propext"
  && (!Gates.Baselines.prefOk Gates.Baselines.axPrefix "axioms uzed: propext")
  && Gates.Baselines.prefOk Gates.Baselines.violPrefix "violations: none"
  && (!Gates.Baselines.prefOk Gates.Baselines.violPrefix "violacionz: none")

theorem prefTeeth_true : prefTeeth = true := by decide

/-- The pure spec: the format faces' pins + the drift teeth (+ the
    mandatory negative controls: the sabotaged siblings MUST fail). -/
def baselinesSpec : Spec :=
  Spec.ofList "the baselines ride the grammar layer (B3: the flat\n      line-raw + total-climb shape; the bytes pinned; the drift teeth)"
    (fun _ =>
      assert ((
        sampleRowPrint
          && natTeeth
          && axiomTeeth
          && covCellTeeth
          && prefTeeth
        ) && Gates.Baselines.censusRowOk ("linter.guestlang.x", ("f.lean", 4)))
      "the grammar-layer baseline faces drifted")
    [ ("the nat-atom ACCEPTS the leading zero (must fail)",
        fun _ =>
          assert ((match TextKit.natScan ⟨0, ("0" ++ "630").toList⟩ with
            | .error _ => false | .ok _ => true))
            "control fired: the leading-zero spelling must be refused — \
              the canonical-scan discipline is load-bearing")
    , ("the corrupted axiom keyword CLIMBS (must fail)",
        fun _ =>
          assert (Gates.Baselines.prefOk Gates.Baselines.axPrefix
              "axioms uzed: propext")
            "control fired: the corrupted prefix must fail the climb — \
              the prefix discipline is load-bearing")
    ]
    1 713705

/-! ## the live byte-tie (the main-level IO face) -/

/-- Read one committed baseline, parse it through its grammar, print
    back: the bytes must be the file's (modulo the final newline,
    `Driver.reportGate`'s contract). `pre` adapts the parse-input: the
    elab/axiom files carry a trailing contract newline beyond the
    grammar's last line (the elab) or parse direct (the axiom's blocks
    are all terminated); the census/coverage files are the grammar's
    bytes + the reportGate newline. -/
def liveTie {α : Type} (path : String) (pre : String → String)
    (parse? : String → Option α) (print : α → String) : IO (Option String) := do
  let text ← IO.FS.readFile path
  let fresh := text.dropEnd 1 |>.toString
  match parse? (pre text) with
  | none =>
      return some s!"{path}: the grammar REFUSED the committed baseline \
        (a hand edit? the head: {(fresh.take 48)}...)"
  | some v =>
      let back := print v
      if back == fresh then
        return none
      else
        return some s!"{path}: the grammar's print is NOT the committed \
          bytes (got {(back.take 48)}..., want {(fresh.take 48)}...)"

/-- THE LIVE BYTE-TIE at all four baselines (the migration's proof at
    the spec of record). -/
def liveTeeth : IO (Option String) := do
  let out1 ← liveTie "notes/elab-baseline.tsv" (·.dropEnd 1 |>.toString)
    Gates.Baselines.parseElab?
    (fun es => Gates.Baselines.printElab es.toArray)
  let out2 ← liveTie "notes/nolint-census.tsv" (·.dropEnd 1 |>.toString)
    Gates.Baselines.parseCensus?
    Gates.Baselines.printCensus
  let out3 ← liveTie "notes/axiom-report.md" id
    Gates.Baselines.parseAxiom?
    Gates.Baselines.printAxiom
  let out4 ← liveTie "notes/coverage-matrix.md" (·.dropEnd 1 |>.toString)
    Gates.Baselines.parseCov?
    Gates.Baselines.printCov
  match out1, out2, out3, out4 with
  | none, none, none, none => return none
  | _, _, _, _ =>
      return some (String.intercalate "; "
        ([out1, out2, out3, out4].filterMap id))

end GatesTests.Baselines

/-
# Gates.Baselines — the four report baselines as grammar values

Owner: the B3 migration (design-wave-30.md B3; 05 §1's typed grammar
layer). The four committed baselines — `notes/elab-baseline.tsv`,
`notes/nolint-census.tsv`, `notes/axiom-report.md`,
`notes/coverage-matrix.md` — are `TextKit.Grammar` values on the
CodeRegistry template's FLAT shape: the grammar value per LINE KIND,
the file = the lines' fold, ONE `rel` node at the top (the raw IS the
lines), no `alt` except where the format's faces force it (the
coverage matrix's quiet section: `(none)` vs the tag rows — disjoint
literal heads), and no `fix` anywhere.

THE COMPOSED-GRAMMAR WALL (the B3 agent's park, dissolved by the
probe-validated diagnosis): the certificate's shape — not a kernel
reduction-depth ceiling — is the variable. The flat shape's `wfCheck`
`decide` REDUCES (same node-count class as the registry); the
alt-composed face fails only through REAL WF rows (first-set
collisions between line kinds) or through `rfl`-attempted rel
`exact`/`decode_encode` premises that close once the elementwise map
laws are NAMED. `altCoherent` at any `alt` carries a REAL
value-class-disjointness obligation — the flat fragment (no `alt`)
makes it vacuous. See `notes/v3/15-patterns.md` (the wall's entry).

The laws (the grammar-layer instances, CodeRegistry's route): the
Predictive certificate rides the PROVED `wfCheck_sound` (`decide`
discharges `wfCheck`); law 1 (`run_print_fixFree` — the parse of the
print is the value) instantiates at each format; the write-side gates
(`valueOk`) reduce to the atoms' own pres.

The byte-tie: each gate's fresh render IS `print` (the hand
byte-assembly dies); the bytes are UNCHANGED — the four gates pass
without a re-baseline, which is the migration's proof. The load-failed
block face (`Gates.Axioms`'s `LOAD FAILED` render) never enters the
grammar layer: a load failure exits 1 before any baseline is trusted.

Core-only (imports `TextKit.Grammar*` + `LintKit.Basic` — the cone
rule: gates are C0 host tooling, TextKit and LintKit are C0; the
import is the `@[nolint]` attr's syntax — the graduation opt-outs
below are the honest-gap faces).
-/

module

public import TextKit.Grammar
public import TextKit.Grammar.Lexemes
public import TextKit.Grammar.Check
public import TextKit.Grammar.Laws
public import LintKit.Basic

@[expose] public section

namespace Gates.Baselines

open TextKit

/-! ## the shared lexemes (the file discipline: every line
    LF-terminated; the TAB is the TSVs' field separator) -/

/-- The line terminator (the committed files' every line ends with
    it — the write face's `fresh ++ "\n"` contract). -/
def nlAtom : Lexeme Unit := constCharLex '\n' ()

/-- The TSV field separator. -/
def tabAtom : Lexeme Unit := constCharLex '\t' ()

/-- A free-text line tail's charset: everything but LF (the line
    boundary; `ConfigFormat`'s `valChar`). -/
def txtChar (c : Char) : Bool := c != '\n'

/-- The free-text line atom: the ident shape at `txtChar` (the shared
    generator — the maximal non-LF run; its munch breaks at the LF). -/
def txtAtom : Lexeme String :=
  identAtom "<line>" txtChar txtChar (fun _ hc => hc)

/-- The appended terminator makes the literal nonempty — no per-line
    decide (and never one over a long append chain: the probe's
    maxRecursion datum). -/
theorem lineNeNil (s : String) : (s ++ "\n").toList ≠ [] := by
  intro hcon
  have h1 : (s ++ "\n").toList.length = s.toList.length + 1 := by
    rw [String.toList_append]; simp
  rw [hcon, List.length_nil] at h1
  exact absurd h1 (by simp)

/-- One fixed line (text + LF): the const-string atom at the appended
    terminator. The spell IS the line's bytes. -/
def fixedLine (s : String) : Lexeme Unit :=
  constStrLex (s ++ "\n") (lineNeNil s)

/-! ### the elab baseline (the TSV's data face) -/

/-- One gated root's committed row: the module, its milliseconds, the
    reference root's (`Gates.ElabWatch`'s ratio discipline). -/
structure ElabRow where
  mod : String
  millis : Nat
  refMillis : Nat
deriving Repr, Inhabited

/-- The TSV field charset (anything but the separators) — ONE copy
    shared by the elab row's module face and the nolint census's field
    face (the dupDefBodies tooth refuses twins, so the two formats'
    identical separator class spells once). -/
def tsvChar (c : Char) : Bool := c != '\t' && c != '\n' && c != '\r'

/-- The row head class: a `tsvChar` that is not `#` (the data
    rows' firsts vs the `#`-led header literal — the WF-SEQ-1 row). -/
def elabModHead (c : Char) : Bool := tsvChar c && !(c == '#')

theorem elabModHead_chain : ∀ c, elabModHead c = true → tsvChar c = true :=
  fun _ hc => (Bool.and_eq_true_iff.mp hc).1

/-- The module lexeme (the shared ident-atom at the row's classes). -/
def elabModAtom : Lexeme String :=
  identAtom "<mod>" elabModHead tsvChar elabModHead_chain

/-- The write-side gate at one row: the module's ident discipline —
    nonempty, separator-free, `#`-free head. This IS `elabModAtom`'s
    `pre` (the round-trip law's premise face). -/
def elabRowOk (e : ElabRow) : Bool :=
  identOk elabModHead tsvChar e.mod

/-! ### the elab format's grammar (the flat shape: five fixed header
    lines, then the rows' fold) -/

/-- The five fixed header lines' exact bytes (`Gates.ElabWatch`'s
    render's header — moved here, ONE writer per format). -/
def elabH1 : String := "# The elaboration-time baseline (notes/v3/09-gates-ops.md §7)."
def elabH2 : String := "# GENERATED by `lake exe gates elab-watch --write` — do not hand-edit."
def elabH3 : String := "# mod<TAB>millis<TAB>refMillis — the committed signal is the RATIO; a module"
def elabH4 : String := "# over 2× its committed ratio (and over the GATES_ELAB_FLOOR_MS"
def elabH5 : String := "# jitter floor) fails `gates elab-watch`."

/-- The header lines' raw face (five unit payloads, right-nested). -/
abbrev ElabHdrRaw := Unit × (Unit × (Unit × (Unit × Unit)))

open Grammar in
/-- The five fixed header lines. -/
def elabHdrG : Grammar ElabHdrRaw :=
  .seq (.atom (fixedLine elabH1))
    (.seq (.atom (fixedLine elabH2))
      (.seq (.atom (fixedLine elabH3))
        (.seq (.atom (fixedLine elabH4))
          (.atom (fixedLine elabH5)))))

/-- One data row's raw face: `mod<TAB>millis<TAB>refMillis` (the
    units are the separators' payloads). -/
abbrev ElabRowRaw := String × (Unit × (Nat × (Unit × Nat)))

open Grammar in
/-- One data row's body. -/
def elabRowLineG : Grammar ElabRowRaw :=
  .seq (.atom elabModAtom) (.seq (.atom tabAtom)
    (.seq (.atom natAtom) (.seq (.atom tabAtom) (.atom natAtom))))

open Grammar in
/-- One data line: the row + the LF terminator. -/
def elabLineG : Grammar (ElabRowRaw × Unit) :=
  .seq elabRowLineG (.atom nlAtom)

/-- The row's raw spell (the codec's encode face, elementwise). -/
def elabRawOf : ElabRow → (ElabRowRaw × Unit) :=
  fun e => ((e.mod, ((), (e.millis, ((), e.refMillis)))), ())

/-- The row's climb (the codec's decode face, elementwise). -/
def elabOfRaw : (ElabRowRaw × Unit) → ElabRow :=
  fun p => ⟨p.1.1, p.1.2.2.1, p.1.2.2.2.2⟩

theorem elabOfRaw_elabRawOf (e : ElabRow) : elabOfRaw (elabRawOf e) = e := by
  cases e; rfl

theorem elabRawOf_elabOfRaw (p : ElabRowRaw × Unit) :
    elabRawOf (elabOfRaw p) = p := by
  obtain ⟨⟨m, _, ms, _, rf⟩, _⟩ := p
  rfl

theorem map_elabRound : ∀ es : List ElabRow,
    (es.map elabRawOf).map elabOfRaw = es
  | [] => rfl
  | e :: rest => by
      rw [List.map_cons, List.map_cons, elabOfRaw_elabRawOf, map_elabRound]

/-- The file's raw face: the header's five units + the lines (the
    sub grammar's payload). -/
abbrev ElabRaw := ElabHdrRaw × List (ElabRowRaw × Unit)

/-- THE elab baseline codec: the file = the header + the rows' fold;
    the climb is total (the row level is total: `elabOfRaw` never
    refuses — the canonical format carries every raw line). -/
def elabCodec : Kit.Codec ElabRaw (List ElabRow) where
  encode := fun es => (((), ((), ((), ((), ())))), es.map elabRawOf)
  decode := fun raw => some (raw.2.map elabOfRaw)
  policy := fun _ => True
  decode_encode := fun es => by
    show Option.some ((es.map elabRawOf).map elabOfRaw) = some es
    rw [map_elabRound]
  decode_some_policy := fun _ _ _ => trivial

/-- The climb's exactness (the rel node's `exact` field): a decoded
    row list re-encodes to its raw — the elementwise law rides the
    fold (the registry's `encode_of_rowsDecode` shape). -/
theorem elabExact : ∀ (raw : ElabRaw) (r : List ElabRow),
    elabCodec.decode raw = some r → elabCodec.encode r = raw := by
  intro raw r h
  show ((((), ((), ((), ((), ())))), r.map elabRawOf)) = raw
  have h2 : raw.2.map elabOfRaw = r := Option.some.inj h
  rw [← h2, List.map_map]
  have hpoint : (elabRawOf ∘ elabOfRaw) = id := by
    funext p; exact elabRawOf_elabOfRaw p
  rw [hpoint, List.map_id]

/-- THE GRADUATION (15-patterns #11 at the codec grade,
    `Kit.Codec.toIsoOfExact` — the registry's `registryIso` precedent):
    the climb is TOTAL (`elabCodec`'s decode never refuses — the
    canonical format carries every raw line) + `elabExact` assemble the
    TRUE `Iso` — the raw file ≅ the row list, both round trips. -/
def elabIso : Kit.Iso ElabRaw (List ElabRow) :=
  elabCodec.toIsoOfExact (fun raw => ⟨raw.2.map elabOfRaw, rfl⟩) elabExact

open Grammar in
/-- THE elab baseline's grammar: ONE rel at the top (the raw IS the
    lines) over the flat node spine — five header consts, then the
    rows' fold. No `alt`, no `fix` anywhere. -/
def elabGrammar : Grammar (List ElabRow) :=
  .rel elabCodec (fun _ => true) (fun _ _ _ => rfl) elabExact "elab" []
    (.seq elabHdrG (.rep elabLineG))

/-! ### the elab certificate + the round-trip law -/

/-- THE certificate discharge (the flat shape's decide REDUCES — the
    diagnosis's positive face; the WF rows hand-check green). -/
theorem elabCert : Grammar.Predictive elabGrammar :=
  Grammar.wfCheck_sound elabGrammar (by decide)

/-- The fix-free fold (no `fix` node anywhere). -/
theorem elabFixFree : Grammar.FixFree elabGrammar := by
  repeat constructor

/-- Law 2's coherence premise: no `alt` node — the fold is vacuous. -/
theorem elabCoherent : Grammar.altCoherent elabGrammar := by
  trivial

/-- The value discipline IS the module discipline: `valueOk` holds
    exactly when every row's module is `elabRowOk` (the ident-atom's
    write-side gate; every other field's pre is trivially true). -/
theorem valueOk_elab (es : List ElabRow)
    (h : ∀ e ∈ es, elabRowOk e = true) :
    Grammar.valueOk elabGrammar es = true := by
  have hrow : ∀ e : ElabRow, elabRowOk e = true →
      Grammar.valueOk elabLineG (elabRawOf e) = true := by
    intro e hrow
    cases e with
    | mk m ms rf =>
        have h2 : identOk elabModHead tsvChar m = true := hrow
        simp [Grammar.valueOk, elabLineG, elabRowLineG, elabRawOf,
          elabModAtom, nlAtom, tabAtom, constCharLex, natAtom,
          TextKit.identAtom, h2]
  show (es.map elabRawOf).all
    (fun z => Grammar.valueOk elabLineG z) = true
  rw [List.all_eq_true]
  intro z hz
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
  exact hrow e (h e he)

/-- THE FILE-FORMAT LAW (the grammar layer's instance): a gate-passing
    row list prints to its canonical bytes and parses back EXACTLY. -/
theorem elabRunPrint (es : List ElabRow)
    (hval : Grammar.valueOk elabGrammar es = true) :
    Grammar.run elabGrammar (Grammar.print elabGrammar es) = .ok es :=
  Grammar.run_print_fixFree elabGrammar elabFixFree elabCert es hval

/-- The committed baseline's bytes (the gate's fresh render — the hand
    byte-assembly's successor; the write face appends the file's final
    newline, `Driver.reportGate`'s contract). -/
def printElab (es : Array ElabRow) : String := Grammar.print elabGrammar es.toList

/-- One data line's drift tooth: the line (plus its terminator) must
    be the canonical row spelling — a hand-edited field count, a
    leading-zero millisecond, or a corrupted module is a REFUSAL. -/
def elabLineOk (line : String) : Bool :=
  match Grammar.run elabLineG (line ++ "\n") with
  | .ok _ => true | .error _ => false

/-- The parse faces' newline discipline (the registry's wrapper's
    shape): the file's FINAL newline is `Driver.reportGate`'s — a fresh
    render's last line may be un-terminated; the wrapper appends the LF
    the last line's terminator needs (the empty text stays empty). -/
def canonNl (text : String) : String :=
  if text == "" || text.toList.getLast? == some '\n' then text else text ++ "\n"

def parseElab? (text : String) : Option (List ElabRow) :=
  match Grammar.run elabGrammar (canonNl text) with
  | .ok es => some es | .error _ => none

/-! ## the nolint census (`notes/nolint-census.tsv`) -/

/-- The census's value: one `(linter, file, count)` triple per row
    (the linter's SPELLING — the gate maps its `Name` face here). -/
abbrev CensusRows := List (String × String × Nat)

/-- The census's field lexeme (the shared ident-atom at `tsvChar` —
    the elab face's charset, ONE copy; the fields' spellings are
    separator-free: linter dotted names, file paths). -/
def censusAtom : Lexeme String :=
  identAtom "<field>" tsvChar tsvChar (fun _ hc => hc)

/-- The six fixed header lines (the census's render header + the blank
    separator — ONE writer). -/
def censusH1 : String := "# nolint census — the opt-out rows' per-(linter, file) counts"
def censusH2 : String := "GENERATED by `lake exe gates nolint-census --write` — do not hand-edit."
def censusH3 : String := "CI runs `nolint-census` without --write; a diff fails the gate."
def censusH4 : String := "Every row is load-bearing (the named reason stays) or fixed — a new"
def censusH5 : String := "row lands as a deliberate --write --accept-drift re-baseline diff."

/-- The header's raw face: five text lines + the blank separator. -/
abbrev CensusHdrRaw := Unit × (Unit × (Unit × (Unit × (Unit × Unit))))

open Grammar in
/-- The census's fixed header (five consts + the blank line). -/
def censusHdrG : Grammar CensusHdrRaw :=
  .seq (.atom (fixedLine censusH1))
    (.seq (.atom (fixedLine censusH2))
      (.seq (.atom (fixedLine censusH3))
        (.seq (.atom (fixedLine censusH4))
          (.seq (.atom (fixedLine censusH5))
            (.atom nlAtom)))))

/-- One census row's raw face: `linter<TAB>file<TAB>count`. -/
abbrev CensusRowRaw := String × (Unit × (String × (Unit × Nat)))

open Grammar in
/-- One census line: the row + the LF terminator. -/
def censusLineG : Grammar (CensusRowRaw × Unit) :=
  .seq (.seq (.atom censusAtom) (.seq (.atom tabAtom)
      (.seq (.atom censusAtom) (.seq (.atom tabAtom) (.atom natAtom)))))
    (.atom nlAtom)

/-- The row's raw spell (elementwise). -/
def censusRawOf : (String × String × Nat) → (CensusRowRaw × Unit) :=
  fun p => ((p.1, ((), (p.2.1, ((), p.2.2)))), ())

/-- The row's climb (elementwise). -/
def censusOfRaw : (CensusRowRaw × Unit) → (String × String × Nat) :=
  fun p => (p.1.1, p.1.2.2.1, p.1.2.2.2.2)

theorem censusOfRaw_censusRawOf (p : String × String × Nat) :
    censusOfRaw (censusRawOf p) = p := by cases p; rfl

theorem censusRawOf_censusOfRaw (q : CensusRowRaw × Unit) :
    censusRawOf (censusOfRaw q) = q := by
  obtain ⟨⟨l, _, f, _, k⟩, _⟩ := q
  rfl

theorem map_censusRound : ∀ ps : CensusRows,
    (ps.map censusRawOf).map censusOfRaw = ps
  | [] => rfl
  | p :: rest => by
      rw [List.map_cons, List.map_cons, censusOfRaw_censusRawOf, map_censusRound]

/-- The census file's raw face: the header + the rows. -/
abbrev CensusRaw := CensusHdrRaw × List (CensusRowRaw × Unit)

/-- THE census codec (the file = the header + the rows' fold; the
    climb is total). -/
def censusCodec : Kit.Codec CensusRaw CensusRows where
  encode := fun ps => (((), ((), ((), ((), ((), ()))))), ps.map censusRawOf)
  decode := fun raw => some (raw.2.map censusOfRaw)
  policy := fun _ => True
  decode_encode := fun ps => by
    show Option.some ((ps.map censusRawOf).map censusOfRaw) = some ps
    rw [map_censusRound]
  decode_some_policy := fun _ _ _ => trivial

/-- The climb's exactness (the rel node's `exact` field). -/
theorem censusExact : ∀ (raw : CensusRaw) (ps : CensusRows),
    censusCodec.decode raw = some ps → censusCodec.encode ps = raw := by
  intro raw ps h
  show ((((), ((), ((), ((), ((), ()))))), ps.map censusRawOf)) = raw
  have h2 : raw.2.map censusOfRaw = ps := Option.some.inj h
  rw [← h2, List.map_map]
  have hpoint : (censusRawOf ∘ censusOfRaw) = id := by
    funext q; exact censusRawOf_censusOfRaw q
  rw [hpoint, List.map_id]

/-- THE GRADUATION (15-patterns #11 at the codec grade,
    `elabIso`'s precedent one section up): the climb is TOTAL
    (`censusCodec`'s decode never refuses) + `censusExact` assemble the
    TRUE `Iso` — the raw file ≅ the census rows, both round trips. -/
def censusIso : Kit.Iso CensusRaw CensusRows :=
  censusCodec.toIsoOfExact (fun raw => ⟨raw.2.map censusOfRaw, rfl⟩) censusExact

open Grammar in
/-- THE census's grammar (the flat shape — one rel at the top, the
    file = the lines' fold). -/
def censusGrammar : Grammar CensusRows :=
  .rel censusCodec (fun _ => true) (fun _ _ _ => rfl) censusExact "census" []
    (.seq censusHdrG (.rep censusLineG))

/-- THE certificate (the flat shape's decide reduces). -/
theorem censusCert : Grammar.Predictive censusGrammar :=
  Grammar.wfCheck_sound censusGrammar (by decide)

/-- The fix-free fold. -/
theorem censusFixFree : Grammar.FixFree censusGrammar := by
  repeat constructor

/-- Law 2's coherence premise (no `alt` — vacuous). -/
theorem censusCoherent : Grammar.altCoherent censusGrammar := by
  trivial

/-- The census's write-side gate: every field's ident discipline (the
    atoms' own pres — the census's rows have no other owned content). -/
def censusRowOk (p : String × String × Nat) : Bool :=
  identOk tsvChar tsvChar p.1 && identOk tsvChar tsvChar p.2.1

/-- The value discipline's lemma (the round-trip law's premise face). -/
theorem valueOk_census (ps : CensusRows)
    (h : ∀ p ∈ ps, censusRowOk p = true) :
    Grammar.valueOk censusGrammar ps = true := by
  have hrow : ∀ p : String × String × Nat, censusRowOk p = true →
      Grammar.valueOk censusLineG (censusRawOf p) = true := by
    intro p hrow
    obtain ⟨l, f, k⟩ := p
    have h1 : identOk tsvChar tsvChar l = true :=
      (Bool.and_eq_true_iff.mp hrow).1
    have h2 : identOk tsvChar tsvChar f = true :=
      (Bool.and_eq_true_iff.mp hrow).2
    simp [Grammar.valueOk, censusLineG, censusRawOf, censusAtom, nlAtom,
      tabAtom, constCharLex, natAtom, TextKit.identAtom, h1, h2]
  show (ps.map censusRawOf).all
    (fun z => Grammar.valueOk censusLineG z) = true
  rw [List.all_eq_true]
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  exact hrow p (h p hp)

/-- THE FILE-FORMAT LAW (the census's instance). -/
theorem censusRunPrint (ps : CensusRows)
    (hval : Grammar.valueOk censusGrammar ps = true) :
    Grammar.run censusGrammar (Grammar.print censusGrammar ps) = .ok ps :=
  Grammar.run_print_fixFree censusGrammar censusFixFree censusCert ps hval

/-- The committed baseline's bytes. The grammar's print terminates the
    last line; the WRITE face's final newline is `Driver.reportGate`'s
    (`fresh ++ "\n"`) — the wrapper drops the print's terminator, so
    the on-disk bytes are the print (the old render's contract). -/
def printCensus (ps : CensusRows) : String :=
  (Grammar.print censusGrammar ps).dropEnd 1 |>.toString

/-- One census line's drift tooth (a hand-edited field count, a
    leading-zero count, or a corrupted field is a REFUSAL). -/
def censusLineOk (line : String) : Bool :=
  match Grammar.run censusLineG (line ++ "\n") with
  | .ok _ => true | .error _ => false

/-- The committed file's parse face. -/
def parseCensus? (text : String) : Option CensusRows :=
  match Grammar.run censusGrammar (canonNl text) with
  | .ok ps => some ps | .error _ => none

/-! ### the keyword-prefixed line climb (the axiom report's faces)

The keyword-prefixed lines (`axioms used: …`, `violations: …`) are
LINE-RAW: a const prefix + a permissive run FAILS WF-SEQ-1 (the
prefix's head char is in the run's class — the collision the flat
shape avoids by putting the WHOLE line in one free-text atom and
giving the prefix discipline to the CLIMB). -/

/-- The prefix test at the list level (the pattern-based
    `String.startsWith` is proof-hostile; the list-level `isPrefixOf`
    has the split law). -/
def prefOk (pre line : String) : Bool :=
  pre.toList.isPrefixOf line.toList

/-- The prefixed line's tail (the climb's value face). -/
def prefTail (pre line : String) : String :=
  String.ofList (line.toList.drop pre.toList.length)

/-- The climb inverts the spell: the built line's tail is the value's. -/
theorem prefTail_pref (pre t : String) : prefTail pre (pre ++ t) = t := by
  show String.ofList ((pre ++ t).toList.drop pre.toList.length) = t
  rw [String.toList_append, List.drop_append_length, String.ofList_toList]

/-- The prefix law: a prefix-passing line splits exactly. -/
theorem prefSplit (pre line : String) (h : prefOk pre line = true) :
    pre ++ prefTail pre line = line := by
  have ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp h
  have h1 : prefTail pre line = String.ofList t := by
    show String.ofList (line.toList.drop pre.toList.length) = String.ofList t
    rw [← ht, List.drop_append_length]
  have h2 : line = pre ++ String.ofList t := by
    apply String.toList_inj.mp
    show line.toList = (pre ++ String.ofList t).toList
    simp [String.toList_append, ht.symm]
  rw [h1, h2]

/-! ## the axiom report (`notes/axiom-report.md`) -/

/-- One package's block (the CLEAN face — a load-failed block exits 1
    and never enters the baseline; the grammar layer never expresses
    it). The two free-text lines carry their `axioms used: `/`violations: `
    prefixes VERBATIM (the gate's data spellings); the climb validates
    the prefixes. -/
structure AxiomBlock where
  dir : String
  decls : Nat
  axTail : String
  violTail : String
deriving Repr, Inhabited, DecidableEq

/-- The section line's dir charset (the gated packages' dirs). -/
def axDirChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'

/-- The dir head class: an `axDirChar` that is uppercase (the dirs'
    spelling; disjoint from the `## ` literal's `#`). -/
def axDirHead (c : Char) : Bool := axDirChar c && c.isUpper

theorem axDirHead_chain : ∀ c, axDirHead c = true → axDirChar c = true :=
  fun _ hc => (Bool.and_eq_true_iff.mp hc).1

/-- The dir lexeme (the shared ident-atom; the run breaks at the ` — `
    literal's space). -/
def axDirAtom : Lexeme String :=
  identAtom "<dir>" axDirHead axDirChar axDirHead_chain

/-- The `axioms used: ` prefix (the climb's keyword face). -/
def axPrefix : String := "axioms used: "

/-- The `violations: ` prefix. -/
def violPrefix : String := "violations: "

/-- The ten fixed header lines (`Gates.Axioms`'s `reportHeader` —
    moved here, ONE writer per format). -/
def axH1 : String := "# Axiom report — the global axiom surface"
def axH2 : String := "GENERATED by `lake exe gates axioms --write` — do not hand-edit."
def axH3 : String := "CI runs `gates axioms` without `--write`; a diff against this file fails the gate."
def axH4 : String := "Per package: every declaration of the listed root modules gets its axiom cone"
def axH5 : String := "from the kernel's CollectAxioms; the allowlist (propext, Classical.choice,"
def axH6 : String := "Quot.sound, disclosed _native.native_decide./_native.bv_decide. trust bases)"
def axH7 : String := "is LintKit.AxiomAllowlist's, consumed via LintKit.runLintersOnDecls."

/-- The header's raw face: seven text lines + three blank separators
    (the reportHeader's blank faces). -/
abbrev AxiomHdrRaw :=
  Unit × (Unit × (Unit × (Unit × (Unit ×
    (Unit × (Unit × (Unit × (Unit × Unit))))))))

open Grammar in
/-- The axiom report's fixed header (seven consts + the blanks).
    The committed file's line sequence: title, blank, GENERATED, CI,
    blank, Per-package×4, blank. -/
def axiomHdrG : Grammar AxiomHdrRaw :=
  .seq
    (.atom (fixedLine axH1))
    (.seq
      (.atom nlAtom)
      (.seq
        (.atom (fixedLine axH2))
        (.seq
          (.atom (fixedLine axH3))
          (.seq
            (.atom nlAtom)
            (.seq
              (.atom (fixedLine axH4))
              (.seq
                (.atom (fixedLine axH5))
                (.seq
                  (.atom (fixedLine axH6))
                  (.seq
                    (.atom (fixedLine axH7))
                    (.atom nlAtom)))))))))

/-- One section line's raw face: `## <dir> — <n> decls checked`. -/
abbrev AxSecRaw := (Unit × (String × (Unit × (Nat × Unit)))) × Unit

/-- The section line's body (the structural face — the dir/nat
    fields' WF rows are green: `#`/space/` — `/digit pairwise
    disjoint). -/
def axSecBody : Grammar (Unit × (String × (Unit × (Nat × Unit)))) :=
  .seq
    (.atom (constStrLex "## " (by decide)))
    (.seq
      (.atom axDirAtom)
      (.seq
        (.atom (constStrLex " — " (by decide)))
        (.seq
          (.atom natAtom)
          (.atom (constStrLex " decls checked" (by decide))))))

open Grammar in
/-- One section line = the body + the terminator. -/
def axSecLineG : Grammar AxSecRaw := .seq axSecBody (.atom nlAtom)

/-- One free-text line's raw face (the line-raw face; the prefix
    discipline is the climb's). -/
abbrev TxtRaw := String × Unit

open Grammar in
/-- One free-text line (the whole line is the run; the climb validates
    the keyword prefix). -/
def axTxtLineG : Grammar TxtRaw := .seq (.atom txtAtom) (.atom nlAtom)

/-- One block's raw face: sec, blank, ax, viol, blank, blank, blank
    (the committed file's seven-line block — the shard-captured block
    separator's TWO blanks + the block-boundary blank; the byte-tie
    ties the grammar to the COMMITTED bytes, the spec of record). -/
abbrev AxiomBlockRaw :=
  AxSecRaw × (Unit × (TxtRaw × (TxtRaw × (Unit × (Unit × Unit)))))

open Grammar in
/-- One package's block: section, blank, axioms line, violations line,
    blank, blank, blank. -/
def axiomBlockG : Grammar AxiomBlockRaw :=
  .seq axSecLineG
    (.seq (.atom nlAtom)
      (.seq axTxtLineG
        (.seq axTxtLineG
          (.seq (.atom nlAtom)
            (.seq (.atom nlAtom) (.atom nlAtom))))))

/-- The file's raw face: the header + the blocks' fold. -/
abbrev AxiomRaw := AxiomHdrRaw × List AxiomBlockRaw

/-- One block's section line's raw (elementwise). -/
def axSecRawOf (b : AxiomBlock) : AxSecRaw :=
  ⟨⟨(), (b.dir, ((), (b.decls, (()))))⟩, ()⟩

/-- One block's free-text faces' raw (elementwise). -/
def axSecondOf (b : AxiomBlock) :
    Unit × (TxtRaw × (TxtRaw × (Unit × (Unit × Unit)))) :=
  ⟨(), ⟨⟨axPrefix ++ b.axTail, ()⟩,
    ⟨⟨violPrefix ++ b.violTail, ()⟩, ((), ((), ()))⟩⟩⟩

/-- One block's raw spell (elementwise). -/
def axBlockRawOf (b : AxiomBlock) : AxiomBlockRaw :=
  ⟨axSecRawOf b, axSecondOf b⟩

/-- One block's climb (the prefix-validation face: a hand-edited
    keyword is a REFUSAL). -/
def axBlockClimb (p : AxiomBlockRaw) : Option AxiomBlock :=
  if prefOk axPrefix p.2.2.1.1 && prefOk violPrefix p.2.2.2.1.1 then
    some ⟨p.1.1.2.1, p.1.1.2.2.2.1,
      prefTail axPrefix p.2.2.1.1, prefTail violPrefix p.2.2.2.1.1⟩
  else none

/-- The climb inverts the spell, one block. -/
theorem axBlockClimb_axBlockRawOf (b : AxiomBlock) :
    axBlockClimb (axBlockRawOf b) = some b := by
  have hax : prefOk axPrefix (axPrefix ++ b.axTail) = true := by
    rw [prefOk, List.isPrefixOf_iff_prefix]
    exact ⟨b.axTail.toList, (String.toList_append).symm⟩
  have hviol : prefOk violPrefix (violPrefix ++ b.violTail) = true := by
    rw [prefOk, List.isPrefixOf_iff_prefix]
    exact ⟨b.violTail.toList, (String.toList_append).symm⟩
  show (if prefOk axPrefix (axPrefix ++ b.axTail)
      && prefOk violPrefix (violPrefix ++ b.violTail) then
    some ⟨b.dir, b.decls, prefTail axPrefix (axPrefix ++ b.axTail),
      prefTail violPrefix (violPrefix ++ b.violTail)⟩
  else none) = some b
  rw [hax, hviol, prefTail_pref, prefTail_pref]
  simp

/-- The spell inverts the climb, one block (the exactness's elementwise
    face — the prefix law supplies the keyword's return). -/
theorem axBlockRawOf_axBlockClimb (p : AxiomBlockRaw) (b : AxiomBlock)
    (h : axBlockClimb p = some b) : axBlockRawOf b = p := by
  rw [axBlockClimb] at h
  split at h
  · rename_i hcond
    have hb : ⟨p.1.1.2.1, p.1.1.2.2.2.1,
      prefTail axPrefix p.2.2.1.1, prefTail violPrefix p.2.2.2.1.1⟩ = b :=
      Option.some.inj h
    have hax3 : axPrefix ++ prefTail axPrefix p.2.2.1.1 = p.2.2.1.1 :=
      prefSplit axPrefix p.2.2.1.1 (Bool.and_eq_true_iff.mp hcond).1
    have hviol3 : violPrefix ++ prefTail violPrefix p.2.2.2.1.1
        = p.2.2.2.1.1 :=
      prefSplit violPrefix p.2.2.2.1.1 (Bool.and_eq_true_iff.mp hcond).2
    rw [← hb]
    simp only [axBlockRawOf, axSecRawOf, axSecondOf, hax3, hviol3]
  · exact absurd h (by simp)

theorem map_axBlockRound : ∀ bs : List AxiomBlock,
    (bs.map axBlockRawOf).map axBlockClimb = bs.map Option.some
  | [] => rfl
  | b :: rest => by
      simp only [List.map_cons, axBlockClimb_axBlockRawOf,
        map_axBlockRound, List.map_cons]

/-- The blocks' climb (the fold; a refusing block poisons the file). -/
def axiomBlocksOf : List AxiomBlockRaw → Option (List AxiomBlock)
  | [] => Option.some []
  | p :: rest =>
      match axBlockClimb p with
      | Option.none => Option.none
      | Option.some b => (axiomBlocksOf rest).map fun bs => b :: bs

/-- The climb's fold inverts the spell: a successful climb's blocks
    re-spell to the raws (the exactness's list face). -/
theorem axiomBlocksOf_map : ∀ (raws : List AxiomBlockRaw)
    (bs : List AxiomBlock), axiomBlocksOf raws = some bs →
    raws = bs.map axBlockRawOf := by
  intro raws bs
  induction raws generalizing bs with
  | nil =>
      intro h
      simp only [axiomBlocksOf] at h
      cases bs with
      | nil => rfl
      | cons b rest => simp at h
  | cons p rest ih =>
      intro h
      simp only [axiomBlocksOf] at h
      cases hc : axBlockClimb p with
      | none => rw [hc] at h; simp at h
      | some b =>
          rw [hc] at h
          obtain ⟨bs', hbs, hbeq⟩ := Option.map_eq_some_iff.mp h
          rw [← hbeq, List.map_cons,
            axBlockRawOf_axBlockClimb p b hc, ih bs' hbs]

/-- The header's ten unit payloads (the right-nested seq spine's raw). -/
def axiomHdrUnits : AxiomHdrRaw :=
  ((), ((), ((), ((), ((), ((), ((), ((), ((), ())))))))))

/-- THE axiom report codec: the climb validates the free-text lines'
    prefixes (the hand-edit detection at the parse face); the
    structural faces ride the grammar. -/
@[nolint linter.guestlang.graduation "the image iso is NOT free here: the decode is NOT total — the climb's prefix validation refuses a hand-edited keyword line (the hand-edit detection IS the parse face: `axBlockClimb`'s `prefOk` refusal), so `toIsoOfExact`'s totality premise is false over the raw carrier; the exactness law (`axiomExact`) is the honest strength"]
def axiomCodec : Kit.Codec AxiomRaw (List AxiomBlock) where
  encode := fun bs =>
    (axiomHdrUnits, bs.map axBlockRawOf)
  decode := fun raw => axiomBlocksOf raw.2
  policy := fun _ => True
  decode_encode := fun bs => by
    show axiomBlocksOf (bs.map axBlockRawOf) = Option.some bs
    induction bs with
    | nil => rfl
    | cons b rest ih =>
        simp only [List.map_cons, axiomBlocksOf, axBlockClimb_axBlockRawOf,
          ih, Option.map_some]
  decode_some_policy := fun _ _ _ => trivial

/-- The climb's exactness (the rel node's `exact` field) — the
    elementwise law rides the fold. -/
theorem axiomExact : ∀ (raw : AxiomRaw) (bs : List AxiomBlock),
    axiomCodec.decode raw = some bs → axiomCodec.encode bs = raw := by
  intro raw bs h
  show (axiomHdrUnits, bs.map axBlockRawOf) = raw
  have h2 : axiomBlocksOf raw.2 = Option.some bs := h
  rw [← axiomBlocksOf_map raw.2 bs h2]
  rfl

open Grammar in
/-- THE axiom report's grammar (the flat shape: the ten-line header,
    then the blocks' fold — each block six lines: section, blank,
    axioms, violations, blank, blank). -/
def axiomGrammar : Grammar (List AxiomBlock) :=
  .rel axiomCodec (fun _ => true) (fun _ _ _ => rfl) axiomExact "axiom-report" []
    (.seq axiomHdrG (.rep axiomBlockG))

/-- THE certificate (the flat shape's decide reduces — the diagnosis's
    positive face at the report's scale: ten header consts + the
    six-line blocks' fold). -/
theorem axiomCert : Grammar.Predictive axiomGrammar :=
  Grammar.wfCheck_sound axiomGrammar (by decide)

/-- The fix-free fold. -/
theorem axiomFixFree : Grammar.FixFree axiomGrammar := by
  repeat constructor

/-- Law 2's coherence premise (no `alt` — vacuous). -/
theorem axiomCoherent : Grammar.altCoherent axiomGrammar := by
  trivial

/-- The free-text tail's write-side discipline: nonempty, all non-LF,
    non-LF head (the txt-atom's ident gate at the tail). -/
def axTailOk (t : String) : Bool := identOk txtChar txtChar t

/-- The prefixed line's gate IS the tail's: the keyword's chars are
    all non-LF (the literals' own face). -/
theorem axTailOk_line (pre t : String) (hs : pre.toList.all txtChar = true)
    (hhead : pre.toList.head?.all txtChar = true)
    (ht : axTailOk t = true) :
    axTailOk (pre ++ t) = true := by
  show identOk txtChar txtChar (pre ++ t)
  simp only [TextKit.identOk, String.toList_append]
  have ht1 : (!t.toList.isEmpty) = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).1
  have ht2 : t.toList.all txtChar = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).2
  have ht3 : t.toList.head?.all txtChar = true :=
    (Bool.and_eq_true_iff.mp ht).2
  cases hpop : pre.toList.head? with
  | none =>
      have hnil : pre.toList = [] := by
        cases hpl : pre.toList with
        | nil => rfl
        | cons c cs => rw [hpl] at hpop; simp at hpop
      simp [hnil, ht1, ht2, ht3]
  | some c =>
      have hc : txtChar c = true := by
        rw [hpop] at hhead; simpa using hhead
      have htn : t ≠ "" := by
        intro hcon
        rw [hcon] at ht1
        simp at ht1
      simp [hpop, hc, ht1, ht2, hs, htn]

/-- The keyword prefixes' chars are all non-LF (the literals' face). -/
theorem axPrefix_chars : axPrefix.toList.all txtChar = true := by
  simp [axPrefix, txtChar]

theorem axPrefix_head : axPrefix.toList.head?.all txtChar = true := by
  simp [axPrefix, txtChar]

theorem violPrefix_chars : violPrefix.toList.all txtChar = true := by
  simp [violPrefix, txtChar]

theorem violPrefix_head : violPrefix.toList.head?.all txtChar = true := by
  simp [violPrefix, txtChar]

/-- The axiom report's write-side gate: the dir's ident discipline +
    the tails' non-LF discipline (the round-trip law's premise). -/
def axiomBlockOk (b : AxiomBlock) : Bool :=
  identOk axDirHead axDirChar b.dir
    && axTailOk b.axTail && axTailOk b.violTail

/-- The value discipline's lemma (the round-trip law's premise face). -/
theorem valueOk_axiom (bs : List AxiomBlock)
    (h : ∀ b ∈ bs, axiomBlockOk b = true) :
    Grammar.valueOk axiomGrammar bs = true := by
  have hblock : ∀ b : AxiomBlock, axiomBlockOk b = true →
      Grammar.valueOk axiomBlockG (axBlockRawOf b) = true := by
    intro b hok
    have hdir : identOk axDirHead axDirChar b.dir = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).1
    have hax : axTailOk b.axTail = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).2
    have hviol : axTailOk b.violTail = true :=
      (Bool.and_eq_true_iff.mp hok).2
    have haxG : Grammar.valueOk axTxtLineG
        (axPrefix ++ b.axTail, ()) = true := by
      show (identOk txtChar txtChar (axPrefix ++ b.axTail)
        && decide (() = ())) = true
      exact Bool.and_eq_true_iff.mpr ⟨axTailOk_line axPrefix b.axTail
        axPrefix_chars axPrefix_head hax, decide_eq_true rfl⟩
    have hviolG : Grammar.valueOk axTxtLineG
        (violPrefix ++ b.violTail, ()) = true := by
      show (identOk txtChar txtChar (violPrefix ++ b.violTail)
        && decide (() = ())) = true
      exact Bool.and_eq_true_iff.mpr ⟨axTailOk_line violPrefix b.violTail
        violPrefix_chars violPrefix_head hviol, decide_eq_true rfl⟩
    show Grammar.valueOk axiomBlockG (axBlockRawOf b) = true
    have hdir' : (!b.dir.toList.isEmpty && b.dir.toList.all axDirChar
        && Option.all axDirHead b.dir.toList.head?) = true := hdir
    simp only [Grammar.valueOk, axiomBlockG, axSecLineG,
      axSecBody, axBlockRawOf, axSecRawOf, axSecondOf, nlAtom, constCharLex,
      constStrLex, natAtom, axDirAtom, TextKit.identAtom, TextKit.identOk,
      hdir', haxG, hviolG]
    simp
  show (bs.map axBlockRawOf).all
    (fun z => Grammar.valueOk axiomBlockG z) = true
  rw [List.all_eq_true]
  intro z hz
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
  exact hblock b (h b hb)

/-- THE FILE-FORMAT LAW (the axiom report's instance). -/
theorem axiomRunPrint (bs : List AxiomBlock)
    (hval : Grammar.valueOk axiomGrammar bs = true) :
    Grammar.run axiomGrammar (Grammar.print axiomGrammar bs) = .ok bs :=
  Grammar.run_print_fixFree axiomGrammar axiomFixFree axiomCert bs hval

/-- The committed baseline's bytes. The grammar's print terminates the
    last line; the WRITE face's final newline is `Driver.reportGate`'s
    (`fresh ++ "\n"`) — the wrapper drops the print's terminator (the
    old render's contract). -/
def printAxiom (bs : List AxiomBlock) : String :=
  (Grammar.print axiomGrammar bs).dropEnd 1 |>.toString

/-- The fixed header's bytes (the shard-assembly's header face — the
    parent concatenates the shards' blocks after it). -/
def printAxiomHeader : String := Grammar.print axiomHdrG axiomHdrUnits

/-- One package's block's bytes (the shard's stdout face; the block's
    seven lines, each LF-terminated). -/
def printAxiomBlock (b : AxiomBlock) : String :=
  Grammar.print axiomBlockG (axBlockRawOf b)

/-- The committed file's parse face (the climb's prefix-validation
    teeth at the file grade). -/
def parseAxiom? (text : String) : Option (List AxiomBlock) :=
  match Grammar.run axiomGrammar (canonNl text) with
  | .ok bs => some bs | .error _ => none

/-! ## the coverage matrix (`notes/coverage-matrix.md`) -/

/-- One ctor's row: the tag + the emitter/registry cells (the cell
    SPLIT — which cell is the registry column — is the GATE's face:
    the count is the emitter table's, not the grammar's; a hand-edited
    count is a byte change, which is the diff face's tooth). -/
abbrev CovRow := String × List Bool

/-- The matrix's value: the ctor rows + the quiet section (the `(none)`
    face is `none`; the tag rows are `some`). -/
abbrev CovValue := List CovRow × List String

/-- The tag's charset (backtick/pipe-free; the table's metacharacters). -/
def covTagChar (c : Char) : Bool :=
  c != '`' && c != '|' && c != '\n' && c != '\r'

/-- The tag lexeme (the shared ident-atom at the tag charset). -/
def covTagAtom : Lexeme String :=
  identAtom "<tag>" covTagChar covTagChar (fun _ hc => hc)

/-- The cell's charset: the `x`/`.` spellings' class. -/
def covCellChar (c : Char) : Bool := c == 'x' || c == '.'

/-- The cell lexeme (over-accepts multi-char runs; the climb pins the
    canonical single-char spellings). -/
def covCellAtom : Lexeme String :=
  identAtom "<cell>" covCellChar covCellChar (fun _ hc => hc)

/-- The twelve fixed header lines (the render's first list — ONE
    writer). -/
def covH1 : String := "# Coverage matrix — the closed Ty universe's exercise surface"
def covH3 : String := "GENERATED by `lake exe gates coverage --write` — do not hand-edit."
def covH4 : String := "CI runs `gates coverage`; a diff against this file = a coverage-surface change (the gate)."
def covH6 : String := "Rows: the closed `Ty` universe (SchemaCore.Ty). Emitter columns are PROBE-DIFFERENTIAL:"
def covH7 : String := "a probe item carrying the ctor is added to the replayed registry and the emitter re-run —"
def covH8 : String := "`x` = the ctor renders with bytes of its own (distinct from every sibling ctor's probe),"
def covH9 : String := "`.` = byte-collides with some sibling ctor in that emitter (the declared"
def covH10 : String := "retraction-with-note rows surface here). `registry` = the ctor's tag occurs in the"
def covH11 : String := "committed registry's field types."

/-- The header's raw face: twelve lines (nine text + three blanks,
    at the render's positions). -/
abbrev CovHdrRaw :=
  Unit × (Unit × (Unit × (Unit × (Unit ×
    (Unit × (Unit × (Unit × (Unit × (Unit × (Unit × Unit))))))))))

open Grammar in
/-- The twelve-line header. -/
def covHdrG : Grammar CovHdrRaw :=
  .seq (.atom (fixedLine covH1))
    (.seq (.atom nlAtom)
      (.seq (.atom (fixedLine covH3))
        (.seq (.atom (fixedLine covH4))
          (.seq (.atom nlAtom)
            (.seq (.atom (fixedLine covH6))
              (.seq (.atom (fixedLine covH7))
                (.seq (.atom (fixedLine covH8))
                  (.seq (.atom (fixedLine covH9))
                    (.seq (.atom (fixedLine covH10))
                      (.seq (.atom (fixedLine covH11))
                        (.atom nlAtom)))))))))))

/-- The table's structure lines' raw (the current emitters' spell —
    a changed emitter set is a deliberate grammar update). -/
abbrev CovTblRaw := Unit × Unit

open Grammar in
/-- The table header + separator (the committed bytes' spell). -/
def covTblG : Grammar CovTblRaw :=
  .seq (.atom (fixedLine "| Ty ctor | schema-wit | schema-rust | schema-ts | registry |"))
    (.atom (fixedLine "| --- | --- | --- | --- | --- |"))

/-- One cell's raw face. -/
abbrev CovCellRaw := Unit × (String × Unit)

open Grammar in
/-- One cell: ` x |`. -/
def covCellG : Grammar CovCellRaw :=
  .seq (.atom (constStrLex " " (by decide)))
    (.seq (.atom covCellAtom) (.atom (constStrLex " |" (by decide))))

/-- One data row's raw face (the cells' rep + the terminator). -/
abbrev CovRowRaw :=
  (Unit × (String × (Unit × List CovCellRaw))) × Unit

open Grammar in
/-- One data row: `` | `<tag>` | `` then the cells' fold, then LF. -/
def covRowLineG : Grammar CovRowRaw :=
  .seq
    (.seq (.atom (constStrLex "| `" (by decide)))
      (.seq (.atom covTagAtom)
        (.seq (.atom (constStrLex "` |" (by decide)))
          (.rep covCellG))))
    (.atom nlAtom)

/-- One cell's raw spell. -/
def covCellRawOf (b : Bool) : CovCellRaw := ((), ((if b then "x" else "."), ()))

/-- One cell's climb (the canonicality tooth: a non-single-char or
    corrupted cell is a REFUSAL). -/
def covCellClimb (raw : CovCellRaw) : Option Bool :=
  if raw.2.1 = "x" then Option.some true
  else if raw.2.1 = "." then Option.some false
  else Option.none

theorem covCellClimb_covCellRawOf (b : Bool) :
    covCellClimb (covCellRawOf b) = Option.some b := by
  cases b <;> rfl

theorem covCellRawOf_covCellClimb (raw : CovCellRaw) (b : Bool)
    (h : covCellClimb raw = Option.some b) : covCellRawOf b = raw := by
  obtain ⟨u, ⟨s, u2⟩⟩ := raw
  rw [covCellClimb] at h
  cases b with
  | false =>
      split at h
      · exact absurd h (by simp)
      · split at h
        · rename_i h2
          have hs2 : s = "." := h2
          show ((), (".", ())) = (u, (s, u2))
          rw [hs2]
        · exact absurd h (by simp)
  | true =>
      split at h
      · rename_i h1
        have hs1 : s = "x" := h1
        show ((), ("x", ())) = (u, (s, u2))
        rw [hs1]
      · exact absurd h (by simp)

/-- The cells' climb (the fold; a corrupted cell poisons the row). -/
def covCellsOf : List CovCellRaw → Option (List Bool)
  | [] => Option.some []
  | c :: rest =>
      match covCellClimb c with
      | Option.none => Option.none
      | Option.some b => (covCellsOf rest).map fun bs => b :: bs

/-- One row's raw spell. -/
def covRowRawOf (r : CovRow) : CovRowRaw :=
  (⟨(), (r.1, ((), r.2.map covCellRawOf))⟩, ())

/-- One row's climb. -/
def covRowClimb (raw : CovRowRaw) : Option CovRow :=
  (covCellsOf raw.1.2.2.2).map fun bs => (raw.1.2.1, bs)

/-- The cells' climb inverts the spell. -/
theorem covCellsOf_map : ∀ cs : List Bool,
    covCellsOf (cs.map covCellRawOf) = Option.some cs
  | [] => rfl
  | b :: rest => by
      show covCellsOf (covCellRawOf b :: (rest.map covCellRawOf))
        = Option.some (b :: rest)
      rw [covCellsOf, covCellClimb_covCellRawOf]
      show Option.map (fun bs => b :: bs) (covCellsOf (rest.map covCellRawOf))
        = Option.some (b :: rest)
      rw [covCellsOf_map, Option.map_some]

/-- The cells' spell inverts the climb. -/
theorem covCellsOf_exact : ∀ (raws : List CovCellRaw) (bs : List Bool),
    covCellsOf raws = Option.some bs → raws = bs.map covCellRawOf := by
  intro raws
  induction raws with
  | nil =>
      intro bs h
      simp only [covCellsOf] at h
      cases bs with
      | nil => rfl
      | cons b rest => simp at h
  | cons c rest ih =>
      intro bs h
      simp only [covCellsOf] at h
      cases hc : covCellClimb c with
      | none => rw [hc] at h; simp at h
      | some b =>
          rw [hc] at h
          cases bs with
          | nil => simp at h
          | cons b2 bs' =>
              obtain ⟨hbs, heq, hbeq⟩ := Option.map_eq_some_iff.mp h
              have hbeq' : b = b2 ∧ hbs = bs' := by simpa using hbeq
              have hbb : b = b2 := hbeq'.1
              have hbs' : bs' = hbs := hbeq'.2.symm
              have hc2 : covCellClimb c = Option.some b2 := by rw [hc, hbb]
              rw [List.map_cons, covCellRawOf_covCellClimb c b2 hc2,
                ih hbs heq, hbs']

/-- One row's climb inverts the spell. -/
theorem covRowOf_covRowRawOf (r : CovRow) :
    covRowClimb (covRowRawOf r) = Option.some r := by
  show (covCellsOf (r.2.map covCellRawOf)).map (fun bs => (r.1, bs))
      = Option.some r
  rw [covCellsOf_map, Option.map_some]

/-- One row's spell inverts the climb. -/
theorem covRowRawOf_covRowClimb (raw : CovRowRaw) (r : CovRow)
    (h : covRowClimb raw = Option.some r) : covRowRawOf r = raw := by
  rw [covRowClimb, Option.map_eq_some_iff] at h
  obtain ⟨bs, hbs, hbeq⟩ := h
  rw [hbeq.symm]
  show (⟨(), ((raw.1.2.1), ((), bs.map covCellRawOf))⟩, ()) = raw
  rw [← covCellsOf_exact raw.1.2.2.2 bs hbs]

/-! ### the quiet section

The tag-rows face (`- \`set\`` lines) is the grammar's; the `(none)`
face (the empty-quiet spelling) is the GATE's single hand line — the
rel-lifted alt CANNOT express the pair: the none branch's rel codec
needs `decode (encode x) = some x` over the WHOLE shared value type,
and the singleton branch's decode cannot return the tag values (the
probe's wall datum — a genuine shape wall, not a reduction one). The
face lands when its first committed bytes do (the leftover rule). -/

/-- One quiet line's raw face. -/
abbrev CovQTagRaw := (Unit × (String × Unit)) × Unit

/-- One quiet line's tail: the tag + the closing backtick. -/
def covQTagTail : Grammar (String × Unit) :=
  .seq (.atom covTagAtom) (.atom (constStrLex "`" (by decide)))

/-- One quiet line's body: the `` - ` `` literal + the tail. -/
def covQTagBody : Grammar (Unit × (String × Unit)) :=
  .seq (.atom (constStrLex "- `" (by decide))) covQTagTail

open Grammar in
/-- One quiet tag line: `` - `<tag>` `` + LF. -/
def covQTagLineG : Grammar CovQTagRaw :=
  .seq covQTagBody (.atom nlAtom)

/-- One quiet tag's raw spell. -/
def covQTagRawOf (t : String) : CovQTagRaw :=
  (⟨(), (t, ())⟩, ())

/-- One quiet tag's climb. -/
def covQTagClimb (raw : CovQTagRaw) : String := raw.1.2.1

theorem covQTagClimb_covQTagRawOf (t : String) :
    covQTagClimb (covQTagRawOf t) = t := rfl

theorem covQTagRawOf_covQTagClimb (raw : CovQTagRaw) :
    covQTagRawOf (covQTagClimb raw) = raw := rfl

/-! ### the coverage codec + the file grammar -/

/-- The coverage file's raw face (the grammar's seq-spine's payload:
    the header+table pair, the rows' list, the blank, the quiet
    header, the second blank, the tags' list). -/
abbrev CovRaw :=
  (CovHdrRaw × CovTblRaw) ×
    (List CovRowRaw ×
      (Unit × ((Unit × (Unit × Unit)) ×
        (Unit × List CovQTagRaw))))

/-- The header's twelve unit payloads. -/
def covHdrUnits : CovHdrRaw :=
  ((), ((), ((), ((), ((), ((), ((), ((), ((), ((), ((), ())))))))))))

/-- The table lines' two units. -/
def covTblUnits : CovTblRaw := ((), ())

/-- The quiet header's three units (the THREE const lines; the blank
    AFTER them is the spine's own `nlAtom`). -/
def covQHdrUnits : Unit × (Unit × Unit) := ((), ((), ()))

/-- The quiet tags' round map (the climb∘spell = id). -/
theorem map_covQTagRound : ∀ ts : List String,
    (ts.map covQTagRawOf).map covQTagClimb = ts
  | [] => rfl
  | t :: rest => by
      rw [List.map_cons, List.map_cons, covQTagClimb_covQTagRawOf,
        map_covQTagRound]

/-- The rows' climb (the fold; a corrupted row poisons the matrix). -/
def covRowsOf : List CovRowRaw → Option (List CovRow)
  | [] => Option.some []
  | p :: rest =>
      match covRowClimb p with
      | Option.none => Option.none
      | Option.some r => (covRowsOf rest).map fun rs => r :: rs

/-- The rows' climb inverts the spell. -/
theorem covRowsOf_map : ∀ rs : List CovRow,
    covRowsOf (rs.map covRowRawOf) = Option.some rs := by
  intro rs
  induction rs with
  | nil => rfl
  | cons r rest ih =>
      show covRowsOf (covRowRawOf r :: (rest.map covRowRawOf))
        = Option.some (r :: rest)
      rw [covRowsOf, covRowOf_covRowRawOf]
      show Option.map (fun rs => r :: rs) (covRowsOf (rest.map covRowRawOf))
        = Option.some (r :: rest)
      rw [ih, Option.map_some]

/-- The rows' spell inverts the climb. -/
theorem covRowsOf_exact : ∀ (raws : List CovRowRaw) (rs : List CovRow),
    covRowsOf raws = Option.some rs → raws = rs.map covRowRawOf := by
  intro raws
  induction raws with
  | nil =>
      intro rs h
      simp only [covRowsOf] at h
      cases rs with
      | nil => rfl
      | cons r rest => simp at h
  | cons p rest ih =>
      intro rs h
      simp only [covRowsOf] at h
      cases hc : covRowClimb p with
      | none => rw [hc] at h; simp at h
      | some r =>
          rw [hc] at h
          cases rs with
          | nil => simp at h
          | cons r2 rs' =>
              obtain ⟨hres, heq, hreq⟩ := Option.map_eq_some_iff.mp h
              have hpair : r = r2 ∧ hres = rs' := by simpa using hreq
              have hc2 : covRowClimb p = Option.some r2 := by
                rw [hc, hpair.1]
              rw [List.map_cons, covRowRawOf_covRowClimb p r2 hc2,
                ih hres heq, hpair.2.symm]

/-- The quiet tags' raw round map (the climb∘spell = id at the raw
    face). -/
theorem map_covQTagRoundRaw : ∀ raws : List CovQTagRaw,
    (raws.map covQTagClimb).map covQTagRawOf = raws
  | [] => rfl
  | r :: rest => by
      rw [List.map_cons, List.map_cons, covQTagRawOf_covQTagClimb,
        map_covQTagRoundRaw]

/-- THE coverage matrix's codec: the rows' climb + the quiet tags'
    climb (the quiet VALUE is the tag list; the `(none)` face is the
    gate's hand line — see the section note). -/
@[nolint linter.guestlang.graduation "the image iso is NOT free here: the decode is NOT total — the rows' climb refuses a corrupted cell spelling (the `covCellClimb` refusal IS the corruption detection at the parse face), so `toIsoOfExact`'s totality premise is false over the raw carrier; the exactness law (`covExact`) is the honest strength"]
def covCodec : Kit.Codec CovRaw CovValue where
  encode := fun v =>
    ⟨⟨covHdrUnits, covTblUnits⟩,
      ⟨v.1.map covRowRawOf,
        ⟨(), ⟨covQHdrUnits, ⟨(), v.2.map covQTagRawOf⟩⟩⟩⟩⟩
  decode := fun raw =>
    (covRowsOf raw.2.1).map
      fun rs => (rs, raw.2.2.2.2.2.map covQTagClimb)
  policy := fun _ => True
  decode_encode := fun v => by
    obtain ⟨rows, quiet⟩ := v
    have hrows : covRowsOf (rows.map covRowRawOf) = Option.some rows :=
      covRowsOf_map rows
    show (covRowsOf (rows.map covRowRawOf)).map
        (fun rs => (rs, (quiet.map covQTagRawOf).map covQTagClimb))
      = Option.some (rows, quiet)
    rw [hrows, Option.map_some, map_covQTagRound]
  decode_some_policy := fun _ _ _ => trivial

/-- The climb's exactness (the rel node's `exact` field). -/
theorem covExact : ∀ (raw : CovRaw) (v : CovValue),
    covCodec.decode raw = Option.some v → covCodec.encode v = raw := by
  intro raw v h
  show ⟨⟨covHdrUnits, covTblUnits⟩,
    ⟨v.1.map covRowRawOf,
      ⟨(), ⟨covQHdrUnits, ⟨(), v.2.map covQTagRawOf⟩⟩⟩⟩⟩ = raw
  have h' : (covRowsOf raw.2.1).map
      (fun rs => (rs, raw.2.2.2.2.2.map covQTagClimb)) = Option.some v := h
  obtain ⟨rs, hrows, hface⟩ := Option.map_eq_some_iff.mp h'
  have hv : v = (rs, raw.2.2.2.2.2.map covQTagClimb) := hface.symm
  have h2 : covRowsOf raw.2.1 = Option.some v.1 := by
    rw [hrows, hv]
  rw [← covRowsOf_exact raw.2.1 v.1 h2]
  have hq : v.2.map covQTagRawOf = raw.2.2.2.2.2 := by
    rw [hv, map_covQTagRoundRaw]
  rw [hq]
  rfl

open Grammar in
/-- The quiet header's THREE const lines (the blank after them is the
    file spine's own line). -/
def covQHdrG : Grammar (Unit × (Unit × Unit)) :=
  .seq (.atom (fixedLine "## Registry-quiet ctors (absent from the committed registry —"))
    (.seq (.atom (fixedLine "unexercised members of the closed universe; findings, not failures;"))
      (.atom (fixedLine "`--strict` promotes)")))

open Grammar in
/-- THE coverage matrix's grammar (the flat shape: the twelve-line
    header, the table's two consts, the data rows' fold, the blank,
    the quiet header, the blank, the quiet tags' fold). -/
def covGrammar : Grammar CovValue :=
  .rel covCodec (fun _ => true) (fun _ _ _ => rfl) covExact "coverage" []
    (.seq
      (.seq covHdrG covTblG)
      (.seq
        (.rep covRowLineG)
        (.seq
          (.atom nlAtom)
          (.seq covQHdrG
            (.seq (.atom nlAtom) (.rep covQTagLineG))))))

/-- THE certificate (the flat shape's decide reduces). -/
theorem covCert : Grammar.Predictive covGrammar :=
  Grammar.wfCheck_sound covGrammar (by decide)

/-- The fix-free fold. -/
theorem covFixFree : Grammar.FixFree covGrammar := by
  repeat constructor

/-- Law 2's coherence premise (no `alt` — vacuous). -/
theorem covCoherent : Grammar.altCoherent covGrammar := by
  trivial

/-- The coverage's write-side gate: the tags' + cells' ident
    disciplines (the climb's canonical faces; the round-trip law's
    premise). -/
def covRowOk (r : CovRow) : Bool :=
  identOk covTagChar covTagChar r.1
    && r.2.all (fun b => Grammar.valueOk covCellG (covCellRawOf b))

/-- The value discipline's lemma (the round-trip law's premise face). -/
theorem valueOk_cov (v : CovValue)
    (hrows : ∀ r ∈ v.1, covRowOk r = true)
    (hquiet : ∀ t ∈ v.2, identOk covTagChar covTagChar t = true) :
    Grammar.valueOk covGrammar v = true := by
  obtain ⟨rows, quiet⟩ := v
  have hrow : ∀ r : CovRow, covRowOk r = true →
      Grammar.valueOk covRowLineG (covRowRawOf r) = true := by
    intro r hok
    have htag : identOk covTagChar covTagChar r.1 = true :=
      (Bool.and_eq_true_iff.mp hok).1
    have hcells : r.2.all
        (fun b => Grammar.valueOk covCellG (covCellRawOf b)) = true :=
      (Bool.and_eq_true_iff.mp hok).2
    show Grammar.valueOk covRowLineG (covRowRawOf r) = true
    have hcells' : r.2.all
        ((fun z => true && (covCellAtom.pre z.2.fst && true)) ∘ covCellRawOf) =
        true := hcells
    simp only [Grammar.valueOk, covRowLineG, covRowRawOf, covCellG,
      constStrLex, covTagAtom, TextKit.identAtom, constCharLex, nlAtom,
      List.all_map, htag, hcells']
    simp
  have hqtag : ∀ t : String, identOk covTagChar covTagChar t = true →
      Grammar.valueOk covQTagLineG (covQTagRawOf t) = true := by
    intro t hok
    show Grammar.valueOk covQTagLineG (covQTagRawOf t) = true
    simp only [Grammar.valueOk, covQTagLineG, covQTagBody, covQTagTail,
      constStrLex, covTagAtom, TextKit.identAtom, constCharLex, nlAtom, hok]
    simp only [Bool.and_true, decide_true]
    exact hok
  show Grammar.valueOk covGrammar (rows, quiet) = true
  simp only [Grammar.valueOk, covGrammar, covCodec, covHdrG, covTblG,
    covQHdrG, fixedLine, constStrLex, nlAtom, constCharLex]
  have hA : (rows.map covRowRawOf).all
      (fun z => Grammar.valueOk covRowLineG z) = true := by
    rw [List.all_eq_true]
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    exact hrow r (hrows r hr)
  have hB : (quiet.map covQTagRawOf).all
      (fun z => Grammar.valueOk covQTagLineG z) = true := by
    rw [List.all_eq_true]
    intro z hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    exact hqtag t (hquiet t ht)
  simp [hA, hB]

/-- THE FILE-FORMAT LAW (the coverage matrix's instance). -/
theorem covRunPrint (v : CovValue)
    (hval : Grammar.valueOk covGrammar v = true) :
    Grammar.run covGrammar (Grammar.print covGrammar v) = .ok v :=
  Grammar.run_print_fixFree covGrammar covFixFree covCert v hval

/-- The committed baseline's bytes (the TAG face; the `(none)` face is
    the gate's hand line — the section note). The grammar's print
    terminates the last line; the WRITE face's final newline is
    `Driver.reportGate`'s — the wrapper drops it (the old render's
    contract). -/
def printCov (v : CovValue) : String :=
  (Grammar.print covGrammar v).dropEnd 1 |>.toString

/-- The committed file's parse face. -/
def parseCov? (text : String) : Option CovValue :=
  match Grammar.run covGrammar (canonNl text) with
  | .ok v => some v | .error _ => none

end Gates.Baselines

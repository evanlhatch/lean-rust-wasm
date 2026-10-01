/-
# Kit.Ledger — the artifact ledger (notes/v3/09-gates-ops.md §4)

Every generated thing has a ledger row: path, emitter, the demand set
(the EXACT spec rows it folds PLUS the collection/enumeration
dependencies PLUS the emitter's own revision), the content hash, the
obligations it attests. The two query directions, as pure functions:

- BACKWARD: artifact → its spec rows ("what made this?").
- FORWARD: spec row → its artifacts ("what moves if I change this?" —
  the impact filter).

THE DEMAND-SET CORRECTION (the doctrine's review catch — do not
regress): recording previously-read rows is INSUFFICIENT — a query also
depends on ABSENCE, on ENUMERATION (a fold over a registry depends on
the registry's CONTENTS-as-a-set, not just the rows it returned), and
on the emitter's own code. So `DemandSet` carries:

- `rows` — the spec rows the fold read;
- `collections` — the registries/extensions read as a SET (whose
  GROWTH invalidates: a new row in a depended-on collection moves the
  artifact even though the artifact's `rows` never named it);
- `emitterRev` — the emitter's own code identity (a closure has no
  hashable face; the emitter declares its revision — an emitter edit
  that can move artifacts bumps it).

Conservative invalidation is PROVED here: `forward` NEVER under-reports
— every artifact whose demand touches the changed name, or reads ANY
collection in the change's collection set, is in the affected set
(`forward_covers_row`, `forward_growthInvalidates`). Exactness is
promised only where established (the collection face is conservative by
design: it may over-report, never under).

The file format (`notes/artifact-ledger.tsv`-shaped): one row per
line, SEVEN tab-separated fields
`path<TAB>emitter<TAB>rows<TAB>collections<TAB>emitterRev<TAB>hash<TAB>obligations`
(list fields are comma-joined; empty list = empty field), rows sorted
by path, LF endings, no blank lines. THE FORMAT IS A `TextKit.Grammar`
VALUE (05 §1's typed grammar layer — CodeRegistry's flat rep-of-lines
template): the derived parser/printer replaced the old hand-rolled
pair, and THE ROUND TRIP IS THE GENERIC THEOREMS' INSTANCE —
`parse_print` instantiates `Grammar.run_print_fixFree` (+ the wrapper's
newline discipline + the wf gate), `print_parse_raw` instantiates
`Grammar.print_parse`. The grammar's payload is the RAW face (the
seven fields' spellings): the semantic climb to `LedgerRow` (`toRow`)
composes at `parse`, because the climb is PREMISE-LADEN — a `Name`'s
`toString` spelling must re-parse (`rowSpellable`; true for every
dotted identifier, the only kind the emitters produce; quoted/escaped
`Name`s are outside the format, exactly as the old split-based parse
never re-derived them) — and the `rel` node's codec law is
UNCONDITIONAL, so a premise-laden climb cannot ride it. Parse REFUSES
unsorted/duplicate/malformed rows, and `selfStable` is the snapshot
discipline: the committed bytes must be exactly the canonical print (a
hand-edited ledger fails its own stability check).

Core-only. This module is the LEDGER'S DATA + queries; the WRITE path
(the one writer) lives in Kit.Emit — the emit spine's drivers compute
the rows as they write, and the per-package driver rewrites the ledger
file from the emitted set. Gates/inspector read the ledger, never
re-derive it. The committed ledger file itself lands when the first
driver wiring writes it (the byte-tie wave); until then the
header↔ledger agreement (`checkHeader`) is exposed as the pure check
its gate consumes.

The five questions (notes/v3/01-core.md):
- root: DATA — the artifact universe's provenance rows (one carrier:
  `LedgerRow`), read by two total queries.
- carrier grade: the conservatism theorems — `forward`'s
  never-under-reports face proved (rows face + collection-growth face).
- spine reading: the artifact stage's provenance face (09 §4); ONE
  writer (Kit.Emit), readers elsewhere.
- ladder rung: rung 1-2 — total folds over lists; the two conservatism
  theorems are one-`simp` inductions off `List.mem_filter`; the format's
  round trip is the generic laws' INSTANCE (the lexeme fields + the
  wrapper discipline + the spellability premise are the only
  format-local proofs).
- gate row: none yet — `checkHeader` is the pure face; the gate row
  lands with the committed ledger file (the named follow-up).
-/

module

public import Lean
public import TextKit.Basic
public import TextKit.Grammar
public import TextKit.Grammar.Lexemes
public import TextKit.Grammar.Check
public import TextKit.Grammar.Laws
public import Kit.Diag
public import Kit.CodeRegistry

@[expose] public section

open Lean

namespace Kit.Ledger

/-! ## the demand set — the correction, as data -/

/-- WHAT the emission depends on (09 §4's correction): the rows the
    fold read PLUS the collections it enumerated (whose growth
    invalidates) PLUS the emitter's own code identity. -/
structure DemandSet where
  /-- The spec rows the fold read (the exact rows — populated by the
      emitters that can name them; the generic driver layer records the
      collection face). -/
  rows : List Name := []
  /-- The registries/extensions read AS A SET — a fold over a registry
      depends on its contents-as-a-set, so a NEW row in a depended-on
      collection invalidates the artifact even though `rows` never
      named it (the conservative face, proved below). -/
  collections : List Name := []
  /-- The emitter's own revision (the code identity of the fold; a
      closure has no hashable face — the declaration IS the record). -/
  emitterRev : String := "-"
deriving BEq, DecidableEq, Repr, Inhabited

/-! ## the row -/

/-- One ledger row: the artifact's provenance. -/
structure LedgerRow where
  /-- Repo-root-relative artifact path (the ledger's key; sorted). -/
  path : String
  /-- The emitting plugin's name. -/
  emitter : String
  /-- The demand set (the correction's carrier, above). -/
  demand : DemandSet
  /-- The artifact's content hash — the SAME value the artifact's
      2-line GENERATED header names (the agreement check below). -/
  contentHash : UInt64
  /-- The obligation labels the emitter attests for this artifact. -/
  obligations : List String := []
deriving BEq, DecidableEq, Repr, Inhabited

/-! ## the queries — backward and forward -/

/-- BACKWARD query ("what made this?"): the artifact's demand's FULL
    spec surface — the rows it folded PLUS the collections it
    enumerated. The rows-only shape is the pre-correction query the
    doctrine rejects (it cannot see the enumeration face). `[]` for an
    untracked path (the caller's loud gap). -/
def backward (ledger : List LedgerRow) (path : String) : List Name :=
  match ledger.find? (fun a => a.path == path) with
  | some a => a.demand.rows ++ a.demand.collections
  | none => []

/-- FORWARD query ("what moves if I change this?"): `r` is the changed
    spec row, `cs` the collections whose contents changed (r lives in
    them, or grew by them). An artifact is affected iff its demand
    READS the row or ANY changed collection. Conservative: the theorem
    twins below prove it never under-reports (exactness for the rows
    face, conservatism for the collection-growth face — a fold's
    contents-as-a-set dependency can over-report, never under). -/
def forward (r : Name) (cs : List Name) (ledger : List LedgerRow) :
    List LedgerRow :=
  ledger.filter (fun a =>
    decide (r ∈ a.demand.rows)
      || cs.any (fun c => decide (c ∈ a.demand.collections)))

/-- THE ROWS FACE of the never-under-reports discipline: an artifact
    whose demand read the changed row IS in the affected set. -/
theorem forward_covers_row (r : Name) (cs : List Name) (ledger : List LedgerRow)
    (a : LedgerRow) (ha : a ∈ ledger) (hr : r ∈ a.demand.rows) :
    a ∈ forward r cs ledger := by
  rw [forward, List.mem_filter]
  exact ⟨ha, by simp [decide_eq_true hr]⟩

/-- THE COLLECTION-GROWTH FACE (the demand-set correction's provable
    tooth): an artifact that merely ENUMERATED collection `c` is in the
    affected set for a change to `c`'s contents — a NEW row in a
    depended-on collection invalidates it, though its `rows` never
    named the new row. The pre-correction (rows-only) query
    under-reports exactly this case. -/
theorem forward_growthInvalidates (r c : Name) (cs : List Name)
    (ledger : List LedgerRow) (a : LedgerRow)
    (ha : a ∈ ledger) (hc : c ∈ a.demand.collections) (hcs : c ∈ cs) :
    a ∈ forward r cs ledger := by
  rw [forward, List.mem_filter]
  refine ⟨ha, ?_⟩
  simp only [Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨c, hcs, decide_eq_true hc⟩

/-- The review-failure detector: generated paths with NO ledger row
    ("a generated file without a ledger row is a review failure"). -/
def withoutRow (ledger : List LedgerRow) (paths : List String) : List String :=
  paths.filter (fun p => !(ledger.any (fun a => a.path == p)))

/-! ## the header ↔ ledger agreement (the self-audit face) -/

/-- The agreement verdict (ctors, never strings — 04 §6). -/
inductive LedgerAgreement where
  | ok
  | noRow
  | malformedHeader (why : String)
  | hashMismatch (inHeader inRow : UInt64)
deriving BEq, DecidableEq, Repr, Inhabited

/-- The content hash the header's 2nd line names (its `content hash
    <n>` field, Kit.Emit's 2-line GENERATED shape). Total; `none` = no
    hash field (a malformed header). -/
def headerHashOf (headerLine : String) : Option UInt64 :=
  (headerLine.splitOn "|").findSome? fun seg =>
    let t := seg.trimAscii
    if t.startsWith "content hash " then
      match TextKit.scanNat ((t.drop ("content hash ".length : Nat)).toString).toList with
      | some (n, _) => some (UInt64.ofNat n)
      | none => none
    else none

/-- The header ↔ ledger agreement check (the self-audit's finding
    face): the artifact's committed header's content hash vs its ledger
    row's. A mismatch — a regenerated artifact without its ledger
    rewrite, or a hand-edited ledger — is a finding for the gates'
    audit. `noRow` = the review failure (generated file, no row). -/
def checkHeader (ledger : List LedgerRow) (path : String)
    (headerLine : String) : LedgerAgreement :=
  match ledger.find? (fun a => a.path == path) with
  | none => .noRow
  | some row =>
      match headerHashOf headerLine with
      | none =>
          .malformedHeader
            "the header's 2nd line carries no `content hash <n>` field"
      | some h =>
          if h == row.contentHash then .ok else .hashMismatch h row.contentHash

/-! ## the file format — a Grammar value (05 §1's typed grammar layer) -/

open TextKit

/-- A ledger field's charset: anything but the line separators (tab, LF,
    CR). The ONE separator-charset def — CodeRegistry's `rowNameChar`
    (same body, same intent: a persisted-text field is separator-free);
    the lint's dedup preference honored by consumption, not a twin. -/
def fieldChar (c : Char) : Bool := CodeRegistry.rowNameChar c

/-- A list-field member's charset: the field charset minus the comma —
    the list separator is a metacharacter (the maximal-munch boundary
    inside a list field; the old split-based parse enforced the same
    class by construction). -/
def listChar (c : Char) : Bool := fieldChar c && !(c == ',')

/-- A dotted name's spelling back to a `Name` (`a.b` — the fold of the
    dot-split components; the mirror of `toString`). -/
def namesOf (s : String) : Name :=
  (s.splitOn ".").foldl Name.mkStr Name.anonymous

/-- The comma-joined name list (the list fields' face; empty = empty).
    The Inspector's report renders through it. -/
def namesCsv (ns : List Name) : String :=
  String.intercalate "," (ns.map toString)

/-- The comma-joined string list. -/
def strsCsv (xs : List String) : String :=
  String.intercalate "," xs

/-! ### the lexemes (TextKit.Grammar.Lexemes' shared constructors —
     the 06 §7 generator: the per-format constructions were N
     near-identical ~300-line proofs; the obligations discharge ONCE
     at the generic shape, and these are the instantiations) -/

/-- The ledger's separator literals: CodeRegistry's shared const-char
    atoms (the SAME lexemes — consumed, not re-rolled; the registry
    has no comma, the list separator is the ledger's own). -/
def tabAtom : Lexeme Unit := CodeRegistry.tabAtom
def nlAtom : Lexeme Unit := CodeRegistry.nlAtom
def commaAtom : Lexeme Unit := CodeRegistry.charLex ','

/-- A single field's write-side gate: nonempty + separator-free (the
    old `okField`'s exact discipline, at the ident-atom's face). -/
def fieldOk (s : String) : Bool :=
  (!s.toList.isEmpty && s.toList.all fieldChar) && s.toList.head?.all fieldChar

/-- `fieldOk` IS the shared ident-atom's gate at the field charset
    (the head class = the run class — a field's first char is a field
    char iff it is nonempty). -/
theorem fieldOk_eq (s : String) :
    fieldOk s = TextKit.identOk fieldChar fieldChar s := rfl

/-- The single-field lexeme (path / emitter / emitterRev): the shared
    ident-atom at the separator-free charset (`munch` is the charset
    itself — the TAB literal breaks it, the maximal-munch boundary). -/
def fieldAtom : Lexeme String :=
  TextKit.identAtom "<field>" fieldChar fieldChar (fun _ hc => hc)

/-- A list member's write-side gate: nonempty + separator- AND
    comma-free (a member cannot name the separator). -/
def listOk (s : String) : Bool :=
  (!s.toList.isEmpty && s.toList.all listChar) && s.toList.head?.all listChar

/-- `listOk` IS the shared ident-atom's gate at the member charset. -/
theorem listOk_eq (s : String) :
    listOk s = TextKit.identOk listChar listChar s := rfl

/-- The list-member lexeme: the shared ident-atom at the comma-free
    charset (the COMMA literal breaks the munch). -/
def listAtom : Lexeme String :=
  TextKit.identAtom "<member>" listChar listChar (fun _ hc => hc)

/-! ### the raw row + the line -/

/-- One list field's raw spelling: the FIRST member + the rest (the
    empty list = the empty field = `none`; the units ride the separator
    atoms' payloads — the tuple face's marker noise). -/
abbrev CsvRaw := String × List (Unit × String)

/-- The name-list field's raw spelling. -/
def namesRaw : List Name → Option CsvRaw
  | [] => Option.none
  | n :: rest => Option.some (n.toString, rest.map (fun n => ((), n.toString)))

/-- The string-list field's raw spelling. -/
def strsRaw : List String → Option CsvRaw
  | [] => Option.none
  | x :: rest => Option.some (x, rest.map (fun s => ((), s)))

/-- A list field's members back as strings (the decode's raw face). -/
def listMembers : Option CsvRaw → List String
  | Option.none => []
  | Option.some (x, rest) => x :: rest.map (·.2)

/-- The raw row: the seven fields' spellings — path, emitter, the two
    name lists, the emitter's revision, the hash (the nat spelling of
    the UInt64), the obligations — with the six TAB markers' units
    between (the seq's tuple face; the units are the separators'
    payloads — the registry template's marker noise). -/
abbrev RowTuple :=
  String × Unit × String × Unit × Option CsvRaw × Unit × Option CsvRaw ×
    Unit × String × Unit × Nat × Unit × Option CsvRaw

open Grammar in
/-- One list field: members comma-joined (the rep's stop-firsts are the
    comma literal; the continuation's TAB/NL are disjoint from both the
    member class and the comma). -/
def csvListGrammar : Grammar CsvRaw :=
  .seq (.atom listAtom) (.rep (.seq (.atom commaAtom) (.atom listAtom)))

open Grammar in
/-- One row: the seven tab-separated fields (the seq/opt tuple face).
    The TABs are FIRST-CLASS seq elements — a field→field junction's
    right first is a char class, and the certificate's `breaks`
    conservatively rejects cls heads (design §2.2's WF-SEQ-2); the
    literal between keeps every junction decidable. -/
def rowTupleGrammar : Grammar RowTuple :=
  .seq (.atom fieldAtom)
    (.seq (.atom tabAtom) (.seq (.atom fieldAtom)
      (.seq (.atom tabAtom) (.seq (.opt csvListGrammar)
        (.seq (.atom tabAtom) (.seq (.opt csvListGrammar)
          (.seq (.atom tabAtom) (.seq (.atom fieldAtom)
            (.seq (.atom tabAtom) (.seq (.atom natAtom)
              (.seq (.atom tabAtom) (.opt csvListGrammar))))))))))))

open Grammar in
/-- One line: the row + the LF terminator (one per line — the committed
    file's discipline; the parse wrapper handles a MISSING final
    newline). -/
def lineRawGrammar : Grammar (RowTuple × Unit) :=
  .seq rowTupleGrammar (.atom nlAtom)

/-- THE file format as a grammar value: the flat rep-of-lines (the
    slice's shape — no `fix`, no `self` anywhere). The payload is the
    RAW face (the tuple): the semantic climb to `LedgerRow` — `toRow` —
    composes at `parse` (the module header's premise-laden-climb note;
    the deliberate catalog delta: CodeRegistry's template rides `rel`
    because ITS codec is unconditional). -/
def ledgerGrammar : Grammar (List (RowTuple × Unit)) := .rep lineRawGrammar

/-! ### the climb (raw → the row) + the write-side gates -/

/-- The climb: a raw row's spellings → the `LedgerRow` (the hash's nat
    spelling rides `UInt64.ofNat` — the same wrap the old `parseHash`
    did; the list fields' members climb through `namesOf`). -/
def toRow : RowTuple → LedgerRow :=
  fun (path, (), emitter, (), rows, (), cols, (), rev, (), hash, (), obl) =>
    { path := path, emitter := emitter
    , demand := { rows := (listMembers rows).map namesOf
                , collections := (listMembers cols).map namesOf
                , emitterRev := rev }
    , contentHash := UInt64.ofNat hash
    , obligations := listMembers obl }

/-- The line-level climb (the line grammar's payload is the row + the
    LF marker's unit; the marker drops). -/
def toLine : RowTuple × Unit → LedgerRow := fun z => toRow z.1

/-- The spell: a row → its raw tuple (the grammar's printer consumes
    THIS — the raw face's encode). -/
def rowEncode : LedgerRow → RowTuple :=
  fun a => (a.path, (), a.emitter, (), namesRaw a.demand.rows,
    (), namesRaw a.demand.collections, (), a.demand.emitterRev,
    (), a.contentHash.toNat, (), strsRaw a.obligations)

/-- The row's write-side gate (the valueOk premise's value face): the
    single fields `fieldOk`, every list member `listOk`. -/
def rowOk (a : LedgerRow) : Bool :=
  fieldOk a.path && fieldOk a.emitter && fieldOk a.demand.emitterRev &&
    a.demand.rows.all (fun n => listOk n.toString) &&
    a.demand.collections.all (fun n => listOk n.toString) &&
    a.obligations.all listOk

/-- The spellability premise: the row's names re-derive from their
    `toString` spellings (every dotted identifier — the format's value
    face; the law's hypothesis, since the raw face cannot carry it and
    no unconditional codec can climb). -/
def rowSpellable (a : LedgerRow) : Prop :=
  (∀ n ∈ a.demand.rows, namesOf n.toString = n) ∧
  (∀ n ∈ a.demand.collections, namesOf n.toString = n)

/-- The units' cancellation: a marker-noise map round trips (the
    tuple face's noise, cancelled once). -/
private theorem units_map_snd (ss : List String) :
    (ss.map (fun s => ((), s))).map (fun p => p.2) = ss := by
  induction ss with
  | nil => rfl
  | cons a ss ih => rw [List.map_cons, List.map_cons, ih]

private theorem units_map_toString (ns : List Name) :
    (ns.map (fun n => ((), n.toString))).map (fun p => p.2) = ns.map (·.toString) := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [List.map_cons, List.map_cons, ih]; rfl

/-- The members of a name list climb back, under spellability (the
    per-element face). -/
private theorem map_namesOf_toString : ∀ (ns : List Name),
    (∀ n ∈ ns, namesOf n.toString = n) → (ns.map (·.toString)).map namesOf = ns
  | [], _ => rfl
  | n :: rest, h => by
      rw [List.map_cons, List.map_cons, h n (List.Mem.head _),
        map_namesOf_toString rest (fun m hm => h m (List.Mem.tail _ hm))]

/-- The climb inverts the name list's spelling, under spellability. -/
private theorem namesMembers_namesRaw : ∀ (ns : List Name),
    (∀ n ∈ ns, namesOf n.toString = n) → (listMembers (namesRaw ns)).map namesOf = ns
  | [], _ => rfl
  | n :: rest, h => by
      rw [namesRaw, listMembers, List.map_cons,
        units_map_toString rest,
        h n (List.Mem.head _),
        map_namesOf_toString rest (fun m hm => h m (List.Mem.tail _ hm))]

/-- The string-list field's climb (unconditional — the obligations'
    members are strings). -/
private theorem listMembers_strsRaw : ∀ xs : List String,
    listMembers (strsRaw xs) = xs
  | [] => rfl
  | x :: xs => by
      rw [strsRaw, listMembers, units_map_snd]
/-- THE CLIMB'S INVERSION: the climb of the spell is the row. The
    spellability premise is exactly what the name lists need; the hash's
    UInt64 round trip is core's `UInt64.ofNat_toNat`; the string-list
    fields round trip unconditionally. -/
theorem toRow_rowEncode (a : LedgerRow) (hs : rowSpellable a) :
    toRow (rowEncode a) = a := by
  obtain ⟨hrows, hcols⟩ := hs
  rw [rowEncode]
  simp only [toRow]
  rw [namesMembers_namesRaw a.demand.rows hrows,
      namesMembers_namesRaw a.demand.collections hcols,
      listMembers_strsRaw a.obligations, UInt64.ofNat_toNat]

/-! ### the certificate + the law premises' discharge -/

/-- THE certificate discharge (06 §7's build-time check): the format's
    WF rows hand-check green (WF-REP-1: the line is non-nullable;
    WF-REP-2: vacuous — the LF atom's munch is none; WF-SEQ-1: the
    field/member/hash heads vs the TAB/NL literals are prefix-free;
    WF-SEQ-2: the fields' munches broken by the TAB literal, the
    members' munch broken by the COMMA literal, the hash's munch broken
    by the TAB literal). -/
theorem ledgerCert : Grammar.Predictive ledgerGrammar :=
  Grammar.wfCheck_sound ledgerGrammar (by decide)

/-- The fix-free fold (no `fix` node anywhere). -/
theorem ledgerFixFree : Grammar.FixFree ledgerGrammar := by
  repeat constructor

/-- Law 2's coherence premise: NO `alt` node anywhere — the fold's
    branches are all trivial. -/
theorem ledgerCoherent : Grammar.altCoherent ledgerGrammar := by
  repeat constructor

/-- A list field's value discipline. -/
def csvOk (csv : CsvRaw) : Bool := listOk csv.1 && csv.2.all (fun p => listOk p.2)

/-- The list field's valueOk: the members' lexeme gate (the first
    member + every rep iteration's). -/
theorem valueOk_csvList (csv : CsvRaw) (h : csvOk csv = true) :
    Grammar.valueOk csvListGrammar csv = true := by
  have hpair := Bool.and_eq_true_iff.mp h
  have h1 : listAtom.pre csv.1 = true := by
    show TextKit.identOk listChar listChar csv.1 = true
    rw [← listOk_eq]
    exact hpair.1
  have h2 : csv.2.all (fun p => Grammar.valueOk
      (.seq (.atom commaAtom) (.atom listAtom)) p) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hp2 : listOk p.2 = true := List.all_eq_true.mp hpair.2 p hp
    obtain ⟨u, m⟩ := p
    rw [Grammar.valueOk_seq]
    refine Bool.and_eq_true_iff.mpr ⟨rfl, ?_⟩
    show TextKit.identOk listChar listChar m = true
    rw [← listOk_eq]
    exact hp2
  show Grammar.valueOk (.seq (.atom listAtom)
    (.rep (.seq (.atom commaAtom) (.atom listAtom)))) csv = true
  rw [Grammar.valueOk_seq, Grammar.valueOk_rep]
  exact Bool.and_eq_true_iff.mpr ⟨h1, h2⟩

/-- The name-list field's valueOk: every name's spelling passes the
    member gate. -/
theorem valueOk_namesRaw (ns : List Name)
    (h : ns.all (fun n => listOk n.toString) = true) :
    Grammar.valueOk (.opt csvListGrammar) (namesRaw ns) = true := by
  cases ns with
  | nil => rfl
  | cons n rest =>
      have hall : ∀ m ∈ n :: rest, listOk m.toString = true :=
        fun m hm => List.all_eq_true.mp h m hm
      have h1 : listOk n.toString = true := hall n (List.Mem.head _)
      have h3 : (rest.map (fun n => ((), n.toString))).all
          (fun p => listOk p.2) = true := by
        rw [List.all_eq_true]
        intro p hp
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
        exact hall m (List.Mem.tail _ hm)
      exact valueOk_csvList (n.toString, rest.map (fun n => ((), n.toString)))
        (Bool.and_eq_true_iff.mpr ⟨h1, h3⟩)

/-- The string-list field's valueOk: every obligation passes the member
    gate. -/
theorem valueOk_strsRaw (xs : List String) (h : xs.all listOk = true) :
    Grammar.valueOk (.opt csvListGrammar) (strsRaw xs) = true := by
  cases xs with
  | nil => rfl
  | cons x rest =>
      have hall : ∀ m ∈ x :: rest, listOk m = true :=
        fun m hm => List.all_eq_true.mp h m hm
      have h1 : listOk x = true := hall x (List.Mem.head _)
      have h3 : (rest.map (fun s => ((), s))).all (fun p => listOk p.2) = true := by
        rw [List.all_eq_true]
        intro p hp
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
        exact hall m (List.Mem.tail _ hm)
      exact valueOk_csvList (x, rest.map (fun s => ((), s)))
        (Bool.and_eq_true_iff.mpr ⟨h1, h3⟩)

/-- One line's valueOk: the seven fields' gates + the separators' atoms
    (the value discipline is the lexemes' `pre`s and nothing else — the
    nat/hash field is pre-free). -/
theorem valueOk_line (a : LedgerRow) (h : rowOk a = true) :
    Grammar.valueOk lineRawGrammar (rowEncode a, ()) = true := by
  have e1 := Bool.and_eq_true_iff.mp h
  have e2 := Bool.and_eq_true_iff.mp e1.1
  have e3 := Bool.and_eq_true_iff.mp e2.1
  have e4 := Bool.and_eq_true_iff.mp e3.1
  have e5 := Bool.and_eq_true_iff.mp e4.1
  obtain ⟨hp, he⟩ := e5
  have hv := e4.2
  have hr := e3.2
  have hc := e2.2
  have ho := e1.2
  have hpf : ∀ s : String, fieldOk s = true → fieldAtom.pre s = true := by
    intro s hs
    show TextKit.identOk fieldChar fieldChar s = true
    rw [← fieldOk_eq]; exact hs
  have hn1 : Grammar.valueOk (.opt csvListGrammar) (namesRaw a.demand.rows) = true :=
    valueOk_namesRaw a.demand.rows hr
  have hn2 : Grammar.valueOk (.opt csvListGrammar) (namesRaw a.demand.collections) = true :=
    valueOk_namesRaw a.demand.collections hc
  have ho1 : Grammar.valueOk (.opt csvListGrammar) (strsRaw a.obligations) = true :=
    valueOk_strsRaw a.obligations ho
  simp only [lineRawGrammar, rowTupleGrammar, rowEncode,
    Grammar.valueOk_seq]
  rw [hn1, hn2, ho1]
  simp [natAtom, tabAtom, nlAtom, CodeRegistry.tabAtom,
    CodeRegistry.nlAtom, CodeRegistry.charLex, TextKit.constCharLex]
  exact ⟨hpf a.path hp, hpf a.emitter he, hpf a.demand.emitterRev hv⟩

/-- The grammar's value discipline IS the row discipline: `valueOk`
    holds exactly when every row passes `rowOk` (the write-side gate;
    every other field is trivially owned). -/
theorem valueOk_ledger (ledger : List LedgerRow)
    (h : ∀ row ∈ ledger, rowOk row = true) :
    Grammar.valueOk ledgerGrammar (ledger.map (fun row => (rowEncode row, ()))) = true := by
  show (ledger.map (fun row => (rowEncode row, ()))).all
    (fun z => Grammar.valueOk lineRawGrammar z) = true
  rw [List.all_eq_true]
  intro z hz
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hz
  exact valueOk_line row (h row hr)

/-! ### the well-formedness + the one diagnostic envelope -/

/-- Sorted by path, by adjacency (the executable sortedness). -/
def sortedByPath : List LedgerRow → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a.path <= b.path && sortedByPath (b :: rest)

/-- The ledger's well-formedness: paths unique (one row per artifact —
    the one-writer discipline's read face) and sorted by path (the
    snapshot discipline's canonical order). -/
def wf (ledger : List LedgerRow) : Bool :=
  decide ((ledger.map (·.path)).Nodup) && sortedByPath ledger

/-- The KL family's ledger rows — allocated from the PERSISTED registry
    (`notes/code-registry.txt`); the constants are the declaration, the
    code-registry gate's coverage scan ties the spellings to the live
    rows. -/
def eKL0007 : Kit.ECode := ⟨"KL0007"⟩
def eKL0008 : Kit.ECode := ⟨"KL0008"⟩

/-- The ledger's parse refusal, in the ONE envelope's rendering: the
    kind rides the registry's KL row, the text keeps the
    `artifact-ledger:` channel prefix. -/
def ledgerDiag (code : Kit.ECode) (message : String) : String :=
  Kit.Diag.toString { code := code, message := s!"artifact-ledger: {message}" }

/-! ### the derived print/parse (the wrappers) -/

/-- The line's spelling (the derived printer at the raw line) — the old
    hand-rolled `renderRow`'s bytes, now the grammar's. -/
def linePrint : RowTuple × Unit → String := Grammar.print lineRawGrammar

/-- Print the ledger: the grammar's derived printer — one row per line,
    LF-terminated (the committed file's canonical bytes; byte-identical
    to the hand-rolled print it replaces; the caller owns the sort —
    `canonicalize` in Kit.Emit's writer). -/
def print (ledger : List LedgerRow) : String :=
  Grammar.print ledgerGrammar (ledger.map (fun row => (rowEncode row, ())))

/-- Parse the file: the grammar's derived parser (the run entry) + the
    climb + the well-formedness gate — an ill-formed (unsorted,
    duplicate-pathed) ledger is a REFUSAL, never a silent accept. The
    trailing-newline discipline: a MISSING final newline canonicalizes
    (the wrapper appends the LF the line terminator needs; the empty
    file is the empty ledger). The refusals ride the ONE diagnostic
    envelope (05 §4): the malformed-row kind is the registry's KL0007
    row, the ill-formed kind KL0008 — the parse refusals are
    positional/structural, so the literal Diag is the honest shape
    there. -/
def parse (s : String) : Except String (List LedgerRow) :=
  let s' := if s == "" || s.toList.getLast? == some '\n' then s else s ++ "\n"
  match Grammar.run ledgerGrammar s' with
  | .error _ =>
      .error (ledgerDiag eKL0007 "malformed row — expected \
`path<TAB>emitter<TAB>rows<TAB>collections<TAB>emitterRev<TAB>hash<TAB>obligations` \
(list fields comma-joined; no blank lines)")
  | .ok raws =>
      let ledger := raws.map toLine
      if wf ledger then .ok ledger
      else .error (ledgerDiag eKL0008 "ill-formed ledger — paths must be \
unique and rows sorted by path")

private theorem print_nil : print [] = "" := rfl

private theorem print_cons (row : LedgerRow) (rest : List LedgerRow) :
    print (row :: rest) = (linePrint (rowEncode row, ())) ++ print rest := rfl

private theorem linePrint_last_newline (row : LedgerRow) :
    (linePrint (rowEncode row, ())).toList.getLast? = some '\n' := by
  show (Grammar.print rowTupleGrammar (rowEncode row) ++ "\n").toList.getLast? = some '\n'
  rw [String.toList_append, TextKit.lit_nl, List.getLast?_append]
  simp

private theorem getLast?_append_right (a b : List Char) (hb : b ≠ []) :
    (a ++ b).getLast? = b.getLast? := by
  rw [List.getLast?_append]
  cases hb2 : b.getLast? with
  | none => exact absurd hb2 (by simp [hb])
  | some l => simp

/-- The derived print is LF-terminated (the last byte of a nonempty
    ledger's print — the parse wrapper's no-append branch on the
    canonical bytes). -/
private theorem print_last_newline : ∀ (ledger : List LedgerRow), ledger ≠ [] →
    (print ledger).toList.getLast? = some '\n' := by
  intro ledger
  induction ledger with
  | nil => intro h; exact absurd rfl h
  | cons row rest ih =>
      intro hne
      rw [print_cons, String.toList_append]
      cases rest with
      | nil =>
          rw [print_nil, show ("".toList) = ([] : List Char) from rfl,
            List.append_nil]
          exact linePrint_last_newline row
      | cons r2 rs =>
          have hrest : (r2 :: rs) ≠ [] := by simp
          have hne2 : (print (r2 :: rs)).toList ≠ [] := by
            have h3 := ih hrest
            intro h0; rw [h0] at h3; simp at h3
          rw [getLast?_append_right _ _ hne2]
          exact ih hrest

/-! ### the round trip — the file format's law, the generic instances -/

/-- The line-level climb inverts the spell (the spellability premise
    rides to the row face). -/
private theorem toLine_rowEncode (row : LedgerRow) (hs : rowSpellable row) :
    toLine (rowEncode row, ()) = row := by
  show toRow (rowEncode row) = row
  exact toRow_rowEncode row hs

/-- The climb over the spell's image is the ledger (the spellability
    premise, per row). -/
private theorem map_climb (ledger : List LedgerRow)
    (hspell : ∀ row ∈ ledger, rowSpellable row) :
    (ledger.map (fun row => (rowEncode row, ()))).map toLine = ledger := by
  induction ledger with
  | nil => rfl
  | cons row rest ih =>
      show toLine (rowEncode row, ()) ::
        (rest.map (fun row => (rowEncode row, ()))).map toLine = row :: rest
      have hs' : ∀ r ∈ rest, rowSpellable r :=
        fun r hr => hspell r (List.Mem.tail _ hr)
      rw [toLine_rowEncode row (hspell row (List.Mem.head _)), ih hs']

/-- THE FILE-FORMAT LAW (the grammar layer's instance, 05 §1): a
    well-formed ledger of `rowOk`/spellable rows prints to its
    canonical text and parses back to EXACTLY itself. The hand-proved
    family the pre-grammar file promised (the row law, the
    line-structure fold — the old `splitOn` machinery core never had)
    is `Grammar.run_print_fixFree`'s content; the wrapper's newline
    discipline + the wf gate + the spellability premise are the
    format-local remainder. -/
theorem parse_print (ledger : List LedgerRow) (hwf : wf ledger = true)
    (hok : ∀ row ∈ ledger, rowOk row = true)
    (hspell : ∀ row ∈ ledger, rowSpellable row) :
    parse (print ledger) = .ok ledger := by
  simp only [parse]
  have hcond : ((print ledger == "" ||
      (print ledger).toList.getLast? == some '\n') = true) := by
    cases ledger with
    | nil => rw [print_nil]; simp
    | cons row rest =>
        have hne : ((row :: rest) : List LedgerRow) ≠ [] := by simp
        simp [print_last_newline (row :: rest) hne]
  rw [if_pos hcond]
  have hrun : Grammar.run ledgerGrammar (print ledger)
      = .ok (ledger.map (fun row => (rowEncode row, ()))) :=
    Grammar.run_print_fixFree ledgerGrammar ledgerFixFree ledgerCert _
      (valueOk_ledger ledger hok)
  simp only [hrun]
  rw [map_climb ledger hspell, if_pos hwf]

/-- Law 2 (the exactness direction) at the ledger's grammar (the raw
    face): a successful derived parse consumed EXACTLY the print of its
    result (+ the parsed value is value-owned — the fields'
    discipline). -/
theorem print_parse_raw (fuel : Nat) (ys : List (RowTuple × Unit))
    (cur cur' : Cursor)
    (h : Grammar.parseG ledgerGrammar fuel cur = .ok (ys, cur')) :
    cur.cs = (Grammar.print ledgerGrammar ys).toList ++ cur'.cs ∧
    cur'.off = cur.off + (Grammar.print ledgerGrammar ys).length ∧
    Grammar.valueOk ledgerGrammar ys = true :=
  Grammar.print_parse ledgerGrammar fuel ledgerCoherent h

/-- THE SNAPSHOT DISCIPLINE: the committed bytes ARE the canonical
    print — a hand-edited ledger fails its own stability check (the
    bytes no longer re-derive from the parse, or the parse refuses).
    The one-writer rule's detection face for the ledger file itself. -/
def selfStable (s : String) : Bool :=
  match parse s with
  | .ok ledger => print ledger == s
  | .error _ => false

/-- THE ROUND-TRIP LAW's registration (proved at the law's defining
    face): `selfStable` IS the parse∘print discipline — the parse
    decides, the canonical re-print decides the bytes. An edit that
    decouples the stability check from the parse or the print fails
    this `rfl`. The FULL inversion is `parse_print` above — the
    generic theorem's instance. -/
theorem parse_print_selfStable (s : String) :
    selfStable s =
      match parse s with
      | .ok ledger => print ledger == s
      | .error _ => false :=
  rfl

end Kit.Ledger

end -- public section

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
by path, LF endings, no blank lines. Parse and print are total
(TextKit's scanners + `String.splitOn` — never hand-rolled char
plumbing); parse REFUSES unsorted/duplicate/malformed rows, and
`selfStable` is the snapshot discipline: the committed bytes must be
exactly the canonical print (a hand-edited ledger fails its own
stability check).

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
  theorems are one-`simp` inductions off `List.mem_filter`.
- gate row: none yet — `checkHeader` is the pure face; the gate row
  lands with the committed ledger file (the named follow-up).
-/

import Lean
import TextKit.Basic
import Kit.Diag
import Kit.CodeRegistry

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

/-! ## the file format — print/parse, both total -/

/-- A ledger field's charset: anything but the separators (tab, LF, CR).
    The ONE separator-charset def — CodeRegistry's `rowNameChar` (same
    body, same intent: a persisted-text field is separator-free); the
    lint's dedup preference honored by consumption, not a twin. -/
def fieldChar (c : Char) : Bool := CodeRegistry.rowNameChar c

/-- A dotted name's spelling back to a `Name` (`a.b` — the fold of the
    dot-split components; the mirror of `toString`). -/
def namesOf (s : String) : Name :=
  (s.splitOn ".").foldl Name.mkStr Name.anonymous

/-- The comma-joined name list (the list fields' face; empty = empty). -/
def namesCsv (ns : List Name) : String :=
  String.intercalate "," (ns.map toString)

/-- The comma-joined string list. -/
def strsCsv (xs : List String) : String :=
  String.intercalate "," xs

/-- One name-CSV field's parse: comma-split, no empty entries, charset
    checked. Total; `none` = malformed. -/
def parseNames (s : String) : Option (List Name) :=
  if s == "" then some []
  else
    let comps := s.splitOn ","
    if comps.any (fun c => c == "" || !(c.all fieldChar)) then none
    else some (comps.map namesOf)

/-- One string-CSV field's parse (the obligations; entries checked). -/
def parseStrs (s : String) : Option (List String) :=
  if s == "" then some []
  else
    let comps := s.splitOn ","
    if comps.any (fun c => c == "" || !(c.all fieldChar)) then none
    else some comps

/-- A bare field's check: nonempty + separator-free. -/
def okField (s : String) : Bool := s != "" && s.all fieldChar

/-- The hash field's parse: TextKit's `scanNat`, fully consumed. -/
def parseHash (s : String) : Option UInt64 :=
  match TextKit.scanNat s.toList with
  | some (n, []) => some (UInt64.ofNat n)
  | _ => none

/-- Render one row: the seven tab-separated fields. -/
def renderRow (a : LedgerRow) : String :=
  a.path ++ "\t" ++ a.emitter ++ "\t" ++ namesCsv a.demand.rows ++ "\t"
    ++ namesCsv a.demand.collections ++ "\t" ++ a.demand.emitterRev ++ "\t"
    ++ toString a.contentHash ++ "\t" ++ strsCsv a.obligations

/-- Print the ledger: one row per line, LF-terminated (the committed
    file's canonical bytes; the caller owns the sort — `canonicalize`
    in Kit.Emit's writer). -/
def print (ledger : List LedgerRow) : String :=
  ledger.foldl (fun acc a => acc ++ renderRow a ++ "\n") ""

/-- Parse one line: the seven fields, each checked. Total; `none` =
    malformed. -/
def parseRow (line : String) : Option LedgerRow :=
  match line.splitOn "\t" with
  | [path, emitter, rowsS, colsS, revS, hashS, oblS] => do
      if !(okField path && okField emitter && okField revS) then none
      else
        let rows ← parseNames rowsS
        let cols ← parseNames colsS
        let hash ← parseHash hashS
        let obl ← parseStrs oblS
        pure { path := path, emitter := emitter
             , demand := { rows := rows, collections := cols
                         , emitterRev := revS }
             , contentHash := hash, obligations := obl : LedgerRow }
  | _ => none

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

/-- Parse the file: one row per line, LF endings, no blank lines; the
    final newline's empty tail is the file's, not a row's. The result
    must satisfy `wf` — an unsorted or duplicate-pathed ledger is a
    REFUSAL, never a silent accept. Total over String.

    The refusals ride the ONE diagnostic envelope (05 §4): the failure
    kind is the registry's KL row (`notes/code-registry.txt`), the
    rendering is the envelope's one-line face — the parse refusals are
    positional/structural (no single `got` to enumerate a valid space
    over), so the literal Diag is the honest shape there. -/
def parse (s : String) : Except String (List LedgerRow) :=
  let ls := s.splitOn "\n"
  let ls := if ls.getLast? == some "" then ls.take (ls.length - 1) else ls
  match ls.foldl (fun (acc : Except String (List LedgerRow)) (line : String) =>
      match acc with
      | .error e => .error e
      | .ok rows =>
          match parseRow line with
          | some row => .ok (row :: rows)
          | none => .error (ledgerDiag eKL0007 "malformed row — expected \
`path<TAB>emitter<TAB>rows<TAB>collections<TAB>emitterRev<TAB>hash<TAB>obligations` \
(list fields comma-joined; no blank lines)"))
      (.ok []) with
  | .error e => .error e
  | .ok revRows =>
      let ledger := revRows.reverse
      if wf ledger then .ok ledger
      else .error (ledgerDiag eKL0008 "ill-formed ledger — paths must be \
unique and rows sorted by path")

/-- THE SNAPSHOT DISCIPLINE: the committed bytes ARE the canonical
    print — a hand-edited ledger fails its own stability check (the
    bytes no longer re-derive from the parse, or the parse refuses).
    The one-writer rule's detection face for the ledger file itself. -/
def selfStable (s : String) : Bool :=
  match parse s with
  | .ok ledger => print ledger == s
  | .error _ => false

/-- THE ROUND-TRIP LAW (the parse/print correspondence's registration,
    proved at the law's defining face): `selfStable` IS the parse∘print
    discipline — the parse decides, the canonical re-print decides the
    bytes. An edit that decouples the stability check from the parse or
    the print fails this `rfl`. The full inversion
    (`parse (print ledger) = .ok ledger` at the wf face) lands with its
    `String.splitOn` machinery (core has none — the row face is the
    tests' pinned face for now). -/
theorem parse_print_selfStable (s : String) :
    selfStable s =
      match parse s with
      | .ok ledger => print ledger == s
      | .error _ => false :=
  rfl

end Kit.Ledger

/-
# Inspector.LedgerView — the provenance ledger's queries, rendered

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: notes/v3/09-gates-ops.md §4 (the provenance ledger —
the inspector READS it, never re-derives it; the two query directions —
BACKWARD "what made this?" and FORWARD "what moves if I change this?";
"a generated file without a ledger row is a review failure"); the
demand-set correction as data (Kit.Ledger's `DemandSet` — the rows face
PLUS the collection-enumeration face PLUS the emitter revision; the
conservatism is PROVED there: `forward` never under-reports).

The ledger file itself does not exist yet (Kit.Ledger's header: it
lands with the first driver wiring — the byte-tie wave). The report is
HONEST about that: the absent file renders the DORMANT state, never a
fabricated green, and the emitter-declared side of the orphan check is
named as Gates.Ownership's row (the two faces, kept distinct).

The on-disk artifact scan is MIRRORED from Gates.Ownership (scanRoots +
the explicit-stack walk), not imported: the inspector stays a leaf so
the gates can consume its sweep without a cycle (Inspector.Replay's
header note). One writer per artifact path: when the gates consume the
inspector, the mirror swaps to the shared surface.

The five questions (notes/v3/01-core.md):
- root: none — the ledger reading's rendering face over Kit.Ledger's
  data (09 §4's provenance stage).
- carrier grade: none of its own — the conservatism is Kit.Ledger's
  (proved); this module renders, never re-derives.
- spine reading: the artifact stage's provenance face, read-side.
- ladder rung: rung 1 — total folds over parsed rows.
- gate row: none — the report FLAGs orphans (the review failure's loud
  marker) and exits nonzero on them, but the ownership gate owns the
  emitter-declared teeth; the inspector covers the LEDGER side.
-/

import Kit.Ledger

namespace Inspector.LedgerView

open Kit.Ledger

/-! ## The host face (the committed file + the mirrored artifact scan) -/

/-- The committed ledger file's path (Kit.Ledger's named shape; the
    ONE writer is Kit.Emit's driver layer — this module only reads). -/
def ledgerPath : System.FilePath := "notes/artifact-ledger.tsv"

/-- One generated-artifact scan root (MIRRORED from Gates.Ownership —
    see the header; a directory + a required extension, `""` = all). -/
structure ScanRoot where
  dir : String
  ext : String

/-- The scan roots, mirrored verbatim from Gates.Ownership's (the
    tree's layout: all of `gen/` + the generated crate's Rust dirs). -/
def scanRoots : List ScanRoot :=
  [ { dir := "gen", ext := "" }
  , { dir := "crates/schema-generated/src", ext := "rs" }
  , { dir := "crates/schema-generated/tests", ext := "rs" } ]

/-- The recursive directory walk, as an explicit worklist loop (the
    noNewPartial rule — structurally terminating on the stack's own
    consumption). MIRRORED from Gates.Ownership.walk. -/
def walk (root : System.FilePath) : IO (List String) := do
  let mut acc : List String := []
  let mut stack : List System.FilePath := [root]
  repeat
    match stack with
    | [] => break
    | dir :: rest =>
      stack := rest
      unless ← dir.pathExists do continue
      let entries ← dir.readDir
      for e in entries do
        if ← e.path.isDir then
          stack := e.path :: stack
        else
          acc := e.path.toString :: acc
  pure acc.reverse

/-- The on-disk artifact set: every scan root's files (extension-
    filtered), sorted for a deterministic report. -/
def scanGenerated : IO (List String) := do
  let mut out : List String := []
  for r in scanRoots do
    let all ← walk r.dir
    out := out ++ (if r.ext.isEmpty then all
                   else all.filter (·.endsWith ("." ++ r.ext)))
  pure (out.toArray.qsort (fun a b => a <= b) |>.toList)

/-- The committed ledger's state at read time: ABSENT (the honest
    dormant state — the file lands with the first driver wiring), the
    parse REFUSAL (Kit.Ledger's one-envelope diagnostic), or LOADED. -/
inductive LedgerState where
  | absent
  | refused (err : String)
  | loaded (rows : List LedgerRow)

/-- Read + parse the committed ledger file. A read error other than
    absence is also a REFUSAL (the loud state, never a silent empty). -/
def readLedger : IO LedgerState := do
  unless ← ledgerPath.pathExists do return .absent
  match ← IO.FS.readFile ledgerPath with
  | s => match Kit.Ledger.parse s with
    | .ok rows => return .loaded rows
    | .error e => return .refused e

/-! ## The pure renders (the tests' pins; no IO past this line) -/

/-- String-list dedup, order-preserving (the forward table's name
    universe). -/
def dedupStr : List String → List String
  | [] => []
  | x :: xs => if xs.contains x then dedupStr xs else x :: dedupStr xs

/-- One artifact's backward line: the demand's full spec surface (rows
    PLUS collections — the rows-only shape is the pre-correction query
    the doctrine rejects). -/
def renderBackwardLine (a : LedgerRow) : String :=
  s!"  {a.path} ← {a.emitter} (rev {a.demand.emitterRev}, hash {a.contentHash})\n" ++
  s!"    spec rows: {if a.demand.rows.isEmpty then "(none)" else Kit.Ledger.namesCsv a.demand.rows}\n" ++
  s!"    collections: {if a.demand.collections.isEmpty then "(none)" else Kit.Ledger.namesCsv a.demand.collections}\n" ++
  s!"    obligations: {if a.obligations.isEmpty then "(none)" else Kit.Ledger.strsCsv a.obligations}"

/-- The BACKWARD table: every ledger row's demand surface ("what made
    this?"). Empty ledger → the honest no-rows line. -/
def backwardTable (rows : List LedgerRow) : String :=
  if rows.isEmpty then "backward: no ledger rows\n"
  else "backward (artifact → its demand surface):\n" ++
    String.intercalate "" (rows.map renderBackwardLine)

/-- The FORWARD table: every demanded name (row or collection) → the
    affected artifacts. `forward r [r]` — the changed name is either
    the row itself or a collection whose contents changed; the query is
    CONSERVATIVE (Kit.Ledger's proved face: it may over-report on the
    collection face, never under). -/
def forwardTable (rows : List LedgerRow) : String :=
  let names := dedupStr
    (rows.flatMap fun a => (a.demand.rows.map toString) ++ (a.demand.collections.map toString))
  if names.isEmpty then "forward: no demanded names\n"
  else "forward (spec name → affected artifacts):\n" ++
    String.intercalate "\n" (names.map fun n =>
      let affected := (Kit.Ledger.forward n.toName [n.toName] rows).map (·.path)
      s!"  {n} → {if affected.isEmpty then "(nothing)" else String.intercalate ", " affected}")

/-- The ORPHANS: on-disk generated files with NO ledger row — the
    review failure's ledger-side face (Kit.Ledger.withoutRow, consumed).
    The emitter-declared side is the ownership gate's row. -/
def orphans (rows : List LedgerRow) (onDisk : List String) : List String :=
  Kit.Ledger.withoutRow rows onDisk

/-- One artifact-path's backward answer: (rendered, tracked). An
    untracked path is the LOUD miss (exit 1 at the exe's face), and the
    miss lists the tracked paths — the did-you-mean discipline. -/
def backwardAnswer (rows : List LedgerRow) (path : String) : String × Bool :=
  match rows.find? (fun a => a.path == path) with
  | some a => (renderBackwardLine a, true)
  | none =>
      (s!"inspector: NO ledger row for `{path}` — untracked by the ledger\n"
        ++ "  tracked artifact paths:\n"
        ++ String.intercalate "\n" (rows.map (fun a => s!"    - {a.path}")) ++ "\n"
        ++ "  (a GENERATED file with no row is a review failure — 09 §4)",
      false)

/-- One spec name's forward answer ("what moves if I change this?"). A
    name affecting nothing is a legitimate answer (exit 0) — the
    conservative query already ran; over-reporting is its honest face. -/
def forwardAnswer (rows : List LedgerRow) (name : String) : String :=
  let affected := (Kit.Ledger.forward name.toName [name.toName] rows).map (·.path)
  s!"forward `{name}` → {if affected.isEmpty then "(nothing)"
    else String.intercalate ", " affected}\n" ++
  "  (conservative: an artifact that merely ENUMERATED a collection of \
    this name is included — the demand-set correction's proved face)"

/-- THE LEDGER REPORT: the committed file's state, the two query
    directions, and the orphans. The ABSENT state renders DORMANT —
    the ledger side's orphan check has no rows to compare, and the
    report says so instead of a fabricated clean. (rendered, failed?). -/
def report (onDisk : List String) (st : LedgerState) : String × Bool :=
  match st with
  | .absent =>
      (s!"provenance ledger — {ledgerPath}\n" ++
        "  STATE: ABSENT — the committed ledger does not exist yet (it lands \
          with the first driver wiring, the byte-tie wave).\n" ++
        s!"  The ledger-side queries are DORMANT, not green: no row backs any \
          artifact, and no orphan verdict is issued (there is nothing to \
          compare {onDisk.length} on-disk artifact(s) against).\n" ++
        "  The orphan check's EMITTER-DECLARED side is the ownership gate's row \
          (gates ownership) — the two faces, both honest.",
      false)
  | .refused e =>
      (s!"provenance ledger — {ledgerPath}\n  REFUSED: {e}\n" ++
        "  (the ledger's own parse discipline fired — a hand-edited or \
          malformed ledger fails its stability check)",
      true)
  | .loaded rows =>
      let orph := orphans rows onDisk
      (s!"provenance ledger — {ledgerPath}\n" ++
        s!"  {rows.length} ledger row(s), {onDisk.length} on-disk artifact(s) \
          under the scan roots\n" ++
        backwardTable rows ++ forwardTable rows ++
        (if orph.isEmpty then
            "orphans: none — every on-disk generated artifact has its ledger row\n"
          else
            "orphans: FLAGGED — on-disk generated artifacts with NO ledger row \
              (a review failure, 09 §4):\n" ++
            String.intercalate "\n" (orph.map (fun p => s!"  ORPHAN {p}")) ++ "\n") ++
        "  the ledger is READ here (one writer: the emit spine's driver layer); \
          the emitter-declared orphan face is the ownership gate's row",
      !orph.isEmpty)

end Inspector.LedgerView

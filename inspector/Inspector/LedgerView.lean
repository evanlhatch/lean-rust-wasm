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

The on-disk artifact scan is Inspector.ArtifactScan's (the shared leaf
the ownership gate consumes too — the anti-cycle mirror is retired:
gates→inspector is the sanctioned direction, and the mirror's cost
already arrived, its scanRoots list missing the faults lane's row).

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
import Kit.ListExtras
import Inspector.ArtifactScan
import Inspector.Tables

namespace Inspector.LedgerView

open Kit.Ledger
open SchemaCore (Field RowVals)
open Inspector.Tables (ledgerFields ledgerRowOf ledgerRowsOf selectRows projectRows
  readStr readU64 qLedgerAll qLedgerDemands)

/-! ## The host face (the committed file + the shared artifact scan) -/

/-- The committed ledger file's path (Kit.Ledger's named shape; the
    ONE writer is Kit.Emit's driver layer — this module only reads). -/
def ledgerPath : System.FilePath := "notes/artifact-ledger.tsv"

/-- The on-disk artifact set — Inspector.ArtifactScan's (the ONE
    enumeration; the ownership gate rides the same surface). -/
def scanGenerated : IO (List String) := Inspector.ArtifactScan.scanGenerated

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
    universe) — Kit.ListExtras.dedup's String face (the ONE dedup). -/
def dedupStr : List String → List String := Kit.ListExtras.dedup

/-- One artifact's backward line: the demand's full spec surface (rows
    PLUS collections — the rows-only shape is the pre-correction query
    the doctrine rejects). -/
def renderBackwardLine (a : LedgerRow) : String :=
  s!"  {a.path} ← {a.emitter} (rev {a.demand.emitterRev}, hash {a.contentHash})\n" ++
  s!"    spec rows: {if a.demand.rows.isEmpty then "(none)" else Kit.Ledger.namesCsv a.demand.rows}\n" ++
  s!"    collections: {if a.demand.collections.isEmpty then "(none)" else Kit.Ledger.namesCsv a.demand.collections}\n" ++
  s!"    obligations: {if a.obligations.isEmpty then "(none)" else Kit.Ledger.strsCsv a.obligations}"

/-- THE RENDER FACE over the table row: the qlang! scan's result rows
    → the SAME bytes. The list columns are the ledger file's own csv
    spellings (`namesCsv`/`strsCsv` — the persisted format's list
    faces), so the line is byte-identical to `renderBackwardLine`'s
    (the tests pin the equality, row by row). -/
def renderBackwardRowT (row : RowVals ledgerFields) : String :=
  s!"  {readStr row "path"} ← {readStr row "emitter"} (rev {readStr row "emitterRev"}, hash {readU64 row "hash"})\n" ++
  s!"    spec rows: {if readStr row "specRows" == "" then "(none)" else readStr row "specRows"}\n" ++
  s!"    collections: {if readStr row "collections" == "" then "(none)" else readStr row "collections"}\n" ++
  s!"    obligations: {if readStr row "obligations" == "" then "(none)" else readStr row "obligations"}"

/-- The BACKWARD table: every ledger row's demand surface ("what made
    this?") — THE MIGRATED SHAPE (C5): the qlang! scan `qLedgerAll`
    decides the table face; the render walks the table's order
    (`selectRows` — the engine's answer is a canonical set, the render
    keeps the table's order), so the bytes are the hand fold's. Empty
    ledger → the honest no-rows line. -/
def backwardTable (rows : List LedgerRow) : String :=
  let trows := selectRows qLedgerAll (ledgerRowsOf rows)
  if trows.isEmpty then "backward: no ledger rows\n"
  else "backward (artifact → its demand surface):\n" ++
    String.intercalate "" (trows.map renderBackwardRowT)

/-- The csv field's members (the EMPTY field is NO members — the
    ledger file's own list spelling; `splitOn` on the empty field would invent
    one empty member). -/
def csvMembers (s : String) : List String :=
  s.splitOn "," |>.filter (· != "")

/-- The FORWARD table: every demanded name (row or collection) → the
    affected artifacts. THE MIGRATED SHAPE (C5): the name universe is
    the qlang! PROJECTION `qLedgerDemands` (the demand columns, the
    drop projection's order-preserving narrowing), read back through
    the csv spellings; the affected filter stays `Kit.Ledger.forward`
    — the proved conservatism is consumed, never re-derived (a
    csv-membership predicate over a RUNTIME name is outside the
    qlang! fragment — the named friction). The universe's order is the
    engine's canonical order (sorted) — no pin distinguishes it.
    `forward r [r]` — the changed name is either the row itself or a
    collection whose contents changed; the query is CONSERVATIVE
    (Kit.Ledger's proved face: it may over-report on the collection
    face, never under). -/
def forwardTable (rows : List LedgerRow) : String :=
  let names := dedupStr
    ((projectRows qLedgerDemands (ledgerRowsOf rows)).flatMap fun r =>
      csvMembers (readStr r "specRows") ++ csvMembers (readStr r "collections"))
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

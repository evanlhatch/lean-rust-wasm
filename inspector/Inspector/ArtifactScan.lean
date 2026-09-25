/-
Inspector.ArtifactScan — the on-disk generated-artifact scan, ONE copy

Formerly a MIRROR (Inspector.LedgerView's copy of Gates.Ownership's
scan — the anti-cycle mirror while the inspector stayed a leaf). The
gates consume the inspector now (Gates.Impact's import — the sanctioned
direction; the Replay header's note), so the mirror's reason is gone
and its cost arrived on schedule: the two `scanRoots` tables had ALREADY
drifted (the ownership gate's `crates/mandate-faults` row was missing
from the ledger face's list — exactly the silent divergence a mirror
promises to prevent). This module is the shared leaf both faces
consume; the gate's STRICTER table (4 rows) is the one that survived —
the ledger-side orphan check gets the faults lane back into its
universe (a fix, not a behavior regression: the ledger is dormant
today — absent file renders the honest ABSENT state).

The five questions (notes/v3/01-core.md):
- root: none — the artifact surface's on-disk enumeration.
- carrier grade: none — FS machinery over committed bytes.
- spine reading: the artifact stage's on-disk face, read-side.
- ladder rung: n/a (host machinery).
- gate row: the ownership gate's on-disk set + the ledger report's
  artifact count ride THIS enumeration (never a second walk).
-/

namespace Inspector.ArtifactScan

/-- One generated-artifact scan root: a directory (relative to the
    repo root) + a required extension (`""` = every file under it). -/
structure ScanRoot where
  dir : String
  ext : String

/-- The scan roots (the tree's layout): the whole `gen/` directory +
    the generated crate's Rust dirs. A committed-or-not file under a
    root is artifact surface either way (the disk is stricter than
    the VCS — it catches the uncommitted squatter before the commit). -/
def scanRoots : List ScanRoot :=
  [ { dir := "gen", ext := "" }
  , { dir := "crates/schema-generated/src", ext := "rs" }
  , { dir := "crates/schema-generated/tests", ext := "rs" }
  , { dir := "crates/mandate-faults/src", ext := "rs" } ]

/-- The recursive directory walk, as an explicit worklist loop (the
    linter's noNewPartial rule: no new `partial` — the file-system
    tree is walked by an explicit stack, structurally on the stack's
    own consumption). Absent roots sweep empty. -/
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

/-- The files a root sweeps (the extension filter applied). -/
def rootFiles (r : ScanRoot) : IO (List String) := do
  let all ← walk r.dir
  pure (if r.ext.isEmpty then all
        else all.filter (·.endsWith ("." ++ r.ext)))

/-- The on-disk artifact set: every scan root's files (extension-
    filtered), sorted for a deterministic report. -/
def scanGenerated : IO (List String) := do
  let mut out : List String := []
  for r in scanRoots do
    let all ← rootFiles r
    out := out ++ all
  pure (out.toArray.qsort (fun a b => a <= b) |>.toList)

end Inspector.ArtifactScan

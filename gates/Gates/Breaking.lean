/-
Gates.Breaking — the breaking gate (`gates breaking`; notes/v3/
03-bidirectional.md §7 + §2, notes/v3/09-gates-ops.md §3, decisions.md
D13's rename honesty).

The committed `notes/universe.snapshot` is the spec of record for the
registry's content (SnapshotCheck's substrate); this gate is its
FORWARD consumer:

1. THE BASELINE — the committed snapshot file, parsed with the ONE
   parser (`SchemaCore.parse`); an absent or corrupt baseline is a loud
   refusal (exit 1), never a silent zero (an empty old universe would
   read as all-additions — the dishonest clean).
2. THE CURRENT — the replayed registry (the integral of the event log,
   15 #7) through the ONE reader (`registryOfItems ∘ schemaExt.getState`
   — the same replay gen-check runs).
3. THE DIFF + VERDICT — `SchemaCore.diff` (the net change over the name
   key) + `SchemaCore.verdictOf` over the remedy registry below. The
   change list prints as data; a delete+add pair with agreeing field
   contents is flagged as a POSSIBLE rename (D13: names are
   presentation — reported, NEVER silently merged; the stable-id lane
   is the named follow-up).
4. THE EXIT-CODE DISCIPLINE (the ONLY mapping —
   `CompatVerdict.exitCode`): clean → 0; remedied → 0 WITH the remedy
   evidence named in the report (shippable; apply the migration, then
   re-baseline); unremedied → 2 — the LOUD warning (`just gates` fails
   on 2).

The remedy registry (`registeredMigrations`): EMPTY until the first
real breaking change lands with its soundness theorem (the legacy
discipline — the exemplar `SchemaCore.widenBounded` + `widenBounded_sound`
ships with the type in SchemaCore.Diff). The remedied face is exercised
in SchemaTests; a migration registers HERE with its proof.

The five questions (notes/v3/01-core.md):
- root: Change — the net change between the committed snapshot and the
  replayed registry, decided.
- carrier grade: the verdict over data (the exit code is the decision's
  only encoded face; the report carries the evidence).
- spine reading: the artifact stage's forward check (baseline → verdict).
- ladder rung: n/a — the teeth are the exit codes.
- gate row: the breaking row itself (the registry's LAST row — appended,
  after its substrate snapshot-check's row).
-/
import Lean
import Gates.Packages
import Gates.Common
import Gates.SnapshotCheck
import SchemaCore

open SchemaCore

namespace Gates.Breaking

/-- The committed baseline (the exe runs from the repo root). ONE copy —
    the path is SnapshotCheck's (the substrate's owner); this gate consumes
    the named constant, never a second literal (the dupDefBodies rule). -/
def snapshotPath : System.FilePath := Gates.SnapshotCheck.snapshotPath

/-- The remedy registry: a migration lands here WITH its soundness
    theorem (the exemplar lives in SchemaCore.Diff; the authoring
    surface is the named follow-up). Empty is honest: no remedy, no
    remedied verdict. -/
def registeredMigrations : List SchemaCore.Migration := []

/-- `gates breaking` — the diff + verdict + the exit-code discipline. -/
unsafe def run : IO UInt32 := do
  let pkg : PkgSpec := { dir := "SchemaCore", srcDir := "schemacore", roots := #[`SchemaCore.Slice] }
  Gates.withPkgEnv "breaking" pkg fun env => do
    -- 1. the baseline: the committed snapshot, through the ONE parser
    unless ← snapshotPath.pathExists do
      IO.eprintln s!"breaking: FAIL — no baseline at {snapshotPath}; \
commit one via `lake exe gates snapshot-check --write` (an absent \
baseline is NEVER the empty universe — that would read as all-additions)"
      return 1
    let committed ← IO.FS.readFile snapshotPath
    let baseline ←
      match SchemaCore.parse committed with
      | .error e => do
        IO.eprintln s!"breaking: FAIL — baseline {snapshotPath} is corrupt: {e}"
        return 1
      | .ok items => pure items
    -- 2. the current: the replayed registry, through the ONE reader
    let current ←
      match registryOfItems (schemaExt.getState env) with
      | .error e => do
        IO.eprintln s!"breaking: FAIL — the replayed registry refused: {e}"
        return 1
      | .ok reg => pure reg.items
    -- 3. the diff + the verdict
    let changes := SchemaCore.diff baseline current
    let verdict := SchemaCore.verdictOf changes registeredMigrations
    let breaking := SchemaCore.breakingOf changes
    let renames := SchemaCore.renameCandidates baseline current
    for c in changes do
      IO.println s!"  {c}"
    for (o, n) in renames do
      IO.println s!"  possible rename: {o} → {n} (field contents agree; \
reported, NEVER silently merged — D13: the stable-id lane is the follow-up)"
    -- 4. the exit-code discipline (CompatVerdict.exitCode — the only mapping)
    match verdict with
    | .clean =>
        IO.println s!"breaking: clean ({changes.length} safe change(s), \
{current.length} item(s)) — the compatibility relation holds"
        return verdict.exitCode
    | .remedied =>
        IO.println s!"breaking: REMEDIED — {breaking.length} breaking \
change(s) vs {snapshotPath}, all with sound remedy evidence:"
        for c in breaking do
          IO.println s!"  {c}"
        IO.println "action required: apply the migration(s) to the event \
log, then re-baseline (`lake exe gates snapshot-check --write`)"
        return verdict.exitCode
    | .unremedied =>
        IO.eprintln s!"breaking: FAIL — {breaking.length} unremedied \
breaking change(s) vs {snapshotPath}:"
        for c in breaking do
          IO.eprintln s!"  {c}"
        return verdict.exitCode

end Gates.Breaking

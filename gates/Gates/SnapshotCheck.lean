/-
Gates.SnapshotCheck — the universe-snapshot gate
(`gates snapshot-check [--write]`; notes/v3/09-gates-ops.md §2-3 +
notes/v3/03-bidirectional.md §7 + notes/v3/13-interfaces.md's "the
universe snapshot" row).

The committed `notes/universe.snapshot` is the SPEC OF RECORD for the
registry's content — the substrate the breaking gate diffs against (the
forward consumer). The gate:

1. REPLAY — the registration module's olean with extensions loaded
   (the SAME replay gen-check runs; the registry = the integral of the
   event log, 15 #7). The load prelude is `Gates.withPkgEnv`'s.
2. RENDER — `SchemaCore.snapshotOfEnv`: the replayed registry through
   the ONE writer (`Snapshot.print`, canonical: sorted, one line per
   item). A name that fails the write-side gate (`nameOk`) is a loud
   refusal — parse failures are always corruption, never writer drift.
3. THE TIE — the committed file vs the fresh canonical bytes,
   byte-exact (a data file: NO GENERATED header, so NO stripping — the
   canonical bytes ARE the file; the code-registry-check precedent).
   ONE tie per artifact: the snapshot is never also gen-check's.
   The tie tail is `Driver.byteTieGate`'s core.
4. THE TEETH — a hand-edited or corrupt committed file fails the byte
   tie; the gate ALSO parses the committed file first, so a tampered
   file is refused with the parser's diagnostic (the parse tooth), and
   a parsed-but-drifted file fails the byte tie (the drift tooth). The
   parse tooth is this gate's extra tooth and stays here — it does not
   fit the shared core (neither does the absent-file bootstrap).

`--write` is the deliberate re-baseline: it writes the fresh canonical
bytes (commit-visible; never a launder — the fresh render is the ONE
writer's output, there is no committed data being laundered).

The five questions (notes/v3/01-core.md):
- root: Universe — the replayed registry's content as the committed
  baseline (the snapshot = the integral, 15 #7).
- carrier grade: the byte tie + the PROVED round-trip law
  (`SchemaCore.Snapshot.parse_print`) — the gate's bytes are the
  canonical form of a replayed universe.
- spine reading: the artifact stage's check face over the ONE writer.
- ladder rung: n/a — the tie is the teeth.
- gate row: the snapshot-check row itself.
-/
import Lean
import Gates.Packages
import Gates.Common
import SchemaCore

open SchemaCore

namespace Gates.SnapshotCheck

/-- The committed baseline (the exe runs from the repo root). -/
def snapshotPath : System.FilePath := "notes/universe.snapshot"

/-- `gates snapshot-check [--write]` — exit 1 on any refusal. -/
unsafe def run (write : Bool) : IO UInt32 := do
  let pkg : PkgSpec := { dir := "SchemaCore", srcDir := "schemacore", roots := #[`SchemaCore.Slice] }
  Gates.withPkgEnv "snapshot-check" pkg fun env => do
    let fresh ←
      match SchemaCore.snapshotOfEnv env with
      | .error e => do
        IO.eprintln s!"snapshot-check: RENDER REFUSED — {e}"
        return 1
      | .ok fresh => pure fresh
    unless ← snapshotPath.pathExists do
      if write then
        Kit.Emit.writeFileCreatingDirs snapshotPath fresh
        IO.println s!"wrote {snapshotPath} (bootstrap — the empty universe renders empty)"
        IO.println "snapshot-check: clean — the baseline is the canonical render"
        return 0
      IO.println s!"snapshot-check: {snapshotPath} absent — run \
`lake exe gates snapshot-check --write` and commit"
      return 1
    let committed ← IO.FS.readFile snapshotPath
    -- the parse tooth: a tampered/corrupt file is refused with the
    -- parser's diagnostic, not a bare byte-diff
    match SchemaCore.parse committed with
    | .error e =>
        IO.println s!"snapshot-check: REFUSED — the committed file does not \
parse ({e}) — corruption, never writer drift; repair or re-baseline with \
`lake exe gates snapshot-check --write`"
        return 1
    | .ok parsed =>
        -- the drift tooth: the canonical bytes must tie (the
        -- Driver.byteTieGate core; the parse refusal above is this
        -- gate's extra tooth and stays)
        Driver.byteTieGate committed fresh write
          (Kit.Emit.writeFileCreatingDirs snapshotPath)
          (inSyncWrite := none)
          (driftWriteMsg :=
            s!"wrote {snapshotPath} (re-baselined — a deliberate, commit-visible act)")
          (cleanAfterWrite := false)
          (cleanMsg :=
            "snapshot-check: clean — the committed universe snapshot is the \
canonical render of the replayed registry (byte-tied)")
          (driftMsg :=
            s!"snapshot-check: {snapshotPath} DRIFTED from the fresh canonical \
render of the replayed registry — run \
`lake exe gates snapshot-check --write` and commit (never hand-edit the \
baseline; the parsed file carried {parsed.length} item(s))")

end Gates.SnapshotCheck

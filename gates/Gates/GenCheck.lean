/-
Gates.GenCheck — the byte-tie gate (`gates gen-check`).

The artifact's committed bytes vs a fresh regen — THE stripped compare:
the volatile header lines (the 2-line GENERATED block: clock, spec sha)
are exempt; the artifact BODY must tie byte-exact, and the committed
header's content-hash line must still name the fresh body's hash. The
regen is `SchemaCore.regen` — the SAME semantics the `schema` writer
runs (one copy, never two; a gate that re-encodes the writer would tie
two encodings, not the artifact to the spec).

The teeth: hand-edit the committed artifact → gen-check fails →
`just gen` restores. A gate without teeth is decoration (09).

Provenance: fresh (the gate arrives with its first emitter — the
doctrine's nothing-without-a-consumer rule; the stripped-compare
discipline is Kit.Emit's header + notes/v3/09-gates-ops.md).

The five questions (notes/v3/01-core.md):
- root: Crossing — the artifact's committed bytes vs the fresh reading.
- carrier grade: the tie law (Kit.Golden's stripped-compare shape) —
body byte-equality + the header hash naming the fresh body.
- spine reading: the artifact stage's check face over the ONE regen
(never a second encoding).
- ladder rung: n/a — the gate's teeth are the byte equality.
- gate row: the gen-check row itself (`gates gen-check`).
-/
import Lean
import Gates.Packages
import Gates.Common
import SchemaCore

open Lean

namespace Gates.GenCheck

/-- The byte-tie verdict for one artifact (ctors, never strings). -/
inductive Tie where
  | tied
  | absent
  | drifted (why : String)

/-- The stripped compare for one generated file: the committed file's
    body (the 2 header lines dropped) must be byte-equal to the fresh
    body, and the committed header's content-hash line must name the
    fresh body's hash. -/
def tieOf (committed fresh : String) : Tie :=
  let lines := committed.splitOn "\n"
  match lines[1]? with
  | none => .drifted "committed file has no 2-line GENERATED header"
  | some headerLine =>
    let committedBody := String.intercalate "\n" (lines.drop 2)
    if committedBody != fresh then
      .drifted "artifact body drifted"
    else if !(headerLine.contains (toString fresh.hash)) then
      .drifted "header content hash does not name the fresh body's hash"
    else
      .tied

/-- `gates gen-check` — regen over the replayed registry, compare each
    artifact's committed bytes. Exit 1 on any drift/absence/load
    failure; the clean line names the tied artifact count. -/
unsafe def run : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  -- The registration module's olean carries the `@[schema]` appends;
  -- loadPkgEnv replays the extensions (loadExts := true).
  let pkg : PkgSpec := { dir := "SchemaCore", roots := #[`SchemaCore.Slice] }
  let env ←
    match ← Gates.loadPkgEnv base pkg with
    | .error e => do
      IO.eprintln s!"gen-check: LOAD FAILED — {e}"
      return 1
    | .ok env => pure env
  match SchemaCore.regen env with
  | .error e =>
    IO.eprintln s!"gen-check: REGEN FAILED — {e}"
    return 1
  | .ok r => do
    let mut failed := false
    let mut tied := 0
    for f in r.files do
      let path : System.FilePath := f.path
      unless ← path.pathExists do
        IO.eprintln s!"gen-check: {f.path} ABSENT — run `just gen` and commit"
        failed := true
        continue
      let committed ← IO.FS.readFile path
      match tieOf committed f.contents with
      | .tied => tied := tied + 1
      | .drifted why => do
        IO.eprintln s!"gen-check: {f.path} DRIFTED ({why}) — \
          run `just gen` and commit (never hand-edit a generated file)"
        failed := true
      | .absent => pure ()
    if failed then return 1
    IO.println s!"gen-check: clean — {tied} artifact(s) byte-tied"
    return 0

end Gates.GenCheck

/-
Gates.LegacyHash — the legacy-immutability gate (`gates legacy-hash`;
design-wave-30 B4, the read-only discipline's mechanical tooth).

`legacy/` is the pre-v3 mining source: READ-ONLY reference (the
mandate's hard rule — port content, never migrate in place). Until now
the read-only discipline was prose; this row makes it a HASH: the
gate walks legacy/'s whole file surface, hashes every file's bytes,
and diffs the per-file rows against the committed baseline
`notes/legacy-surface.txt` — a drift (any byte changed, any file added
or removed) is a FINDING, exit 1. The first write is the row's own
baseline (a new row's first-write is not a re-baseline).

The sabotage control (mandatory, 09 §8): the hash's sensitivity pins
live in GatesTests.Main — a content tamper, a path rename, an added
file and a dropped file each MUST change the surface (the mutant
hasher's negative control); the live run fails closed on an ABSENT
legacy tree (a scan that cannot complete is a finding, never silence).

The five questions (notes/v3/01-core.md):
- root: Universe — the committed baseline as the spec of record (the
frozen surface of the read-only tree).
- carrier grade: none — a hash fold, not a crossing.
- spine reading: the artifact stage's check face (committed baseline
vs the fresh walk).
- ladder rung: n/a — the drift equality is the tooth.
- gate row: the legacy-hash row itself (`gates legacy-hash`).
-/
import Gates.Common

namespace Gates.LegacyHash

/-- The read-only surface's root (the exe runs from the repo root). -/
def legacyRoot : System.FilePath := "legacy"

/-- The committed baseline. -/
def baselinePath : System.FilePath := "notes/legacy-surface.txt"

/-- One file's row: `path<TAB>hash` (the per-file row names the drift).
The hash is the BYTES' (`Kit.Emit.bytesHash` — the binary corpus files
under legacy/ are tracked surface too; the hash reads the bytes, never
the UTF-8 decode). -/
def rowOf (path contentHash : String) : String :=
  s!"{path}\t{contentHash}"

/-- The walk's skip list (by base name): `.devenv` is the devenv
shell's scratch dir, `.lake`/`.git` the build + VCS state, and
`node_modules` the docs-site's dependency cache — all UNTRACKED
scratch under legacy/ (symlinked store paths, a volatile sqlite
cache, pack files, the npm cache), not the legacy source surface.
Everything TRACKED under legacy/ is frozen; the skips are named here,
never silent (the CodeRegistryCheck skip-list convention). -/
def skipDirNames : List String := [".devenv", ".lake", ".git",
  "node_modules"]

/-- Fuel-bounded walk over EVERY file under `dir` (all extensions —
the whole surface is frozen). Returns the `(path, content)` rows in
sorted-path order (the deterministic render) + whether the fuel ran
out (exhaustion is a REPORTED finding, never a silent truncation). -/
def walkSurface : Nat → System.FilePath →
    IO (List (String × String) × Bool)
  | 0, _ => return ([], true)
  | fuel + 1, dir => do
    if !(← dir.pathExists) then return ([], false)
    let mut rows : List (String × String) := []
    let mut subdirs : List System.FilePath := []
    let mut exhausted := false
    for e in ← dir.readDir do
      if skipDirNames.contains e.fileName then continue
      if ← e.path.isDir then subdirs := e.path :: subdirs
      else
        let bytes ← IO.FS.readBinFile e.path
        rows := (e.path.toString, toString (Kit.Emit.bytesHash bytes)) :: rows
    for d in subdirs do
      let (rs, ex) ← walkSurface fuel d
      rows := rows ++ rs
      exhausted := exhausted || ex
    return (rows, exhausted)

/-- The fresh surface render: the per-file rows, sorted by path. -/
def renderSurface (rows : List (String × String)) : String :=
  let rs := (rows.map (fun (p, c) => rowOf p c)).toArray.qsort (· <= ·)
  (rs.toList.foldl (· ++ · ++ "\n") "")

/-- `gates legacy-hash [--write]` — exit 1 on any drift/absence. -/
def run (write acceptDrift : Bool) : IO UInt32 := do
  unless ← legacyRoot.pathExists do
    IO.println <| toString (GateDiag eGT0012
      "legacy-hash: the legacy tree is ABSENT — the read-only surface \
      cannot be verified (run from the repo root; fail closed)")
    return 1
  let (rows, exhausted) ← walkSurface 32 legacyRoot
  if exhausted then
    IO.println <| toString (GateDiag eGT0012
      "legacy-hash: WALK FUEL EXHAUSTED — the legacy tree is deeper \
      than the bound; raise the fuel")
    return 1
  let fresh := renderSurface rows
  Driver.reportGate "legacy-hash" baselinePath fresh write acceptDrift false
    s!"legacy-hash: clean — {rows.length} file(s) hashed, the \
      read-only surface frozen"
    (Driver.diffCheck "legacy-hash" "surface"
      "legacy/ drifted — the read-only discipline's hard rule (restore \
      the tree; a re-baseline is the INTEGRATOR's deliberate act)"
      baselinePath fresh)

end Gates.LegacyHash

/-
LintMain — the `lintkit` executable: runs the tree's env-linters over a
package's oleans WITHOUT the package importing LintKit:

    lake exe lintkit [flags] [Module...]

With NO modules the GATED ROOTS are linted (Gates.Packages' set — the
whole tree's own code). `lake build` first: the driver imports oleans,
never builds them.

Usage: `lintkit [--disable=linter.guestlang.x] [--enable=linter.guestlang.x]
         [--extra-prefix=Foo.Bar] Module...`

Exit 1 if any finding; findings print as `#check <decl> /- <msg> -/`.

The five questions (notes/v3/01-core.md): none of its own — the IO
shell (root/carrier/spine answers live in LintKit.Runner). Gate row:
none — this exe IS the lintkit sweep's driver (the gated roots by
default), not a gate row.
-/
import LintKit
import Gates

open Lean LintKit

/-- The CLI surface: lint flags + module roots (empty = the gated roots). -/
private structure Cli where
  cfg : DriverConfig
  mods : Array Name

def Cli.gatedRoots : Array Name := #[`Kit, `TextKit, `TestingKit, `LintKit, `Gates, `Wit, `SchemaCore, `ZSet, `Machines, `Query, `Guest]

/-- The tree's srcDir layout (lakefile.toml): the gated roots' source
mounts, so the text lints resolve sources from the repo-root cwd. A
`--src-root=` flag adds mappings on top. -/
def Cli.defaultSrcRoots : Array (Name × String) :=
  #[(`Kit, "kit"), (`TextKit, "textkit"), (`TestingKit, "testingkit"),
    (`LintKit, "lintkit"), (`Gates, "gates"), (`Wit, "wit"),
    (`SchemaCore, "schemacore"), (`ZSet, "zset"), (`Machines, "machines"),
    (`Query, "query"), (`Guest, "guest")]

def Cli.parse (args : List String) : Cli := Id.run do
  let mut cfg : DriverConfig := { srcRoots := Cli.defaultSrcRoots }
  let mut mods : Array Name := #[]
  for a in args do
    if let some n := a.dropPrefix? "--disable=" then
      cfg := { cfg with overrides := cfg.overrides.insert n.toString.toName false }
    else if let some n := a.dropPrefix? "--enable=" then
      cfg := { cfg with overrides := cfg.overrides.insert n.toString.toName true }
    else if let some p := a.dropPrefix? "--extra-prefix=" then
      cfg := { cfg with extraPrefixes :=
        if cfg.extraPrefixes.isEmpty then p.toString
        else cfg.extraPrefixes ++ "," ++ p.toString }
    else if let some rs := a.dropPrefix? "--src-root=" then
      -- repeatable `--src-root=<module-root>=<dir>`: extra source mounts
      -- for the text lints (non-gated roots linted by hand)
      match rs.toString.splitOn "=" with
      | [r, dir] => cfg := { cfg with srcRoots := cfg.srcRoots.push (r.toName, dir) }
      | _ => pure ()  -- malformed flag: ignored (the usage line documents the shape)
    else
      mods := mods.push a.toName
  let roots := if mods.isEmpty then Cli.gatedRoots else mods
  return { cfg, mods := roots }

unsafe def main (args : List String) : IO UInt32 := do
  let parsed := Cli.parse args
  let cfg := parsed.cfg
  let mods := parsed.mods
  LintKit.initLintSearchPath
  Lean.enableInitializersExecution
  let env ← importModules (mods.map ({ module := · })) {}
    (trustLevel := 1024) (loadExts := true)
  let (findings, _) ← (LintKit.lintModules mods cfg).toIO
    { fileName := "<lintkit>", fileMap := default } { env }
  let roots := mods.map (·.getRoot)
  let (textFindings, missing) ← runTextLintsOnModules env roots cfg
  for m in missing do
    IO.eprintln s!"warning: no source file found for module `{m}` — text \
      lints skipped for it"
  let mut failed := false
  for f in findings do
    IO.println f.message
    failed := true
  for f in textFindings do
    IO.println s!"{f.file}:{f.line}: [{f.linter}] {f.message}"
    failed := true
  if failed then
    IO.println s!"lintkit: {findings.size + textFindings.size} finding(s) in \
      {String.intercalate " " (mods.map toString).toList}"
    return 1
  IO.println s!"lintkit: clean ({String.intercalate " " (mods.map toString).toList})"
  return 0

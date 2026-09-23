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

def Cli.gatedRoots : Array Name := #[`Kit, `TextKit, `TestKit, `LintKit, `Gates, `SchemaCore]

def Cli.parse (args : List String) : Cli := Id.run do
  let mut cfg : DriverConfig := {}
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
  let mut failed := false
  for f in findings do
    IO.println f.message
    failed := true
  if failed then
    IO.println s!"lintkit: {findings.size} finding(s) in \
      {String.intercalate " " (mods.map toString).toList}"
    return 1
  IO.println s!"lintkit: clean ({String.intercalate " " (mods.map toString).toList})"
  return 0

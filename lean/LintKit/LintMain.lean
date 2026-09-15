/-
LintMain — the `guestlang-lint` executable. Runs the guestlang env-linters +
text lints over a package's oleans WITHOUT the package importing LintKit:

    cd lean/<pkg> && lake env <LintKit>/.lake/build/bin/guestlang-lint <Module>...

Usage: `guestlang-lint [--disable=linter.guestlang.x] [--enable=linter.guestlang.x]
         [--extra-prefix=Foo.Bar] Module...`

`lake env` supplies the target package's `LEAN_PATH`/`LEAN_SRC_PATH`; the
driver importModules the given roots and lints exactly the declarations and
sources of modules rooted at them (never mathlib/core internals).
Exit 1 if any finding; findings print as `#check <decl> /- <msg> -/` (env
linters) or `file:line: <msg>` (text lints).
-/
import LintKit

open Lean LintKit

/-- The CLI surface: lint flags + module roots; `--artifacts-root=<path>`
(and no modules) runs the artifact-header gate instead. -/
private structure Cli where
  cfg : DriverConfig
  mods : Array Name
  artifactsRoot : Option String

def Cli.parse (args : List String) : Cli := Id.run do
  let mut cfg : DriverConfig := {}
  let mut mods : Array Name := #[]
  let mut root : Option String := none
  for a in args do
    if let some n := a.dropPrefix? "--disable=" then
      cfg := { cfg with overrides := cfg.overrides.insert n.toString.toName false }
    else if let some n := a.dropPrefix? "--enable=" then
      cfg := { cfg with overrides := cfg.overrides.insert n.toString.toName true }
    else if let some p := a.dropPrefix? "--extra-prefix=" then
      cfg := { cfg with extraPrefixes :=
        if cfg.extraPrefixes.isEmpty then p.toString
        else cfg.extraPrefixes ++ "," ++ p.toString }
    else if let some r := a.dropPrefix? "--artifacts-root=" then
      root := some r.toString
    else
      mods := mods.push a.toName
  return { cfg, mods, artifactsRoot := root }

unsafe def runArtifactGate (root : String) : IO UInt32 := do
  let findings ← LintKit.checkGeneratedArtifacts root
  for f in findings do
    IO.println s!"{f.file}: [{f.linter}] {f.message}"
  if findings.isEmpty then
    IO.println "artifact-headers: clean"
    return 0
  IO.println s!"artifact-headers: {findings.size} finding(s)"
  return 1

unsafe def main (args : List String) : IO UInt32 := do
  let { cfg, mods, artifactsRoot } := Cli.parse args
  if let some root := artifactsRoot then
    return ← runArtifactGate root
  if mods.isEmpty then
    IO.eprintln "usage: guestlang-lint [--disable=<linter.option>] \
      [--extra-prefix=<Prefix>] <Module>..."
    return 1
  LintKit.initLintSearchPath
  Lean.enableInitializersExecution
  let env ← importModules (mods.map ({ module := · })) {}
    (trustLevel := 1024) (loadExts := true)
  let (findings, _) ← (LintKit.lintModules mods cfg).toIO
    { fileName := "<guestlang-lint>", fileMap := default } { env }
  let roots := mods.map (·.getRoot)
  let (textFindings, missing) ← runTextLintsOnModules env roots cfg
  for m in missing do
    IO.eprintln s!"warning: no source file found for module `{m}` on \
      LEAN_SRC_PATH — text lints skipped for it"
  let mut failed := false
  for f in findings do
    IO.println f.message
    failed := true
  for f in textFindings do
    IO.println s!"{f.file}:{f.line}: [{f.linter}] {f.message}"
    failed := true
  if failed then
    IO.println s!"guestlang-lint: {findings.size + textFindings.size} finding(s) in \
      {String.intercalate " " (mods.map toString).toList}"
    return 1
  IO.println s!"guestlang-lint: clean ({String.intercalate " " (mods.map toString).toList})"
  return 0

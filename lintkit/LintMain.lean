/-
LintMain — the `lintkit` executable: runs the tree's env-linters over a
package's oleans WITHOUT the package importing LintKit:

    lake exe lintkit [flags] [Module...]

With NO modules the GATED PACKAGES are linted — Gates.Packages'
`gatedPackages` table, THE single source (the re-audit's finding: this
driver kept its own root + srcRoot tables, which had drifted from the
gates'). The fold is ONE CHILD PROCESS PER PACKAGE (`--package=<dir>`
re-dispatches to a single-package shard): cross-package decl-name
collisions refuse a shared `importModules` (observed: two test
fixtures' `duelSpec`), and libgc's conservative stack scan retains each
dropped env — the in-process fold peaked past the OOM line (the legacy
tree's sharded-mode lesson, arrived again at 42 gated packages). `lake
build` first: the driver imports oleans, never builds them.

Usage: `lintkit [--disable=linter.guestlang.x] [--enable=linter.guestlang.x]
         [--extra-prefix=Foo.Bar] [--src-root=Root=dir] Module...`

Exit 1 if any finding; findings print as `#check <decl> /- <msg> -/`.

The five questions (notes/v3/01-core.md): none of its own — the IO
shell (root/carrier/spine answers live in LintKit.Runner). Gate row:
none — this exe IS the lintkit sweep's driver (the gated roots by
default), not a gate row.
-/
import LintKit
import Gates

open Lean LintKit

/-- The gated source mounts, DERIVED from Gates.Packages' table (the
single source — never a parallel copy; `gates packages-check` guards
the table against the lakefile both directions). -/
def Cli.defaultSrcRoots : Array (Name × String) :=
  (Gates.gatedPackages.toList.flatMap fun p =>
    p.roots.toList.map fun r => (r, p.srcDir)).toArray

/-- The CLI surface: lint flags + module roots (`none` = the gated
packages, the table's fold) + the child dispatch (`--package=<dir>`:
one gated package, the shard's own process). The PARSE is Kit.Cli's
(C7's one driver): the shared `--package` + the lint extras; an
unknown `--…` token refuses through the closed-world Diag (the
did-you-mean — the old parse silently swallowed it as a module name). -/
def Cli.parse (args : List String) :
    Except Kit.Diag (DriverConfig × Option (Array Name) × Option String) := do
  let f ← Kit.Cli.parseFlags ["disable", "enable", "extra-prefix", "src-root"] args
  let mut cfg : DriverConfig := { srcRoots := Cli.defaultSrcRoots }
  -- the repeatable `--src-root=<module-root>=<dir>`: extra source mounts
  -- for the text lints (non-gated roots linted by hand)
  for rs in f.all "src-root" do
    match rs.splitOn "=" with
    | [r, d] => cfg := { cfg with srcRoots := cfg.srcRoots.push (r.toName, d) }
    | _ => pure ()  -- malformed: ignored (the usage line documents the shape)
  for n in f.all "disable" do
    cfg := { cfg with overrides := cfg.overrides.insert n.toName false }
  for n in f.all "enable" do
    cfg := { cfg with overrides := cfg.overrides.insert n.toName true }
  for p in f.all "extra-prefix" do
    cfg := { cfg with extraPrefixes :=
      if cfg.extraPrefixes.isEmpty then p
      else cfg.extraPrefixes ++ "," ++ p }
  let mods := if f.rest.isEmpty then none else some (f.rest.map (·.toName)).toArray
  return (cfg, mods, f.pkg)

-- The one-package lint fold (the shard body) is `LintKit.lintShard`
-- (Runner) — shared verbatim with the lint gate row (`Gates.Lint`); the
-- explicit mode's fold below is its roots-generalization, kept there.

unsafe def main (args : List String) : IO UInt32 := do
  let (cfg, mods, pkg) ←
    match Cli.parse args with
    | .error d =>
        IO.eprintln (Kit.Diag.toString d)
        return 1
    | .ok p => pure p
  LintKit.initLintSearchPath
  match pkg with
  | some dir =>
      -- THE SHARD: one gated package, this process's ONLY env (the
      -- runAll/per-gate RSS discipline: libgc's conservative stack scan
      -- retains each dropped env — 42 packages folded in one process
      -- peaked past the OOM line, observed). The table row is looked up
      -- by dir — the single source, never a parallel copy.
      match Gates.gatedPackages.toList.find? fun p => p.dir == dir with
      | none =>
          IO.eprintln s!"lintkit: --package={dir} names no Gates.Packages row"
          return 1
      | some pkg =>
          let base ← Lean.searchPathRef.get
          match ← Gates.loadPkgEnv base pkg with
          | .error e =>
              IO.eprintln s!"lintkit: {pkg.dir}: LOAD FAILED — {e}"
              return 1
          | .ok env =>
              let mods := String.intercalate " " (pkg.roots.map toString).toList
              return if ← LintKit.lintShard s!"{pkg.dir} ({mods})" pkg.roots cfg env
                then 1 else 0
  | none => match mods with
  | some mods =>
      -- the explicit mode: ONE env over the given modules (the caller's
      -- own scope; a cross-package decl-name collision refuses loudly —
      -- the gated default's per-package fold is the collision-free path)
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
      let mods := String.intercalate " " (mods.map toString).toList
      if ← LintKit.reportFindings mods findings textFindings then return 1
      IO.println s!"lintkit: clean ({mods})"
      return 0
  | none =>
      -- the GATED default: the table's fold, ONE CHILD PROCESS per
      -- package (the shard above; the same shape `Gates.runAll` uses
      -- for the gate rows). The child's stdio is inherited so the
      -- findings stream live.
      let mut failed := false
      let mut linted : Array String := #[]
      for pkg in Gates.gatedPackages do
        let child ← IO.Process.spawn
          { cmd := "lake", args := #["exe", "lintkit", s!"--package={pkg.dir}"]
          , stdout := .inherit, stderr := .inherit }
        let code ← child.wait
        if code != 0 then failed := true
        linted := linted.push pkg.dir
      if failed then
        IO.println s!"lintkit: FAILED ({linted.size} package(s) folded \
          before the verdict)"
        return 1
      IO.println s!"lintkit: clean ({linted.size} gated package(s) — \
        Gates.Packages' table, the single source)"
      return 0

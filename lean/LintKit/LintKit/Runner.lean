/-
LintKit.Runner — the engine shared by the `guestlang-lint` exe
(`LintMain.lean`) and the self-tests (`Tests/Main.lean`).

Why a custom runner instead of `lake lint --builtin-lint` (the v4.33 stock
mechanism): stock env-linting gates every per-declaration check on
`envLinterSnapshotExt`, which is populated at `addDecl` time ONLY when the
linter's option was registered in the elaborating process — i.e. only for
modules that import LintKit. Requiring every module of every package to
import LintKit is precisely the downstream burden the doctrine forbids. This
runner instead treats "no snapshot" as "option default" (still honoring
snapshots and `@[nolint]` where they exist), so `lake env guestlang-lint`
works on unmodified packages.

The linters are also registered via `@[builtin_env_linter]`, so packages
that DO import LintKit get stock `lake lint --builtin-lint` integration for
free (snapshots recorded, per-decl opt-outs honored by core).
-/
module

public import LintKit.AxiomAllowlist
public import LintKit.GuestBan
public import LintKit.RecursiveSimpEqns
public import LintKit.DupDefBodies
public import LintKit.PackageNamespace
public import LintKit.TextLints
public import LintKit.UpstreamDup
public import LintKit.BareChecker
public import LintKit.CodecLints

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- One env-linter finding: linter option name, declaration, rendered
message (via `EnvLinter.printWarning`: `#check <decl> /- <msg> -/`). -/
structure LintFinding where
  linter  : Name
  decl    : Name
  message : String
  deriving Repr, Inhabited

/-- Driver configuration: CLI per-linter overrides win over option defaults
when no per-declaration snapshot exists. -/
structure DriverConfig where
  overrides     : NameMap Bool := {}
  /-- Comma-separated extra prefixes for `packageNamespace`. -/
  extraPrefixes : String := ""
  /-- `--src-root=<module-root>=<dir>` mappings (repeatable): where a linted
  module root's sources live RELATIVE TO THE DRIVER'S CWD. The single-lake
  migration's fix: the driver runs from the repo root, but absorbed packages'
  sources stay at `lean/<dir>/` — text lints must resolve them there or they
  are silently skipped (the cwd fallback below stays for the classic
  `cd lean/<pkg>` invocation). -/
  srcRoots      : Array (Name × String) := {}
  deriving Inhabited

/-- The guestlang env-linters, with their options. This list is the driver's
registry; the `@[builtin_env_linter]` registrations are for the stock
`lake lint` path. -/
meta def guestlangLinters : Array (NamedEnvLinter × Lean.Option Bool) := #[
  ({ toEnvLinter := axiomAllowlistLinter
     optName := `linter.guestlang.axiomAllowlist
     declName := ``LintKit.axiomAllowlistLinter },
   linter.guestlang.axiomAllowlist),
  ({ toEnvLinter := recursiveSimpEqnsLinter
     optName := `linter.guestlang.recursiveSimpEqns
     declName := ``LintKit.recursiveSimpEqnsLinter },
   linter.guestlang.recursiveSimpEqns),
  ({ toEnvLinter := dupDefBodiesLinter
     optName := `linter.guestlang.dupDefBodies
     declName := ``LintKit.dupDefBodiesLinter },
   linter.guestlang.dupDefBodies),
  ({ toEnvLinter := packageNamespaceLinter
     optName := `linter.guestlang.packageNamespace
     declName := ``LintKit.packageNamespaceLinter },
   linter.guestlang.packageNamespace),
  ({ toEnvLinter := GuestBan.guestBanLinter
     optName := `linter.guestlang.guestBan
     declName := ``LintKit.GuestBan.guestBanLinter },
   linter.guestlang.guestBan),
  ({ toEnvLinter := upstreamDupLinter
     optName := `linter.guestlang.upstreamDup
     declName := ``LintKit.upstreamDupLinter },
   linter.guestlang.upstreamDup),
  ({ toEnvLinter := bareCheckerLinter
     optName := `linter.guestlang.bareChecker
     declName := ``LintKit.bareCheckerLinter },
   linter.guestlang.bareChecker)
]

/-- Per-declaration enablement (the runner's replacement for core's
snapshot-only `isLinterEnabledFor`): `@[nolint]` > elaboration-time
`set_option` snapshot > CLI override > option default. -/
def linterEnabledFor (env : Environment) (cfg : DriverConfig)
    (opt : Lean.Option Bool) (decl : Name) : Bool :=
  if hasNolint env decl opt.name then false
  else match Linter.getEnvLinterSnapshotEntry? env decl opt.name with
    | some b => b
    | none   => (cfg.overrides.find? opt.name).getD opt.defValue

/-- All declarations of the environment whose defining module's name is
rooted at one of `roots` (i.e. the target package's own decls — never
mathlib/core internals). -/
def packageDecls (env : Environment) (roots : Array Name) : CoreM (Array Name) := do
  let mut decls : Array Name := #[]
  for (decl, _) in env.constants.map₁.toList do
    let some idx := env.const2ModIdx[decl]? | continue
    let m := env.header.moduleNames[idx]!
    if roots.any (·.isPrefixOf m) then
      decls := decls.push decl
  return decls

/-- Run every enabled env-linter over `decls`. -/
def runLintersOnDecls (decls : Array Name) (cfg : DriverConfig := {}) :
    CoreM (Array LintFinding) := do
  let env ← getEnv
  withOptions (·.set `linter.guestlang.packageNamespace.extraPrefixes
      (DataValue.ofString cfg.extraPrefixes)) do
    let mut findings := #[]
    for (linter, opt) in guestlangLinters do
      -- whole-linter CLI disable: skip the pass (per-decl snapshots may still
      -- differ, but a CLI `--disable` is meant as a blanket off)
      if cfg.overrides.find? opt.name == some false then continue
      for decl in decls do
        unless linterEnabledFor env cfg opt decl do continue
        let msg? ← tryCatch
          ((linter.test decl).run' Elab.Command.mkMetaContext)
          fun e => pure (some m!"LINTER FAILED:\n{e.toMessageData}")
        match msg? with
        | none => continue
        | some msg =>
          let rendered ← Linter.EnvLinter.printWarning decl msg
          findings := findings.push { linter := linter.optName, decl, message := ← rendered.toString }
    return findings

/-- Lint the import closure of `mods` (the package's roots: lib umbrella +
tests root), restricted to decls defined in modules rooted at those roots.
Returns findings sorted by declaration name for deterministic output. -/
def lintModules (mods : Array Name) (cfg : DriverConfig := {}) :
    CoreM (Array LintFinding) := do
  let roots := mods.map (·.getRoot)
  let decls ← packageDecls (← getEnv) roots
  let findings ← runLintersOnDecls decls cfg
  return findings.qsort fun a b => Name.quickLt a.decl b.decl

/-- Initialize the search paths for a lint run. The driver is always
invoked as `cd lean/<pkg> && lake env guestlang-lint ...`; `lake env` puts
DEPENDENCIES before the root package on `LEAN_PATH`, so an unqualified
`Tests.Main` resolves to a dependency's identically-named test module
(observed: LSpec's `Tests/Main.olean` shadows codegen-core's). Prepending
the cwd package's own build dir restores the resolution order the package's
own build uses. -/
def initLintSearchPath : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let cwd ← IO.currentDir
  Lean.searchPathRef.modify fun sp => (cwd / ".lake" / "build" / "lib" / "lean") :: sp

/-- The `--src-root` mapping lookup: the FIRST mapping whose root prefixes
the module wins (the justfile passes one flag per absorbed lib); `none` =
the cwd fallback. Pure so the self-tests can pin the resolution order. -/
def srcRootFor (srcRoots : Array (Name × String)) (m : Name) : Option String :=
  (srcRoots.find? fun (r, _) => r.isPrefixOf m).map (·.2)

/-- Source-text lints over the `.lean` files of all linted modules. Sources
resolve through the `--src-root` mappings first (`<module-root>=<dir>`, the
single-lake driver's absorbed-package mounts), then cwd-relative (the
classic `cd lean/<pkg>` invocation — every linted module belongs to the cwd
package, see `initLintSearchPath`), never via the search path, so dependency
modules with colliding names are never scanned. Missing sources are reported
as warnings by the caller, never silently skipped. -/
def runTextLintsOnModules (env : Environment) (roots : Array Name)
    (cfg : DriverConfig := {}) : IO (Array TextFinding × Array Name) := do
  let cwd ← IO.currentDir
  let mut findings := #[]
  let mut missing := #[]
  for m in env.header.moduleNames do
    unless roots.any (·.isPrefixOf m) do continue
    -- first --src-root mapping whose root prefixes the module wins; the
    -- cwd fallback keeps the pre-monolith per-package invocation working
    let file := match srcRootFor cfg.srcRoots m with
      | some dir => modToFilePath dir m "lean"
      | none => modToFilePath cwd m "lean"
    unless ← file.pathExists do
      missing := missing.push m
      continue
    let content ← IO.FS.readFile file
    for f in runTextLints file.toString content
        ++ checkUnregisteredRoundtrip file.toString content
        ++ checkDidyoumeanDiscipline file.toString content do
      let on := (cfg.overrides.find? f.linter).getD true
      if on then findings := findings.push f
  return (findings, missing)

/-- Extract the `"outputs": [...]` string arrays from a forge jobs manifest
(the writer is ours and stable: `jobJson` in SchemaLang.Emit.Registry). -/
private def outputsOf (manifest : String) : List String := Id.run do
  let mut outs := []
  for chunk in (manifest.splitOn "\"outputs\"").drop 1 do
    let arr := ((chunk.splitOn "]").headD "")
    let mut inStr := false
    let mut cur := ""
    for c in arr.toList do
      if c == '"' then
        if inStr then outs := cur :: outs
        inStr := !inStr
        cur := ""
      else if inStr then cur := cur ++ c.toString
  return outs.reverse

/-- The artifact-header gate: every generated output DECLARED in a forge
jobs manifest exists on disk and starts with the GENERATED header (the
driver prepends it — a missing header means a hand-written or stale file
sits at a generated path). `repoRoot` because the exe runs from a package
dir. Returns findings (linter name `linter.guestlang.artifactHeader`). -/
def checkGeneratedArtifacts (repoRoot : System.FilePath) : IO (Array TextFinding) := do
  let manifests := ["crates/forge/src/jobs_generated.json",
                    "crates/forge/src/faults_jobs_generated.json"]
  let mut findings := #[]
  for m in manifests do
    let path := repoRoot / m
    unless ← path.pathExists do continue
    let content ← IO.FS.readFile path
    for out in outputsOf content do
      let p := repoRoot / out
      if !(← p.pathExists) then
        findings := findings.push
          { file := out, line := 0
            linter := `linter.guestlang.artifactHeader
            message := "declared generated output does not exist — run `just gen`" }
      else
        let headStr ← IO.FS.withFile p .read fun h => do
          pure ((← h.getLine) ++ (← h.getLine))
        unless (headStr.splitOn "GENERATED by").length > 1 do
          findings := findings.push
            { file := out, line := 1
              linter := `linter.guestlang.artifactHeader
              message := "declared generated output lacks the GENERATED header — \
                a hand-written file sits at a generated path (the one-writer rule)" }
  return findings

end LintKit

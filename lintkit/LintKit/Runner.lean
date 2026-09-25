/-
LintKit.Runner — the engine the `lintkit` exe drives (mined from
legacy/lean/LintKit/LintKit/Runner.lean).

Why a custom runner instead of `lake lint --builtin-lint` (the v4.33
stock mechanism): stock env-linting gates every per-declaration check on
`envLinterSnapshotExt`, which is populated at `addDecl` time ONLY when
the linter's option was registered in the elaborating process — i.e. only
for modules that import LintKit. Requiring every module of every package
to import LintKit is precisely the downstream burden the doctrine
forbids. This runner instead treats "no snapshot" as "option default"
(still honoring snapshots and `@[nolint]` where they exist).

The linters are ALSO registered via `@[builtin_env_linter]` (the
`register_guestlang_linter` macro's third part), so packages that DO
import LintKit get stock `lake lint --builtin-lint` integration for free.

The text lints (LintKit.TextLints/CodecLints) run over each linted
module's SOURCE file — the source walk (`runTextLintsOnModules`) resolves
files via the driver's `srcRoots` mappings (module root → directory),
never via the search path, so dependency modules with colliding names
are never scanned. Deliberate exclusions vs the legacy Runner: the
artifact-header gate (arrives with the first emitter —
nothing-without-a-consumer).

The five questions (notes/v3/01-core.md):
- root: none — the driver engine (why a custom runner: the header note
above).
- carrier grade: none — findings are structured data (ctors).
- spine reading: the interpretation stage (env → findings → rendered
lines); the exit code is the verdict.
- ladder rung: n/a (host machinery).
- gate row: the lintkit exe over the gated roots + Gates.Axioms'
allowlist run (the same runner code path).
-/
module

public import LintKit.AxiomAllowlist
public import LintKit.BareChecker
public import LintKit.Citations
public import LintKit.CodecLints
public import LintKit.Cone
public import LintKit.DecideFirst
public import LintKit.DupDefBodies
public import LintKit.Graduation
public import LintKit.GuestBan
public import LintKit.PackageNamespace
public import LintKit.RecursiveSimpEqns
public import LintKit.TextLints
public import LintKit.VerdictCtors
public import LintKit.ZeroCitation

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

/-- Driver configuration: CLI per-linter overrides win over option
defaults when no per-declaration snapshot exists. -/
structure DriverConfig where
  overrides     : NameMap Bool := {}
  /-- Comma-separated extra prefixes for `packageNamespace`. -/
  extraPrefixes : String := ""
  /-- `<module-root>=<dir>` mappings (repeatable): where a linted module
  root's sources live RELATIVE TO THE DRIVER'S CWD. Text lints must
  resolve sources or they are silently skipped (reported as warnings). -/
  srcRoots      : Array (Name × String) := {}
  deriving Inhabited

/-- The tree's env-linters, with their options. This list is the driver's
registry; the `@[builtin_env_linter]` registrations are for the stock
`lake lint` path. -/
meta def lintkitLinters : Array (NamedEnvLinter × Lean.Option Bool) := #[
  ({ toEnvLinter := axiomAllowlistLinter
     optName := `linter.guestlang.axiomAllowlist
     declName := ``LintKit.axiomAllowlistLinter },
   linter.guestlang.axiomAllowlist),
  ({ toEnvLinter := dupDefBodiesLinter
     optName := `linter.guestlang.dupDefBodies
     declName := ``LintKit.dupDefBodiesLinter },
   linter.guestlang.dupDefBodies),
  ({ toEnvLinter := packageNamespaceLinter
     optName := `linter.guestlang.packageNamespace
     declName := ``LintKit.packageNamespaceLinter },
   linter.guestlang.packageNamespace),
  ({ toEnvLinter := bareCheckerLinter
     optName := `linter.guestlang.bareChecker
     declName := ``LintKit.bareCheckerLinter },
   linter.guestlang.bareChecker),
  ({ toEnvLinter := verdictCtorsLinter
     optName := `linter.guestlang.verdictCtors
     declName := ``LintKit.verdictCtorsLinter },
   linter.guestlang.verdictCtors),
  ({ toEnvLinter := recursiveSimpEqnsLinter
     optName := `linter.guestlang.recursiveSimpEqns
     declName := ``LintKit.recursiveSimpEqnsLinter },
   linter.guestlang.recursiveSimpEqns),
  ({ toEnvLinter := GuestBan.guestBanLinter
     optName := `linter.guestlang.guestBan
     declName := ``LintKit.GuestBan.guestBanLinter },
   linter.guestlang.guestBan),
  ({ toEnvLinter := decideFirstLinter
     optName := `linter.guestlang.decideFirst
     declName := ``LintKit.decideFirstLinter },
   linter.guestlang.decideFirst),
  ({ toEnvLinter := graduationLinter
     optName := `linter.guestlang.graduation
     declName := ``LintKit.graduationLinter },
   linter.guestlang.graduation),
  ({ toEnvLinter := zeroCitationLinter
     optName := `linter.guestlang.zeroCitation
     declName := ``LintKit.zeroCitationLinter },
   linter.guestlang.zeroCitation)
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
    for (linter, opt) in lintkitLinters do
      -- whole-linter CLI disable: skip the pass (per-decl snapshots may
      -- still differ, but a CLI `--disable` is meant as a blanket off)
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
          findings := findings.push
            { linter := linter.optName, decl, message := ← rendered.toString }
    return findings

/-- Module-level linters: the IMPORT GRAPH is the input, so the test
runs per module, not per declaration (an empty module can violate — a
per-decl test cannot express that). Gating: the option value + the CLI
override; `@[nolint]` cannot attach to a module. No `builtin_env_linter`
mount: that path is per-declaration; this runner is the consumer. -/
meta def lintkitModuleLinters :
    Array (Lean.Option Bool × (Name → CoreM (Array MessageData))) :=
  #[(linter.guestlang.coneImports, coneModuleTest)]

/-- Run the module-level linters over the modules rooted at `roots`.
A finding's `decl` field carries the MODULE name (the site of an import
violation). -/
def runModuleLinters (env : Environment) (roots : Array Name)
    (cfg : DriverConfig := {}) : CoreM (Array LintFinding) := do
  let opts ← getOptions
  let mut findings := #[]
  for (opt, test) in lintkitModuleLinters do
    if cfg.overrides.find? opt.name == some false then continue
    unless opt.get opts do continue
    for h : idx in [0:env.header.moduleNames.size] do
      let m := env.header.moduleNames[idx]
      if roots.any (·.isPrefixOf m) then
        for msg in ← test m do
          findings := findings.push
            { linter := opt.name, decl := m, message := ← msg.toString }
  return findings

/-! ## the text lints (source walk) -/

/-- The text lints (LintKit.TextLints/CodecLints), with their options:
pure `file → content → findings` functions. -/
def lintkitTextLints :
    Array (Lean.Option Bool × (String → String → Array TextFinding)) :=
  #[(linter.guestlang.noNewPartial, checkNoNewPartial),
    (linter.guestlang.nolintReason, checkNolintReason),
    (linter.guestlang.unregisteredRoundtrip, checkUnregisteredRoundtrip),
    (linter.guestlang.didyoumeanDiscipline, checkDidyoumeanDiscipline)]

/-- The `--src-root` mapping lookup: the FIRST mapping whose root prefixes
the module wins; `none` = the cwd fallback. Pure so the self-tests can
pin the resolution order. -/
def srcRootFor (srcRoots : Array (Name × String)) (m : Name) : Option String :=
  (srcRoots.find? fun (r, _) => r.isPrefixOf m).map (·.2)

/-- Source-text lints over the `.lean` files of all linted modules. Sources
resolve through the `--src-root` mappings first, then cwd-relative; never
via the search path, so dependency modules with colliding names are never
scanned. Missing sources are reported as warnings by the caller, never
silently skipped. -/
def runTextLintsOnModules (env : Environment) (roots : Array Name)
    (cfg : DriverConfig := {}) : IO (Array TextFinding × Array Name) := do
  let cwd ← IO.currentDir
  let mut findings := #[]
  let mut missing := #[]
  for m in env.header.moduleNames do
    unless roots.any (·.isPrefixOf m) do continue
    let file := match srcRootFor cfg.srcRoots m with
      | some dir => modToFilePath dir m "lean"
      | none => modToFilePath cwd m "lean"
    unless ← file.pathExists do
      missing := missing.push m
      continue
    let content ← IO.FS.readFile file
    for (opt, check) in lintkitTextLints do
      if cfg.overrides.find? opt.name == some false then continue
      for f in check file.toString content do
        findings := findings.push f
  return (findings, missing)

/-- Lint the import closure of `mods` (the package's roots), restricted
to decls defined in modules rooted at those roots. The DECLARATION
linters run per decl; the MODULE linters (the import graph is their
input — `LintKit.lintkitModuleLinters`) run per module. Returns
findings sorted by declaration/module name for deterministic output. -/
def lintModules (mods : Array Name) (cfg : DriverConfig := {}) :
    CoreM (Array LintFinding) := do
  let roots := mods.map (·.getRoot)
  let decls ← packageDecls (← getEnv) roots
  let declFindings ← runLintersOnDecls decls cfg
  let modFindings ← runModuleLinters (← getEnv) roots cfg
  return (declFindings ++ modFindings).qsort fun a b => Name.quickLt a.decl b.decl

/-- `lintModules` over the EXACT module names (no `getRoot` widening):
the sweep covers the named modules' own code only. The gated-table
consumer (LintMain's per-package fold) needs this for the fixture-rig
roots whose namespace siblings are PLANTED violators (the
`LintKitTests`/`LintKitFixtures` rigs exist to fail the linters —
their consumers are the LintKitTests pins, which demand exactly that
failure; a namespace-widened sweep would gate a permanent red). -/
def lintModulesExact (mods : Array Name) (cfg : DriverConfig := {}) :
    CoreM (Array LintFinding) := do
  let decls ← packageDecls (← getEnv) mods
  let declFindings ← runLintersOnDecls decls cfg
  let modFindings ← runModuleLinters (← getEnv) mods cfg
  return (declFindings ++ modFindings).qsort fun a b => Name.quickLt a.decl b.decl

/-- Initialize the search paths for a lint run (the exe runs from the
repo root; the package's own build dir is prepended so its modules win
over same-named dependency modules). -/
def initLintSearchPath : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let cwd ← IO.currentDir
  Lean.searchPathRef.modify fun sp => (cwd / ".lake" / "build" / "lib" / "lean") :: sp

end LintKit

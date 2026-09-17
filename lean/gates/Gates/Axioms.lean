/-
# Gates.Axioms — the axiom report (`gates axioms [--write] [--package X]`)

Replaces the `just lean-axioms` shell loop (per-package
`lake env guestlang-lint` subprocesses).

SHARDING (the memory fix): the no-flag mode imports EVERY gated
package's environment into ONE process — peak RSS hit ~26.5GB and
tripped earlyoom on a 29GB box. `--package X` imports ONE package's
environment (one process = one environment, ~2–4GB peak); the
`lean-axioms` recipe loops it over `lean_pkgs`. The no-flag mode stays
for the full-file `--write` bootstrap and `gates all`.

The committed baseline stays ONE file (notes/axiom-report.md), one
`## <dir>` section per package. `--package X --write` rewrites only X's
section in place (every other byte untouched); the sharded check diffs
only X's section. The no-flag check still diffs the whole file.

No-flag mode: for each gated
package, its root modules are `importModules`'d (oleans built by
`just lean-build` — this gate never builds), every declaration defined
in those modules gets its axiom cone from the kernel's own
`Lean.collectAxioms` (the `CollectAxioms` machinery `#print axioms`
drives — module-local thanks to the per-module precomputed axiom
extension), and the cone is checked against the allowlist by CONSUMING
`LintKit.runLintersOnDecls` with every non-axiom linter disabled (the
allowlist itself — `LintKit.isAllowedAxiom`: core triple + disclosed
`_native.native_decide.`/`_native.bv_decide.` trust bases — lives in
LintKit.AxiomAllowlist and is never re-encoded here). `@[nolint]` and
`set_option` snapshots are honored exactly as in the old gate (same
runner code path).

Output: one block per package — decls checked, the DISTINCT axiom set
the package actually depends on (the report the hand-maintained
`#print axioms` lists never gave), violations. `--write` updates the
committed `notes/axiom-report.md` (whole file, or X's section under
`--package X`); without it, a diff against the committed report IS the
CI gate (a silent axiom-surface change fails).
Violations and load failures exit 1 regardless of `--write`.

Search paths: the exe runs from `lean/gates` under `lake env`; each
package's own `.lake/build/lib/lean` is prepended per package (the
LintKit.Runner lesson — deps come first on `lake env`'s LEAN_PATH, and
`Tests.Main` exists in several packages, so the target package's dir
must win). qlang/proofkit/ledger/feature-flags/edgepython are NOT
requires of this package — their deps all sit inside gates' cone, so
their own build dir is the only extra path they need.

LEGACY (non-module) file: meta env-extension access (constraint 12,
notes/w5-4-module-migration.md).
-/
import Lean
import LintKit
import Gates.Packages

open Lean

namespace Gates.Axioms

open Gates (PkgSpec gatedPackages)

structure PkgReport where
  dir : String
  decls : Nat := 0
  /-- The distinct axiom set the package's decls depend on, sorted. -/
  axioms : Array Name := #[]
  violations : Array LintKit.LintFinding := #[]
  loadError : Option String := none

/-- Axiom-only lint config: every non-axiom linter whole-disabled at the
    CLI-override level (the runner skips the pass entirely); the axiom
    allowlist keeps its default-on + per-decl snapshot/nolint semantics. -/
def axiomOnlyConfig : LintKit.DriverConfig :=
  { overrides := ({} : NameMap Bool)
      |>.insert `linter.guestlang.dupDefBodies false
      |>.insert `linter.guestlang.packageNamespace false
      |>.insert `linter.guestlang.recursiveSimpEqns false
      |>.insert `linter.guestlang.guestBan false }

/-- Per-package analysis over its imported environment: the allowlist
    violations (LintKit's runner, unmodified) + the distinct axiom union
    (the kernel's CollectAxioms per decl). -/
def analyzeEnv (roots : Array Name) :
    CoreM (Array Name × Array LintKit.LintFinding × Array Name) := do
  let decls ← LintKit.packageDecls (← getEnv) roots
  let findings ← LintKit.runLintersOnDecls decls axiomOnlyConfig
  let mut axs : NameSet := {}
  for d in decls do
    for a in ← collectAxioms d do
      axs := axs.insert a
  return (decls, findings, axs.toArray.qsort Name.quickLt)

/-- Import one package's roots (its own build dir prepended so its
    `Tests.Main` wins over same-named dep modules) and analyze. -/
unsafe def analyzePkg (base : SearchPath) (pkg : PkgSpec) : IO PkgReport := do
  let pkgLib : System.FilePath := s!"../{pkg.dir}/.lake/build/lib/lean"
  Lean.searchPathRef.set (pkgLib :: base)
  try
    Lean.enableInitializersExecution
    let env ← importModules (pkg.roots.map ({ module := · })) {}
      (trustLevel := 1024) (loadExts := true)
    let modRoots := pkg.roots.map (·.getRoot)
    let ctx : Core.Context := { fileName := "<gates-axioms>", fileMap := default }
    let (res, _) ← (analyzeEnv modRoots).toIO ctx { env := env }
    let (decls, findings, axs) := res
    return { dir := pkg.dir, decls := decls.size, axioms := axs, violations := findings }
  catch e =>
    return { dir := pkg.dir, loadError := some (toString e) }

/-- The committed report this gate diffs against (the `diff = CI gate`
    half). -/
def reportPath : System.FilePath := "../../notes/axiom-report.md"

/-- The committed report's fixed header (everything before the first
    `## ` section line). -/
def reportHeader : List String :=
  [ "# Axiom report — the global axiom surface"
  , ""
  , "GENERATED by `lake exe gates axioms --write` (lean/gates) — do not hand-edit."
  , "CI runs `gates axioms` without `--write`; a diff against this file fails the gate."
  , ""
  , "Per package: every declaration of the listed root modules gets its axiom cone"
  , "from the kernel's CollectAxioms; the allowlist (propext, Classical.choice,"
  , "Quot.sound, disclosed _native.native_decide./_native.bv_decide. trust bases)"
  , "is LintKit.AxiomAllowlist's, consumed via LintKit.runLintersOnDecls."
  , "" ]

/-- One package block (deterministic: axioms sorted, violations sorted
    by decl name upstream). Ends with its blank separator line. -/
def renderBlock (r : PkgReport) : List String :=
  match r.loadError with
  | some e =>
    [ s!"## {r.dir}", "", s!"LOAD FAILED: {e}", "" ]
  | none =>
    [ s!"## {r.dir} — {r.decls} decls checked"
    , ""
    , s!"axioms used: {if r.axioms.isEmpty then "(none — fully constructive)"
        else String.intercalate ", " (r.axioms.map toString).toList}"
    , s!"violations: {if r.violations.isEmpty then "none"
        else toString r.violations.size ++ " (see gate output)"}"
    , "" ]

/-- Render the global report (deterministic: package order fixed). -/
def render (reports : Array PkgReport) : String :=
  String.intercalate "\n" (reportHeader ++ (reports.toList.flatMap renderBlock))

/-- Drop trailing empty lines (a block's trailing blank is the section
    separator, not content; the file's last section carries one extra
    from the final newline). -/
def normLines (ls : List String) : List String :=
  ls.reverse.dropWhile (· == "") |>.reverse

/-- Split the committed report into header lines + (dir, lines)
    sections in file order. A section runs from its `## <dir>…` line to
    the next `## ` line or EOF; the key is the title up to ` — `
    (package dirs contain neither). Section lines are normalized
    (separator blanks stripped). -/
def parseSections (text : String) : List String × List (String × List String) :=
  let rec go (header : List String) (cur : Option (String × List String))
      (acc : List (String × List String)) :
      List String → List String × List (String × List String)
    | [] =>
      let acc := match cur with
        | none => acc
        | some (k, ls) => acc ++ [(k, normLines ls)]
      (header, acc)
    | l :: rest =>
      if l.startsWith "## " then
        let acc := match cur with
          | none => acc
          | some (k, ls) => acc ++ [(k, normLines ls)]
        let key := ((l.drop 3).toString.splitOn " — ").headD ""
        go header (some (key, [l])) acc rest
      else match cur with
        | none => go (header ++ [l]) none acc rest
        | some (k, ls) => go header (some (k, ls ++ [l])) acc rest
  go [] none [] (text.splitOn "\n")

/-- Reassemble header + sections with the canonical separators.
    Byte-identical to `render ++ "\n"` when every section is in sync
    and the header is `reportHeader`'s — a sectional `--write` of an
    in-sync report dirties nothing. -/
def serializeSections (header : List String)
    (sections : List (String × List String)) : String :=
  String.intercalate "\n"
    (header ++ sections.flatMap (fun (_, ls) => normLines ls ++ [""])) ++ "\n"

/-- Print one package's result line + violation messages; return whether
    it failed (load error or allowlist violations). -/
def printReport (r : PkgReport) : IO Bool := do
  match r.loadError with
  | some e =>
    IO.println s!"{r.dir}: LOAD FAILED — {e}"
    return true
  | none =>
    IO.println s!"{r.dir}: {r.decls} decls, axioms [{String.intercalate ", " (r.axioms.map toString).toList}], {r.violations.size} violation(s)"
    for v in r.violations do
      IO.println v.message
    return !r.violations.isEmpty

/-- Sharded mode (`--package X`): analyze ONE package (one environment
    in this process); `--write` rewrites only X's section of the
    committed report in place, the check diffs only X's section. -/
unsafe def runOne (base : SearchPath) (pkg : PkgSpec) (write : Bool) : IO UInt32 := do
  let r ← analyzePkg base pkg
  let mut failed ← printReport r
  let fresh := normLines (renderBlock r)
  if write then
    if ← reportPath.pathExists then
      let (header, sections) := parseSections (← IO.FS.readFile reportPath)
      let (found, sections') := sections.foldl (fun (found, acc) (k, ls) =>
        if k == pkg.dir then (true, acc ++ [(k, fresh)])
        else (found, acc ++ [(k, ls)])) (false, [])
      let sections' := if found then sections' else sections' ++ [(pkg.dir, fresh)]
      IO.FS.writeFile reportPath (serializeSections header sections')
      IO.println s!"axioms: {pkg.dir}: section updated in {reportPath} (other sections untouched)"
    else
      IO.println s!"axioms: {reportPath} absent — bootstrap it with a full `lake exe gates axioms --write`"
      failed := true
  else
    if ← reportPath.pathExists then
      let (_, sections) := parseSections (← IO.FS.readFile reportPath)
      match sections.find? (·.1 == pkg.dir) with
      | none =>
        IO.println s!"axioms: {pkg.dir}: no section in {reportPath} — \
          run `lake exe gates axioms --package {pkg.dir} --write` and commit"
        failed := true
      | some (_, committed) =>
        if committed != fresh then
          IO.println s!"axioms: {pkg.dir}: section DRIFTED from {reportPath} — \
            the axiom surface changed; run `lake exe gates axioms --package {pkg.dir} --write` and commit"
          failed := true
    else
      IO.println s!"axioms: {reportPath} absent — run `lake exe gates axioms --write` and commit"
      failed := true
  if failed then return 1
  IO.println s!"axioms: {pkg.dir}: clean — every decl's cone inside the allowlist, section in sync"
  return 0

unsafe def run (write : Bool) (pkgName : Option String := none) : IO UInt32 := do
  -- initSearchPath reads LEAN_PATH (`lake exe` supplies gates' dep
  -- closure) + the sysroot; the per-package prepend happens per import.
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  if let some name := pkgName then
    match gatedPackages.find? (·.dir == name) with
    | some pkg => return ← runOne base pkg write
    | none =>
      IO.eprintln s!"axioms: unknown --package '{name}' — gated: \
        {String.intercalate ", " (gatedPackages.map (·.dir)).toList}"
      return 1
  -- no `--package`: the whole-file report (bootstrap / `gates all`).
  let mut reports : Array PkgReport := #[]
  let mut failed := false
  for pkg in gatedPackages do
    let r ← analyzePkg base pkg
    reports := reports.push r
    if ← printReport r then failed := true
  let text := render reports
  if write then
    IO.FS.writeFile reportPath (text ++ "\n")
    IO.println s!"wrote {reportPath}"
  else
    if ← reportPath.pathExists then
      let committed ← IO.FS.readFile reportPath
      if committed != text ++ "\n" then
        IO.println s!"axioms: report DRIFTED from {reportPath} — \
          the axiom surface changed; run `lake exe gates axioms --write` and commit"
        failed := true
    else
      IO.println s!"axioms: {reportPath} absent — run `lake exe gates axioms --write` and commit"
      failed := true
  if failed then return 1
  IO.println "axioms: clean — every decl's cone inside the allowlist, report in sync"
  return 0

end Gates.Axioms

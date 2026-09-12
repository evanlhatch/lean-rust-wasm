/-
LintKit Tests — TestKit-style self-tests for the guestlang linters (no LSpec:
LintKit is core-only, so the driver is a tiny IO assertion harness in the
same +/− control discipline as TestKit.DetSpec).

Mechanism: env-linters do not surface through `#guard_msgs` (they run
post-hoc over oleans, not during elaboration), so this driver replays the
production path — `importModules` the fixture oleans, run the runner,
assert the finding set. Fixtures plant violations (Violations.lean) and
clean code (Clean.lean); every linter gets a positive control (must fire)
and a negative control (must not).
-/
import LintKit

open Lean LintKit

/-- Tiny assertion accumulator (CheckM-style): failures print and are counted. -/
abbrev M := StateRefT (Array String) IO

def check (label : String) (cond : Bool) : M Unit := do
  unless cond do modify (·.push label)
  if cond then IO.println s!"ok: {label}" else IO.eprintln s!"FAIL: {label}"

def findingsFor (fs : Array LintFinding) (linter : Name) : Array Name :=
  fs.filter (·.linter == linter) |>.map (·.decl)

/-- Expected env-linter findings on the fixture closure, per linter. -/
def expected : Array (Name × Array Name) := #[
  (`linter.guestlang.axiomAllowlist, #[
    `LintKit.TestFixtures.Violations.evil,
    `LintKit.TestFixtures.Violations.usesEvil]),
  (`linter.guestlang.recursiveSimpEqns, #[
    `LintKit.TestFixtures.Violations.recNoSimp]),
  (`linter.guestlang.dupDefBodies, #[
    `LintKit.TestFixtures.Violations.dupOne,
    `LintKit.TestFixtures.Violations.dupTwo]),
  (`linter.guestlang.packageNamespace, #[
    `List.badNs,
    `Substrait.strayFromLintKit])
]

unsafe def run : M Unit := do
  LintKit.initLintSearchPath
  Lean.enableInitializersExecution
  let env ← importModules
    #[{ module := `LintKit.TestFixtures.Violations },
      { module := `LintKit.TestFixtures.Clean }]
    {} (trustLevel := 1024) (loadExts := true)
  let roots := #[`LintKit.TestFixtures]
  -- recursiveSimpEqns is default-OFF tree-wide (see its option's comment);
  -- the fixtures enable it via the CLI-override path, which is also the
  -- override path's own test.
  let cfg : DriverConfig := {
    overrides := ({} : NameMap Bool).insert `linter.guestlang.recursiveSimpEqns true }
  let (findings, _) ← (do
      let decls ← packageDecls (← getEnv) roots
      runLintersOnDecls decls cfg).toIO
    { fileName := "<lintkit-tests>", fileMap := default } { env }
  IO.println s!"-- {findings.size} env-linter finding(s) on fixtures:"
  for f in findings do IO.println s!"  {f.linter} {f.decl}"
  for (linter, want) in expected do
    let got := findingsFor findings linter
    for w in want do
      check s!"{linter} flags {w}" (got.contains w)
    -- negative control: nothing beyond the planted set fires
    let extra := got.filter (!want.contains ·)
    check s!"{linter} flags nothing beyond the planted set (extra: {extra})"
      extra.isEmpty
  -- explicit negative controls: the opt-outs and clean decls
  let allFlagged := findings.map (·.decl)
  for n in [`LintKit.TestFixtures.Violations.nativeOk,
            `LintKit.TestFixtures.Violations.evilNolint,
            `LintKit.TestFixtures.Violations.evilSnap,
            `LintKit.TestFixtures.Clean.twoEqTwo,
            `LintKit.TestFixtures.Clean.extOk,
            `LintKit.TestFixtures.Clean.recSimp,
            `LintKit.TestFixtures.Clean.addFortyOne,
            `LintKit.TestFixtures.Clean.addFortyTwo] do
    check s!"no linter flags {n}" (!allFlagged.contains n)
  -- text lints: pure-function +/− controls
  let bare := checkNoLinterDisable "M.lean"
    "set_option linter.guestlang.axiomAllowlist false in\naxiom x : False\n"
  check "noLinterDisable flags a bare set_option opt-out" (bare.size == 1)
  let justifiedSameLine := checkNoLinterDisable "M.lean"
    "set_option linter.guestlang.axiomAllowlist false in -- because test\naxiom x : False\n"
  check "noLinterDisable accepts a same-line because-comment" justifiedSameLine.isEmpty
  let justifiedAbove := checkNoLinterDisable "M.lean"
    "-- off because the kernel accepts this\nset_option linter.foo false in\naxiom x : False\n"
  check "noLinterDisable accepts a previous-line because-comment" justifiedAbove.isEmpty
  let notFalse := checkNoLinterDisable "M.lean"
    "set_option linter.foo true in\ndef x := 1\n"
  check "noLinterDisable ignores `set_option ... true`" notFalse.isEmpty
  let lspecInTests := checkTestImportDiscipline "/pkg/Tests/Main.lean" "import LSpec\n"
  check "testImportDiscipline flags `import LSpec` under Tests/" (lspecInTests.size == 1)
  let testkitInTests := checkTestImportDiscipline "/pkg/Tests/Main.lean" "import TestKit\n"
  check "testImportDiscipline accepts `import TestKit`" testkitInTests.isEmpty
  let lspecInLib := checkTestImportDiscipline "/pkg/Lib.lean" "import LSpec\n"
  check "testImportDiscipline only applies under Tests/" lspecInLib.isEmpty

def main : IO UInt32 := do
  let (_, failures) ← (unsafe run).run #[]
  if failures.isEmpty then
    IO.println "LintKit tests: all green"
    return 0
  IO.eprintln s!"LintKit tests: {failures.size} failure(s)"
  return 1

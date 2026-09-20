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
    `LintKit.TestFixtures.Violations.dupTwo,
    `LintKit.TestFixtures.Violations.dupCrossA,
    `LintKit.TestFixtures.Cross.dupCrossB]),
  (`linter.guestlang.packageNamespace, #[
    `List.badNs,
    `Substrait.strayFromLintKit,
    -- the `@[derived]` pair: the UNSTAMPED twin fires...
    `List.unstampedBad]),
  (`linter.guestlang.guestBan, #[
    `LintKit.TestFixtures.Violations.evilIo,
    `LintKit.TestFixtures.Violations.evilNatArith]),
  (`linter.guestlang.upstreamDup, #[
    `LintKit.TestFixtures.Violations.swapPlanted]),
  (`linter.guestlang.bareChecker, #[
    `LintKit.TestFixtures.Violations.checkNoBridge])
]

unsafe def run : M Unit := do
  LintKit.initLintSearchPath
  Lean.enableInitializersExecution
  let env ← importModules
    #[{ module := `LintKit.TestFixtures.Violations },
      { module := `LintKit.TestFixtures.Clean },
      { module := `LintKit.TestFixtures.Cross },
      { module := `LintKit.TestFixtures.Derived }]
    {} (trustLevel := 1024) (loadExts := true)
  let roots := #[`LintKit.TestFixtures]
  -- recursiveSimpEqns and guestBan are default-OFF tree-wide (see their
  -- options' comments); the fixtures enable them via the CLI-override path,
  -- which is also the override path's own test.
  let cfg : DriverConfig := {
    overrides := ({} : NameMap Bool).insert `linter.guestlang.recursiveSimpEqns true
      |>.insert `linter.guestlang.guestBan true }
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
            -- ...the STAMPED emitted sibling passes (the structural skip —
            -- the set_option packageNamespace ritual's replacement)
            `List.stampedOk,
            `LintKit.TestFixtures.Clean.twoEqTwo,
            `LintKit.TestFixtures.Clean.extOk,
            `LintKit.TestFixtures.Clean.recSimp,
            `LintKit.TestFixtures.Clean.addFortyOne,
            `LintKit.TestFixtures.Clean.addFortyTwo,
            -- upstreamDup non-triviality calibration: the `id` collision is
            -- under the node-count filter
            `LintKit.TestFixtures.Clean.identityPlanted,
            -- bareChecker: the bridge theorem silences the checker
            `LintKit.TestFixtures.Clean.checkWithBridge] do
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
  let lspecInRenamedTests := checkTestImportDiscipline
    "lean/substrait/SubstraitTests/Main.lean" "import LSpec\n"
  check "testImportDiscipline flags LSpec under a renamed <Pkg>Tests/ root"
    (lspecInRenamedTests.size == 1)
  let lspecRelativeTests := checkTestImportDiscipline "Tests/Main.lean" "import LSpec\n"
  check "testImportDiscipline flags LSpec under a relative Tests/" (lspecRelativeTests.size == 1)
  let testkitInTests := checkTestImportDiscipline "/pkg/Tests/Main.lean" "import TestKit\n"
  check "testImportDiscipline accepts `import TestKit`" testkitInTests.isEmpty
  let lspecInLib := checkTestImportDiscipline "/pkg/Lib.lean" "import LSpec\n"
  check "testImportDiscipline only applies under Tests/" lspecInLib.isEmpty
  let lspecCall := checkTestImportDiscipline "/pkg/Tests/Main.lean"
    "def main := LSpec.lspecIO s []\n"
  check "testImportDiscipline flags direct lspecIO use" (lspecCall.size == 1)
  let testkitCall := checkTestImportDiscipline "/pkg/Tests/Main.lean"
    "def main := TestKit.mainOfSuites s\n"
  check "testImportDiscipline accepts TestKit drivers" testkitCall.isEmpty
  -- noNewPartial: legacy allowance + new-site flagging (+ the renamed
  -- test-root exemption — the single-lake path shape)
  let legacyOk := checkNoNewPartial "lean/wasm-backend/WasmBackend.lean"
    "partial def a := 1\npartial def b := 2\n"
  check "noNewPartial accepts sites within the legacy allowance" legacyOk.isEmpty
  let testsExempt := checkNoNewPartial "lean/substrait/SubstraitTests/Main.lean"
    "partial def x := 1\n"
  check "noNewPartial exempts a renamed <Pkg>Tests/ file" testsExempt.isEmpty
  let legacyOver := checkNoNewPartial "lean/wasm-backend/WasmBackend.lean"
    (String.intercalate "" (List.replicate 10 "partial def x := 1\n"))
  check "noNewPartial flags overage past the legacy allowance" (legacyOver.size == 1)
  let newSite := checkNoNewPartial "lean/foo/Foo.lean" "partial def x := 1\n"
  check "noNewPartial flags a new file's partial def" (newSite.size == 1)
  let partialComment := checkNoNewPartial "lean/foo/Foo.lean"
    "/- partial def is discussed here -/\ndef x := 1\n"
  check "noNewPartial ignores comments" partialComment.isEmpty
  -- noReprInEmit
  let reprInEmit := checkNoReprInEmit "lean/schema-lang/SchemaLang/Emit/Wit.lean"
    "def f := repr x\n"
  check "noReprInEmit flags repr in an emitter" (reprInEmit.size == 1)
  let reprComment := checkNoReprInEmit "lean/schema-lang/SchemaLang/Emit/Wit.lean"
    "-- never `repr` here\ndef f := x\n"
  check "noReprInEmit ignores comments" reprComment.isEmpty
  let reprElsewhere := checkNoReprInEmit "lean/foo/Foo.lean" "def f := repr x\n"
  check "noReprInEmit only applies under Emit/" reprElsewhere.isEmpty
  -- noFormatInDebug
  let fmtInDebug := checkNoFormatInDebug "lean/schema-lang/SchemaLang/Debug.lean"
    "def f := fformat.pretty\n"
  check "noFormatInDebug flags .pretty in Debug.lean" (fmtInDebug.size == 1)
  let fmtElsewhere := checkNoFormatInDebug "lean/foo/Foo.lean"
    "def f := fformat.pretty\n"
  check "noFormatInDebug only applies to Debug.lean" fmtElsewhere.isEmpty
  -- coreHasNoClaim
  let bareClaim := checkCoreHasNoClaim "M.lean" "/-- helper (core has no `foo`) -/\ndef x := 1\n"
  check "coreHasNoClaim flags an uncited claim" (bareClaim.size == 1)
  let citedClaim := checkCoreHasNoClaim "M.lean"
    "/-- helper (core has no `foo` — checked the 4.33 toolchain src) -/\ndef x := 1\n"
  check "coreHasNoClaim accepts a cited claim" citedClaim.isEmpty
  let codeMention := checkCoreHasNoClaim "M.lean" "def coreHasNo := 1\n"
  check "coreHasNoClaim ignores code" codeMention.isEmpty
  let multilineCite := checkCoreHasNoClaim "M.lean"
    "/-- helper (core has no `foo` —\n    checked the toolchain) -/\ndef x := 1\n"
  check "coreHasNoClaim accepts a citation on the next docstring line" multilineCite.isEmpty
  let claimInString := checkCoreHasNoClaim "M.lean"
    "def m := \"core has no documented behavior here\"\n"
  check "coreHasNoClaim ignores string literals" claimInString.isEmpty
  let commentOpenerInString := checkStaleNotesPath "M.lean"
    "def a := \"/-\"\ndef b := \"notes/lean/x.md\"\n"
  check "comment scanner ignores comment openers inside strings" commentOpenerInString.isEmpty
  let nolintInString := checkNolintReason "M.lean"
    "def m := m!\"opt out with @[nolint linter.guestlang.foo]\"\n"
  check "nolintReason ignores attribute syntax inside string literals" nolintInString.isEmpty
  -- staleNotesPath
  let staleRef := checkStaleNotesPath "M.lean" "/- see notes/lean/lean-v3.md -/\ndef x := 1\n"
  check "staleNotesPath flags notes/lean/" (staleRef.size == 1)
  let liveRef := checkStaleNotesPath "M.lean" "/- see notes/vision.md -/\ndef x := 1\n"
  check "staleNotesPath accepts real notes/ paths" liveRef.isEmpty
  -- nolintReason
  let bareNolint := checkNolintReason "M.lean" "@[nolint linter.guestlang.foo]\ndef x := 1\n"
  check "nolintReason flags a bare opt-out" (bareNolint.size == 1)
  let reasonedNolint := checkNolintReason "M.lean"
    "@[nolint linter.guestlang.foo \"because the test\", linter.guestlang.bar \"why\"]\ndef x := 1\n"
  check "nolintReason accepts a reasoned opt-out" reasonedNolint.isEmpty
  -- importBan (the single-lake discipline rows) — positive control: a heavy
  -- root under a banned prefix; negative: the same import outside the prefix,
  -- a clean root under the prefix, and a name-boundary near-miss (MathlibX).
  let bannedImport := checkImportBan "lean/codegen-core/CodegenCore/Emit/Rust.lean"
    "import Mathlib.Data.Nat.Defs\n"
  check "importBan flags Mathlib under lean/codegen-core/" (bannedImport.size == 1)
  let bannedChild := checkImportBan "lean/substrait/Substrait.lean"
    "import Dbsp.Operators\n"
  check "importBan flags a banned-root CHILD (Dbsp.Operators)" (bannedChild.size == 1)
  let outsidePrefix := checkImportBan "lean/schema-lang/SchemaLang.lean"
    "import Mathlib.Data.Nat.Defs\n"
  check "importBan ignores files outside every banned prefix" outsidePrefix.isEmpty
  let cleanImport := checkImportBan "lean/codegen-core/CodegenCore/Kit.lean"
    "import TestKit\n"
  check "importBan accepts TestKit under lean/codegen-core/" cleanImport.isEmpty
  let nearMiss := checkImportBan "lean/TestKit/TestKit.lean"
    "import MathlibX\n"
  check "importBan is name-boundary exact (MathlibX ≠ Mathlib)" nearMiss.isEmpty
  let commentedImport := checkImportBan "lean/LintKit/LintKit/Basic.lean"
    "-- import Mathlib.Data.Nat.Defs\n"
  check "importBan ignores commented-out imports" commentedImport.isEmpty
  -- srcRootFor: the --src-root mapping lookup the text-lint driver uses
  -- (first root-prefixing mapping wins; none = the cwd fallback).
  let mapped := srcRootFor #[(`EdgePython, "lean/edgepython")] `EdgePython.Parity
  check "srcRootFor maps a root-prefixed module" (mapped == some "lean/edgepython")
  let unmapped := srcRootFor #[(`EdgePython, "lean/edgepython")] `Tests.Main
  check "srcRootFor falls through for a non-matching module" (unmapped == none)
  let second := srcRootFor #[(`A, "dirA"), (`Tests, "lean/ledger")] `Tests.Main
  check "srcRootFor picks the first matching mapping" (second == some "lean/ledger")
  -- unregisteredRoundtrip: both directions + no registration vocabulary =
  -- a finding; either direction alone, or a registered pair, is silent;
  -- Tests files are exempt.
  let codecBoth := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def encodeFoo : Foo → List UInt8 := Foo.toBytes\ndef decodeFoo : List UInt8 → Option Foo := Foo.ofBytes\n"
  check "unregisteredRoundtrip flags an enc/dec pair without registration"
    (codecBoth.size == 1)
  let codecEncOnly := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def encodeFoo : Foo → List UInt8 := Foo.toBytes\n"
  check "unregisteredRoundtrip is silent on encoder-only" codecEncOnly.isEmpty
  let codecDecOnly := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def parseFoo : String → Option Foo := some ∘ Foo.parse\n"
  check "unregisteredRoundtrip is silent on decoder-only" codecDecOnly.isEmpty
  let codecRegistered := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def encodeFoo : Foo → List UInt8 := Foo.toBytes\ndef decodeFoo : List UInt8 → Option Foo := Foo.ofBytes\ninstance : PartialIso (List UInt8) Foo := ⟨encodeFoo, decodeFoo, by intro a; rfl⟩\n"
  check "unregisteredRoundtrip accepts a registered codec" codecRegistered.isEmpty
  let codecInTests := checkUnregisteredRoundtrip "lean/x/XTests/Main.lean"
    "def encodeFoo : Foo → List UInt8 := Foo.toBytes\ndef decodeFoo : List UInt8 → Option Foo := Foo.ofBytes\n"
  check "unregisteredRoundtrip exempts Tests files" codecInTests.isEmpty
  let codecRenderParse := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def renderRow : Row → String := toString\ndef parseRow : String → Option Row := none\n"
  check "unregisteredRoundtrip catches render/parse spellings" (codecRenderParse.size == 1)
  -- didyoumeanDiscipline: an unknown-name rejection in a file with none of
  -- the machinery; the file-level exemption when the machinery appears;
  -- non-error lines and non-backticked payloads are silent.
  let dymBare := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throwError s!\"unknown slot `{got}` for this item\"\n"
  check "didyoumeanDiscipline flags a bare unknown-name rejection" (dymBare.size == 1)
  let dymUsing := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throwError (unknownNameMessage ctx got what legal)\n"
  check "didyoumeanDiscipline exempts a file using the machinery" dymUsing.isEmpty
  let dymSuffix := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throwError s!\"unknown slot `{got}` — did you mean: {c}?\"\n"
  check "didyoumeanDiscipline exempts the did-you-mean suffix" dymSuffix.isEmpty
  let dymComment := checkDidyoumeanDiscipline "lean/x/X.lean"
    "-- unknown slots live here\ndef x := 1\n"
  check "didyoumeanDiscipline ignores comments" dymComment.isEmpty
  let dymNoBacktick := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throw s!\"oracle row: unknown fn '{fn}'\"\n"
  check "didyoumeanDiscipline requires a backticked payload" dymNoBacktick.isEmpty

def main : IO UInt32 := do
  let (_, failures) ← (unsafe run).run #[]
  if failures.isEmpty then
    IO.println "LintKit tests: all green"
    return 0
  IO.eprintln s!"LintKit tests: {failures.size} failure(s)"
  return 1

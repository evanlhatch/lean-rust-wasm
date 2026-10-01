/-
LintKitTests.Main — the linters' teeth (notes/v3/15-patterns.md #5:
every linter gets a POSITIVE control that must fire and a MANDATORY
negative control that must not).

Three layers:

1. PURE teeth — data-level verdict functions called directly on planted
   inputs (the text lints, `coneVerdict`/`coneOffences` + the cone order,
   `srcRootFor`, the census options' defaults).
2. FIXTURE env teeth — `LintKitFixtures.Violations` plants one violation
   per linter (the positive controls); `LintKitFixtures.Clean` carries
   the compliant shapes (the mandatory negative controls). The driver
   replays the production path over the fixture root and asserts the
   exact finding set: every planted violation fires, NOTHING ELSE does.
3. GATE teeth — the `@[guest]`/`@[guest_std]` attributes run at
   elaboration; the planted `@[guest]` violation is captured by
   `#guard_msgs` in the fixture module (the gate's error IS the tooth),
   and the marked-clean decl is pinned into the guest-mark registry.

The fixture root `LintKitFixtures` is deliberately not in the lintkit
exe's gated roots — planted findings never leak into the tree run.
Evidence, not architecture — the five-question blocks live in the
modules under test.
-/
import LintKit.Runner
import LintKitTests.Violator
import LintKitFixtures.Violations
import LintKitFixtures.Clean
import LintKitFixturesUntabled.Violator

open Lean LintKit LintKit.GuestGate

/-- Tiny assertion accumulator (CheckM-style): failures print and are
counted. -/
abbrev M := StateRefT (Array String) IO

def check (label : String) (cond : Bool) : M Unit := do
  unless cond do modify (·.push label)
  if cond then IO.println s!"ok: {label}" else IO.eprintln s!"FAIL: {label}"

def findingsFor (fs : Array LintFinding) (linter : Name) : Array Name :=
  fs.filter (·.linter == linter) |>.map (·.decl)

/-- zeroCitation's citation source: a REAL constant mention of
`LintKitFixtures.Clean.citedFixture` from outside its module (this is a
Tests module, exempt from the lint itself). -/
theorem citeCitedFixture : 1 < 2 := LintKitFixtures.Clean.citedFixture

-- zeroCitation's test-PIN tooth: `#print axioms` leaves no constant in
-- the environment, so `LintKitFixtures.Violations.pinnedFixture` would
-- read as uncited — the source scan of this Tests module must see the
-- pin and stay quiet.
#print axioms LintKitFixtures.Violations.pinnedFixture

/-- The pure verdict teeth for the cone linter. -/
def checkPureTeeth : Bool :=
  -- the cone order: C0 ≤ everything; nothing is ≤ C0 but C0
  ((Cone.c0machinery : Cone) ≤ .c3app)
    && ((Cone.c0machinery : Cone) ≤ .c0machinery)
    && !((Cone.c1domain : Cone) ≤ .c0machinery)
    && !((Cone.c3app : Cone) ≤ .c2theory)
  -- POSITIVE: the Mathlib/Batteries ban (06 §8) — both roots, and at
  -- any depth below them (importer roots: LintKitTests C0, SchemaTests C1)
  && (!(coneOffences `LintKitTests #[`Mathlib.Algebra.Group]).isEmpty)
  && (!(coneOffences `SchemaTests #[`Batteries.Data.List.Basic]).isEmpty)
  -- POSITIVE: cone-high project root (SchemaCore is C1) — ROOTED names
  && (!(coneOffences `LintKitTests #[`SchemaCore]).isEmpty)
  -- NEGATIVE: cone-low imports pass (C1 on Kit)
  && (coneOffences `SchemaTests #[`Kit, `LintKit]).isEmpty
  -- NEGATIVE: same-cone imports pass
  && (coneOffences `LintKitTests #[`TextKit, `Kit]).isEmpty
  -- NEGATIVE: the Lean core root passes the C0 ban
  && (coneOffences `LintKitTests #[`Lean.Elab.Tactic]).isEmpty
  -- NEGATIVE: the host-side READER exemption — Gates reads what it
  -- gates without firing; the reader keeps its Mathlib/Batteries ban
  && (coneOffences `Gates #[`SchemaCore]).isEmpty
  -- POSITIVE: the LOUD GAP — an untabled importer root is a finding
  -- (`ConeVerdict.untabled`), never a silent pass: this is the root-
  -- cause fix for the landed-library-forgot-its-row lapse. The tabled
  -- import case stays `.offences` (empty = clean), even with no imports.
  && (coneVerdict `LintKitFixturesUntabled #[`Kit]
        == .untabled `LintKitFixturesUntabled)
  && (coneVerdict `LintKitFixturesUntabled #[]
        == .untabled `LintKitFixturesUntabled)
  && (coneVerdict `Kit #[] == .offences #[])
  && (coneVerdict `SchemaTests #[`Kit] == .offences #[])

/-- The pure teeth for the text lints (positive + negative controls over
planted source text). -/
def checkTextTeeth : M Unit := do
  -- noNewPartial: a new file fires; the seeded allowance stays quiet;
  -- the overage fires; Tests files are exempt; comments are ignored.
  let newSite := checkNoNewPartial "lean/foo/Foo.lean" "partial def x := 1\n"
  check "noNewPartial flags a new file's partial def" (newSite.size == 1)
  let seeded := checkNoNewPartial
    "schemacore/SchemaCore/Describe.lean"
    "partial def a := 1\npartial def b := 2\npartial def c := 3\n"
  check "noNewPartial accepts sites within the seeded allowance" seeded.isEmpty
  let overage := checkNoNewPartial
    "schemacore/SchemaCore/Describe.lean"
    (String.intercalate "" (List.replicate 4 "partial def x := 1\n"))
  check "noNewPartial flags overage past the allowance" (overage.size == 1)
  let testsExempt := checkNoNewPartial "lean/foo/FooTests/Main.lean" "partial def x := 1\n"
  check "noNewPartial exempts a <Pkg>Tests/ file" testsExempt.isEmpty
  let partialComment := checkNoNewPartial "lean/foo/Foo.lean"
    "/- partial def is discussed here -/\ndef x := 1\n"
  check "noNewPartial ignores comments" partialComment.isEmpty
  -- nolintReason: a bare opt-out fires; a reasoned one and a string-
  -- literal mention are quiet.
  let bareNolint := checkNolintReason "M.lean" "@[nolint linter.guestlang.foo]\ndef x := 1\n"
  check "nolintReason flags a bare opt-out" (bareNolint.size == 1)
  let reasonedNolint := checkNolintReason "M.lean"
    "@[nolint linter.guestlang.foo \"because the test\", linter.guestlang.bar \"why\"]\ndef x := 1\n"
  check "nolintReason accepts a reasoned opt-out" reasonedNolint.isEmpty
  let nolintInString := checkNolintReason "M.lean"
    "def m := m!\"opt out with @[nolint linter.guestlang.foo]\"\n"
  check "nolintReason ignores attribute syntax inside string literals" nolintInString.isEmpty
  -- unregisteredRoundtrip: both directions + no registration = a finding;
  -- either direction alone, or a registered pair (vocabulary OR a proved
  -- round-trip law), is silent; Tests files are exempt.
  let codecBoth := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def encFoo : Foo → List UInt8 := Foo.toBytes\ndef decFoo : List UInt8 → Option Foo := Foo.ofBytes\n"
  check "unregisteredRoundtrip flags an enc/dec pair without registration"
    (codecBoth.size == 1)
  let codecEncOnly := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def encFoo : Foo → List UInt8 := Foo.toBytes\n"
  check "unregisteredRoundtrip is silent on encoder-only" codecEncOnly.isEmpty
  let codecDecOnly := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def parseFoo : String → Option Foo := none\n"
  check "unregisteredRoundtrip is silent on decoder-only" codecDecOnly.isEmpty
  let codecVocab := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def encFoo : Foo → List UInt8 := Foo.toBytes\ndef decFoo : List UInt8 → Option Foo := Foo.ofBytes\ninstance : Codec (List UInt8) Foo := ⟨encFoo, decFoo, by intro a; rfl⟩\n"
  check "unregisteredRoundtrip accepts a codec-vocabulary registration" codecVocab.isEmpty
  let codecLaw := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def encFoo : Foo → List UInt8 := Foo.toBytes\ndef decFoo : List UInt8 → Option Foo := Foo.ofBytes\ntheorem decFoo_encFoo_append : True := trivial\n"
  check "unregisteredRoundtrip accepts a proved round-trip law" codecLaw.isEmpty
  let codecRenderParse := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def renderRow : Row → String := toString\ndef parseRow : String → Option Row := none\n"
  check "unregisteredRoundtrip catches render/parse spellings" (codecRenderParse.size == 1)
  let codecInTests := checkUnregisteredRoundtrip "lean/x/XTests/Main.lean"
    "def encFoo : Foo → List UInt8 := Foo.toBytes\ndef decFoo : List UInt8 → Option Foo := Foo.ofBytes\n"
  check "unregisteredRoundtrip exempts Tests files" codecInTests.isEmpty
  let codecDeclExcl := checkUnregisteredRoundtrip "lean/x/X.lean"
    "def declAnchor : Row → Nat := 0\ndef declParse : Nat → Nat := id\n"
  check "unregisteredRoundtrip honors the decl* exclusions" codecDeclExcl.isEmpty
  -- didyoumeanDiscipline: an unknown-name rejection in a file with none
  -- of the machinery; the file-level exemption when the machinery appears;
  -- non-error lines, comments, and non-backticked payloads are silent.
  let dymBare := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throwError s!\"unknown slot `{got}` for this item\"\n"
  check "didyoumeanDiscipline flags a bare unknown-name rejection" (dymBare.size == 1)
  let dymUsing := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throwError (unknownNameMessage ctx got what legal)\n"
  check "didyoumeanDiscipline exempts a file using the machinery" dymUsing.isEmpty
  let dymSuffix := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throwError s!\"unknown slot `{got}` — did you mean: {c}?\"\n"
  check "didyoumeanDiscipline exempts the did-you-mean suffix" dymSuffix.isEmpty
  let dymKitSuggest := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throwError s!\"unknown `{got}`\" ++ Kit.suggestSuffix got legal\n"
  check "didyoumeanDiscipline exempts the Kit.suggest spelling" dymKitSuggest.isEmpty
  let dymComment := checkDidyoumeanDiscipline "lean/x/X.lean"
    "-- unknown slots live here\ndef x := 1\n"
  check "didyoumeanDiscipline ignores comments" dymComment.isEmpty
  let dymNoBacktick := checkDidyoumeanDiscipline "lean/x/X.lean"
    "throw s!\"oracle row: unknown fn '{fn}'\"\n"
  check "didyoumeanDiscipline requires a backticked payload" dymNoBacktick.isEmpty
  -- noLinterSetOption: the `false` ban fires; the enable, the non-linter
  -- set_option, comments, and string literals are quiet; Tests files are
  -- exempt (the fixtures' enable-shape is the negative control's own form).
  let lsoBan := checkNoLinterSetOption "lean/x/X.lean"
    "set_option linter.guestlang.bareChecker false in\ndef x := 1\n"
  check "noLinterSetOption flags the linter-silencing set_option" (lsoBan.size == 1)
  let lsoEnable := checkNoLinterSetOption "lean/x/X.lean"
    "set_option linter.guestlang.decideFirst true in\ndef x := 1\n"
  check "noLinterSetOption is quiet on an ENABLE" lsoEnable.isEmpty
  let lsoNonLinter := checkNoLinterSetOption "lean/x/X.lean"
    "set_option maxHeartbeats 0 in\ndef x := 1\n"
  check "noLinterSetOption is quiet on a non-linter set_option" lsoNonLinter.isEmpty
  let lsoComment := checkNoLinterSetOption "lean/x/X.lean"
    "-- set_option linter.guestlang.bareChecker false\ndef x := 1\n"
  check "noLinterSetOption ignores comments" lsoComment.isEmpty
  let lsoTests := checkNoLinterSetOption "lean/x/XTests/Main.lean"
    "set_option linter.guestlang.bareChecker false in\ndef x := 1\n"
  check "noLinterSetOption exempts Tests files" lsoTests.isEmpty
  -- bareExample: a new file's bare example fires; the seeded allowance
  -- stays quiet; the overage fires; Tests files are exempt; a named decl
  -- mentioning example and a comment are quiet.
  let beNew := checkBareExample "lean/x/X.lean" "example : 1 = 1 := rfl\n"
  check "bareExample flags a source root's bare example" (beNew.size == 1)
  let beSeeded := checkBareExample "schemacore/SchemaCore/RowVals.lean"
    (String.intercalate "" (List.replicate 2 "example : 1 = 1 := rfl\n"))
  check "bareExample accepts sites within the seeded allowance" beSeeded.isEmpty
  let beOver := checkBareExample "schemacore/SchemaCore/RowVals.lean"
    (String.intercalate "" (List.replicate 3 "example : 1 = 1 := rfl\n"))
  check "bareExample flags overage past the allowance" (beOver.size == 1)
  let beTests := checkBareExample "lean/x/XTests/Main.lean" "example : 1 = 1 := rfl\n"
  check "bareExample exempts Tests files" beTests.isEmpty
  let beNamed := checkBareExample "lean/x/X.lean" "def examples : Nat := 1\n"
  check "bareExample is quiet on a name mentioning example" beNamed.isEmpty
  let beComment := checkBareExample "lean/x/X.lean" "-- example : 1 = 1\ndef x := 1\n"
  check "bareExample ignores comments" beComment.isEmpty
  -- srcRootFor: the first root-prefixing mapping wins; none falls through.
  let mapped := srcRootFor #[(`Kit, "kit"), (`KitMore, "other")] `Kit.CodeRegistry
  check "srcRootFor maps a root-prefixed module" (mapped == some "kit")
  let unmapped := srcRootFor #[(`Kit, "kit")] `TextKit.Error
  check "srcRootFor falls through for a non-matching module" (unmapped == none)

/-- The fixture closure's EXPECTED findings, per linter: every planted
violation fires, and NOTHING ELSE does (the negative controls live in
LintKitFixtures.Clean). -/
def fixtureExpected : Array (Name × Array Name) := #[
  (`linter.guestlang.bareChecker, #[`LintKitFixtures.Violations.checkNoBridge]),
  (`linter.guestlang.verdictCtors, #[`LintKitFixtures.Violations.badVerdict]),
  (`linter.guestlang.guestBan, #[
    `LintKitFixtures.Violations.evilIo,
    `LintKitFixtures.Violations.evilNatArith,
    -- the gate-rejected def is a census finding TOO (the two mounts see
    -- the same ban at both enforcement levels)
    `LintKitFixtures.Violations.guestBad]),
  (`linter.guestlang.recursiveSimpEqns, #[`LintKitFixtures.Violations.recNoSimp]),
  (`linter.guestlang.decideFirst, #[`LintKitFixtures.Violations.colorNeHand]),
  (`linter.guestlang.evidenceRedundancy, #[
    -- CLASS A: the re-proof of the carried law
    `LintKitFixtures.Violations.violRoundtrip,
    -- CLASS B: both faces of the weaker-than-kernel row
    `LintKitFixtures.Violations.violSweepObl,
    `LintKitFixtures.Violations.violSweepDischarged]),
  (`linter.guestlang.graduation, #[`LintKitFixtures.Violations.parityCodec]),
  (`linter.guestlang.zeroCitation, #[
    -- the planted zero-citation theorem
    `LintKitFixtures.Violations.uncitedFixture,
    -- TRUE positives in the control module: theorems cited nowhere
    -- outside their module — correct findings, not false ones (the
    -- zeroCitation pins live in LintKitTests.Main)
    `LintKitFixtures.Violations.colorNeHand,
    `LintKitFixtures.Violations.violRoundtrip,
    `LintKitFixtures.Clean.checkWithBridge_true_of_lt,
    `LintKitFixtures.Clean.colorNeDecide,
    `LintKitFixtures.Clean.shadeRfl,
    `LintKitFixtures.Clean.cleanRoundtrip]),
  (`linter.guestlang.axiomAllowlist, #[]),
  (`linter.guestlang.dupDefBodies, #[]),
  (`linter.guestlang.packageNamespace, #[])
]

unsafe def run : M UInt32 := do
  unless checkPureTeeth do
    IO.println "lintkit-tests: PURE TEETH FAILED (coneOffences / cone order)"
    return 1
  checkTextTeeth
  -- the census linters' default-OFF pin (the `default_false` registration)
  check "recursiveSimpEqns is default-OFF (census)"
    (!(linter.guestlang.recursiveSimpEqns).defValue)
  check "guestBan is default-OFF (census)" (!(linter.guestlang.guestBan).defValue)
  check "decideFirst is default-OFF (census)"
    (!(linter.guestlang.decideFirst).defValue)
  -- PROMOTED (the codec→iso constructor landed; every census finding
  -- graduated): the graduation linter is a GATE now.
  check "graduation is default-ON (gate — the promotion)"
    ((linter.guestlang.graduation).defValue)
  -- the enforcement wave's two text lints: the bypass ban + the example
  -- blind spot are GATE lints (default-ON), not censuses.
  check "noLinterSetOption is default-ON (gate)"
    ((linter.guestlang.noLinterSetOption).defValue)
  check "bareExample is default-ON (gate)"
    ((linter.guestlang.bareExample).defValue)
  check "zeroCitation is default-OFF (census)"
    (!(linter.guestlang.zeroCitation).defValue)
  check "evidenceRedundancy is default-OFF (census)"
    (!(linter.guestlang.evidenceRedundancy).defValue)
  check "bareChecker is default-ON (gate)"
    ((linter.guestlang.bareChecker).defValue)
  check "verdictCtors is default-ON (gate)" ((linter.guestlang.verdictCtors).defValue)

  LintKit.initLintSearchPath
  Lean.enableInitializersExecution
  let env ← importModules #[{ module := `LintKitTests.Main }]
      {} (trustLevel := 1024) (loadExts := true)

  -- ENV teeth, layer 1: the CONE linter over this test root — exactly one
  -- finding, at the planted violator LintKitTests.Violator; compliant
  -- modules clean.
  let (coneFindings, _) ← (LintKit.lintModules #[`LintKitTests.Main] {}).toIO
    { fileName := "<lintkit-tests>", fileMap := default } { env }
  check "cone linter: exactly 1 finding at the planted violator"
    (coneFindings.size == 1
      && coneFindings.all fun f => f.decl == `LintKitTests.Violator)
  for f in coneFindings do
    IO.println s!"  [cone] {f.decl}"

  -- ENV teeth, layer 1b: the LOUD GAP — the fixture module whose root
  -- is deliberately untabled fires exactly the cone-gap finding (the
  -- pre-fix linter returned #[] here — the silent lapse this kills).
  let (gapFindings, _) ← (LintKit.lintModules
      #[`LintKitFixturesUntabled.Violator] {}).toIO
    { fileName := "<lintkit-tests>", fileMap := default } { env }
  check "cone linter: the untabled fixture root fires exactly 1 finding"
    (gapFindings.size == 1
      && gapFindings.all fun f => f.linter == `linter.guestlang.coneImports
        && f.decl == `LintKitFixturesUntabled.Violator)
  for f in gapFindings do
    IO.println s!"  [cone-gap] {f.decl}"

  -- ENV teeth, layer 1c: the ONE-ENVELOPE adapter (B1, 05 §4) — every
  -- finding's Diag carries the linter's registry-allocated LK code and
  -- the VERBATIM message (the render face enriches, never rewrites);
  -- the negative control is the verbatim-message pin (no re-rendering
  -- regression) + the code's linter mapping (not the catch-all LK0000).
  check "cone finding's diag carries the LK code + the verbatim message"
    (coneFindings.all fun f => f.diag.code == ⟨"LK0011"⟩
      && f.diag.message == f.message
      && f.diag.severity == .warning)
  check "the catch-all LK0000 is NOT on the registered linters' path"
    (linterCode `linter.guestlang.coneImports != ⟨"LK0000"⟩
      && linterCode `linter.guestlang.nope == ⟨"LK0000"⟩)
  check "the text-lint diag carries the site label"
    ((LintKit.textDiag `linter.guestlang.noNewPartial "a.lean" 7 "m").context
      == [{ name := "a.lean", detail := "7" }])

  -- ENV teeth, layer 2: the fixture closure — census linters enabled via
  -- the CLI-override path (which is the override path's own test).
  let cfg : DriverConfig := {
    overrides := ({} : NameMap Bool).insert `linter.guestlang.recursiveSimpEqns true
      |>.insert `linter.guestlang.guestBan true
      |>.insert `linter.guestlang.decideFirst true
      |>.insert `linter.guestlang.graduation true
      |>.insert `linter.guestlang.zeroCitation true
      |>.insert `linter.guestlang.evidenceRedundancy true }
  let (findings, _) ← (LintKit.lintModules #[`LintKitFixtures.Violations] cfg).toIO
    { fileName := "<lintkit-tests>", fileMap := default } { env }
  IO.println s!"-- {findings.size} fixture finding(s):"
  for f in findings do
    IO.println s!"  {f.linter} {f.decl}"
  for (linter, want) in fixtureExpected do
    let got := findingsFor findings linter
    for w in want do
      check s!"{linter} flags {w}" (got.contains w)
    -- negative control: nothing beyond the planted set fires
    let extra := got.filter (!want.contains ·)
    check s!"{linter} flags nothing beyond the planted set (extra: {extra})"
      extra.isEmpty

  -- GATE teeth: the planted `@[guest]` violation was rejected at
  -- elaboration (the #guard_msgs pin in the fixture module); the clean
  -- decl's mark landed in the guest-mark registry.
  let marks := guestMarkedDecls env
  check "guest gate: Clean.guestOk's mark is in the registry"
    (marks.contains `LintKitFixtures.Clean.guestOk)
  check "guest gate: the rejected decl is NOT marked"
    (!marks.contains `LintKitFixtures.Violations.guestBad)

  if (← get).isEmpty then
    IO.println "lintkit-tests: teeth green"
    return 0
  return 1

unsafe def main : IO UInt32 := do
  let (code, failures) ← (unsafe run).run #[]
  unless failures.isEmpty do
    IO.eprintln s!"lintkit-tests: {failures.size} failure(s)"
    for f in failures do IO.eprintln s!"  FAILED: {f}"
  return code

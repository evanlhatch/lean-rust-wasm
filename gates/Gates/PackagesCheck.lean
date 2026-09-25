/-
Gates.PackagesCheck — the gated-table drift guard
(`gates packages-check`; the re-audit's finding: the gated set lived in
TWO tables — this module's Packages.gatedPackages and the lint driver's
hand-copied roots — and they disagreed, the newest lanes gated by
neither).

The single source is `Gates.Packages.gatedPackages` — every consumer
folds it (the lint driver's default mode, the axiom sweep, the
kernel-check replay's srcDirs, the docs-check envs, the impact core's
gated test). This gate guards the source itself against the LAKEFILE —
the cone-table's loud-gap precedent: a landed library without its gates
row passed every gate silently, which is exactly the lapse the table
exists to prevent. Three findings (ctors, never strings — 09 §8):

1. UNGATED — a lakefile `[[lean_lib]]` with no table row. THE loud gap:
   a new library that forgets its row fails CI here, not silently.
1b. UNGATEDROOT — a lakefile lib root missing from its row's `roots`
   (the root-level face of the same agreement: the row under-declares,
   the modules escape the per-root sweeps while LOOKING covered).
2. STALE — a table row whose `dir` names no lakefile library (the row
   outlived its lib — the drift in the deleted direction).
3. NOSOURCE — a row root with no source file under its row's srcDir
   (a typo'd root sweeps nothing — the silent-vacuity face of the same
   lapse).
4. TESTGHOST / UNTESTEDEXE — the justfile's `test_libs` list × the
   lakefile's `[[lean_exe]]` rows, both directions: a `Tests`-suffixed
   exe missing from `test_libs` is a test `just test` never runs
   (builds ≠ tests); an entry naming no exe is a typo'd test loop
   step. (The convention is the classification: test exes are the
   `<Lib>Tests` names; the drivers/regen exes — `gates`, `lintkit`,
   `wasmgen`, … — are deliberately hand-run, never test_libs rows.)
5. CONEUNTABLED / CONEGHOST — the cone table (LintKit.Cone.coneTable,
   consumed as DATA — the registry-gate enumeration face) × the gated
   table, both directions: a row root whose getRoot has no cone row is
   the loud gap (the module escapes the cone rule silently — 06 §8's
   lapse, caught HERE too, not only at lint time); a cone row with no
   source file or module directory under any lakefile srcDir is the
   row outliving its code (the deleted-direction drift).

The lakefile read is a CONSERVATIVE line scan (the
CodeRegistryCheck's stringLiterals discipline): `[[lean_lib]]` block
starts + the `name = "…"` / `srcDir = "…"` rows; comments skipped; any
other `[[…]]` block (`[[lean_exe]]`, `[[require]]`) ends the current
lib. An over-approximation cannot hide a library (a lib block whose
name row is missed is impossible — the name row is the block's first
field by convention and the scan reads every line).

The negative control (mandatory, 09 §8): the verdict MUST fire all
three findings on a fixture pair missing them, and MUST stay silent on
an agreeing pair — a broken guard fails closed.

The five questions (notes/v3/01-core.md):
- root: Universe — the table × lakefile agreement as decided data.
- carrier grade: none — a finite table's decidable agreement.
- spine reading: the artifact stage's check face over the one source
(the table) against the one build shape (the lakefile).
- ladder rung: rung 1/decide — every finding decided.
- gate row: the packages-check row itself.
-/
import Lean
import LintKit
import Gates.Packages

namespace Gates.PackagesCheck

/-! ## The lakefile scan (the conservative line walk) -/

/-- One lakefile library row (the scan's product): the lib name + its
    srcDir. -/
structure LakeLib where
  name : String
  srcDir : String
  /-- The lakefile row's declared `roots` (the root-level check face:
    a root declared here but missing from the table row escapes the
    per-root sweeps). `[]` when the row declares none — a conservative
    default that cannot hide a library, only weaken its root check. -/
  roots : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- The value of a `key = "value"` row, as data (the first chunk before
    the closing quote); `none` when the line is not that row. -/
def strValue (key line : String) : Option String :=
  match line.trimAscii.toString.dropPrefix? (key ++ " = \"") with
  | some rest => (rest.toString.splitOn "\"").head?
  | none => none

/-- The inside-quote chunks of a line (the items of a `roots = ["a", …]`
    row): `splitOn "\""` alternates outside/inside — the odd positions
    ARE the items (the conservative string-literal discipline: the text
    between the quotes is data, everything around it is syntax). -/
def quotedItems (s : String) : List String :=
  let rec loop : Bool → List String → List String
    | _, [] => []
    | true, _ :: cs => loop false cs   -- an outside chunk: skip
    | false, c :: cs => c :: loop true cs
  loop true (s.splitOn "\"")

/-- Does this line CLOSE a roots list (a `]` outside the last quote)? -/
def closesRoots (line : String) : Bool :=
  match (line.splitOn "\"").getLast? with
  | some tail => tail.contains ']'
  | none => false

/-- The lakefile scan: the `[[lean_lib]]` blocks' (name, srcDir, roots)
    rows. A lib block missing either key row contributes nothing (the
    lakefile's own convention: srcDir defaults, but `name` is mandatory —
    a nameless block is a malformed lakefile, not a hidden library).
    The `roots = [ … ]` row is captured INCLUDING its continuation lines
    (the lakefile's multi-line rows — ComponentTestsLib declares five
    roots across two lines; a scan that read one line would re-create
    the exact root-level gap this gate exists to close). -/
def parseLibs : List String → Bool → Option String → Option String →
    List String → Bool → List LakeLib → List LakeLib
  | [], _, some n, some d, roots, _, acc =>
      { name := n, srcDir := d, roots := roots.reverse } :: acc
    -- the EOF flush: the file's LAST lib block (a wildcard arm before
    -- this one shadowed it — the planted GhostLib tooth caught it)
  | [], _, _, _, _, _, acc => acc
  | line :: rest, inBlock, name, srcDir, roots, pending, acc =>
      let t := line.trimAscii.toString
      if t.startsWith "#" then
        parseLibs rest inBlock name srcDir roots pending acc  -- a comment
      else if t.startsWith "[[lean_lib]]" then
        -- a new lib block: flush the previous one
        let acc := match name, srcDir with
          | some n, some d =>
              { name := n, srcDir := d, roots := roots.reverse } :: acc
          | _, _ => acc
        parseLibs rest true none none [] false acc
      else if t.startsWith "[[" then
        -- a different block kind ([[lean_exe]], [[require]]): flush + close
        let acc := match name, srcDir with
          | some n, some d =>
              { name := n, srcDir := d, roots := roots.reverse } :: acc
          | _, _ => acc
        parseLibs rest false none none [] false acc
      else if pending then
        -- inside a multi-line roots list: accumulate until the close
        if closesRoots t then
          parseLibs rest inBlock name srcDir (quotedItems t ++ roots) false acc
        else
          parseLibs rest inBlock name srcDir (quotedItems t ++ roots) true acc
      else if t.startsWith "roots" && t.contains '[' then
        -- a roots row: complete on this line or opening onto more
        let pending' := !closesRoots t
        parseLibs rest inBlock name srcDir (quotedItems t ++ roots)
          pending' acc
      else if let some v := strValue "name" t then
        -- capture ONLY inside a [[lean_lib]] block — an [[lean_exe]]'s
        -- name row is an exe, never a library
        if inBlock then parseLibs rest inBlock (some v) srcDir roots pending acc
        else parseLibs rest inBlock none none [] false acc
      else if let some v := strValue "srcDir" t then
        if inBlock then parseLibs rest inBlock name (some v) roots pending acc
        else parseLibs rest inBlock none none [] false acc
      else
        parseLibs rest inBlock name srcDir roots pending acc

/-- The scan over lakefile text (the exe runs from the repo root). -/
def parseLakefile (text : String) : List LakeLib :=
  parseLibs (text.splitOn "\n") false none none [] false []

/-- The lakefile scan for the `[[lean_exe]]` blocks' names (the
exe-level face of the same conservative line walk; `parseLibs`' twin).
A block missing its `name` row contributes nothing (a nameless exe is
a malformed lakefile, not a hidden exe). -/
def parseExes : List String → Bool → List String → List String
  | [], _, acc => acc
  | line :: rest, inBlock, acc =>
      let t := line.trimAscii.toString
      if t.startsWith "#" then parseExes rest inBlock acc  -- a comment
      else if t.startsWith "[[lean_exe]]" then parseExes rest true acc
      else if t.startsWith "[[" then parseExes rest false acc
      else if inBlock then
        match strValue "name" t with
        | some v => parseExes rest inBlock (v :: acc)
        | none => parseExes rest inBlock acc
      else parseExes rest inBlock acc

/-- The exe scan over lakefile text (the exe runs from the repo root). -/
def parseLakefileExes (text : String) : List String :=
  parseExes (text.splitOn "\n") false []

/-- The justfile's `test_libs` list (the quoted space-separated exe
names of the `test_libs := "…"` row — the test battery's ONE list). -/
def parseTestLibs (text : String) : List String :=
  ((text.splitOn "\n").filterMap fun line =>
      let t := line.trimAscii.toString
      if t.startsWith "test_libs" && t.contains ":=" then (t.splitOn "\"")[1]?
      else none)
  |>.flatMap (fun v => v.splitOn " ") |>.filter (!·.isEmpty)

/-! ## The verdict (ctors, never strings — 09 §8) -/

/-- One drift finding. -/
inductive Finding where
  /-- A lakefile library with no table row — THE loud gap. -/
  | ungated (lib : String)
  /-- A lakefile root missing from its table row's roots — the
      ROOT-level face (the row exists, but the root escapes the
      per-root sweeps: the exact gap that bit — GuestTests.Deriv,
      ComponentTests.Pipeline). -/
  | ungatedRoot (lib root : String)
  /-- A table row naming no lakefile library. -/
  | stale (dir : String)
  /-- A row root with no source file under its srcDir. -/
  | noSource (dir root : String)
  /-- A justfile `test_libs` entry naming no lakefile exe. -/
  | testedGhost (exe : String)
  /-- A lakefile `Tests`-suffixed exe missing from the justfile's
      test_libs (a test the battery never runs). -/
  | untestedExe (exe : String)
  /-- A gated-table row root whose getRoot has no cone-table row —
      the loud gap, caught at the registry too (06 §8). -/
  | coneUntabled (dir root : String)
  /-- A cone-table root with no source file or module directory under
      any lakefile srcDir (the row outlived its code). -/
  | coneGhost (root : String)
  deriving DecidableEq, Repr

/-- The NAMED table exclusions: lakefile libraries whose row is
    deliberately ABSENT today, each with its reason in the comment —
    the guard refuses nothing for these, but a stale entry (a lib that
    no longer exists, or one whose reason has been remedied) is still a
    finding. Everything else missing a row is the loud gap.

    History: SchemaTestsLib's dupDefBodies findings were audited as
    REMEDIATED (a source grep for ghostMachineKeys/ticketMachineKeys
    finds nothing) and the exclusion was briefly deleted — the lintkit
    fold REFUTED that: the decls are MACRO-GENERATED by
    `schema_entity_machine` (the preset's `<m>Keys` artifact) for the
    ghostMachine/ticketMachine test machines, alpha-equivalent across
    the two. Grep cannot see a generated decl; the fold can.
    REMEDIATED since: the preset's keyless case now emits the `<m>Keys`
    artifact as an `abbrev` (the role-named transparent alias —
    dupDefBodies' calibrated exclusion), and the lib joined the gated
    set (the row's remediation is this history's reason to stay). -/
def expectedUngated : List (String × String) :=
  [ ("LintKitTestsLib", "the linter's own rig — LintKitFixtures.Clean turns \
      the census linters ON; its consumers are the LintKitTests pins")
  ]

/-- The pure verdict. Injections (the teeth stay pure — the Impact
    fixture discipline): `srcExists srcDir root` answers whether the
    root module's source file exists; `rootHosted root` answers whether
    the root has a source file OR module directory under any lakefile
    srcDir (the cone rows name module ROOTS — `ComponentTests` hosts
    `ComponentTests.Main`, a directory, not a file). -/
def verdict (libs : List LakeLib) (exes testLibs : List String)
    (table : Array Gates.PkgSpec) (rootHosted : String → Bool)
    (srcExists : String → String → Bool) : List Finding :=
  let tableDirs := table.toList.map (·.dir)
  let libNames := libs.map (·.name)
  -- 1. every lakefile library must have its row
  let ungated := libs.filterMap fun l =>
    if tableDirs.contains l.name then none
    else if expectedUngated.any fun (n, _) => n == l.name then none
    else some (.ungated l.name)
  -- 1b. every lakefile root must be in its row's roots (the ROOT-level
  --     face of the same agreement — a row that under-declares its
  --     library's roots leaves those modules ungated while LOOKING
  --     covered)
  let ungatedRoots := libs.flatMap fun l =>
    match table.toList.find? fun p => p.dir == l.name with
    | none => []  -- the lib-level face already reported it
    | some row =>
        l.roots.filter
          (fun r => !row.roots.toList.any (fun n => n.toString == r))
          |>.map (fun r => .ungatedRoot l.name r)
  -- 2. every row must name a real library
  let stale := tableDirs.filterMap fun d =>
    if libNames.contains d then none else some (.stale d)
  -- 2b. every named exclusion must still be a real lakefile library
  --     (a remedied or renamed exclusion is drift in the deleted
  --     direction — the loud list never goes stale silently)
  let staleExcl := expectedUngated.filterMap fun (n, _) =>
    if libNames.contains n then none else some (.stale n)
  -- 3. every row root's source must exist (a typo'd root sweeps nothing)
  let noSource := table.toList.flatMap fun p =>
    p.roots.toList.filterMap fun r =>
      if srcExists p.srcDir r.toString then none
      else some (.noSource p.dir r.toString)
  -- 4. the test battery's list × the lakefile's exes, both directions
  --    (builds ≠ tests: a Tests-suffixed exe outside test_libs is a
  --    test the battery never runs)
  let testedGhost := testLibs.filterMap fun e =>
    if exes.contains e then none else some (.testedGhost e)
  let untestedExe := exes.filterMap fun e =>
    if e.endsWith "Tests" && !testLibs.contains e then some (.untestedExe e)
    else none
  -- 5. the cone table × the gated table, both directions (06 §8's loud
  --    gap, caught at the registry; the ghost is the deleted-direction
  --    drift — the cone row outliving its code)
  let coneUntabled := table.toList.flatMap fun p =>
    p.roots.toList.filterMap fun r =>
      if (LintKit.coneOfRoot? r.getRoot).isSome then none
      else some (.coneUntabled p.dir r.toString)
  let coneGhosts := LintKit.coneTable.filterMap fun (r, _) =>
    if rootHosted r.toString then none else some (.coneGhost r.toString)
  ungated ++ ungatedRoots ++ stale ++ staleExcl ++ noSource
    ++ testedGhost ++ untestedExe ++ coneUntabled ++ coneGhosts

/-! ## The negative control (the guard's own tooth) -/

/-- The NAMED table exclusions as fixture lib rows (the self-check's
    stand-ins for the real lakefile's rows). -/
def exclLibs : List LakeLib :=
  expectedUngated.map fun (n, _) => { name := n, srcDir := "excluded" }

/-- The verdict MUST fire on the disagreeing fixtures and MUST stay
    silent on an agreeing one (the exclusions skipped, a stale
    exclusion caught, the ROOT-level face both directions) — fail
    closed. -/
def selfCheck : Bool :=
  -- the loud gap fires on the missing row (the exclusions present as
  -- lib rows and skipped; the unexcluded Ghost gap is THE finding)
  (verdict ({ name := "Ghost", srcDir := "ghost" : LakeLib } :: exclLibs)
    [] [] #[] (fun _ => true) (fun _ _ => true) == [.ungated "Ghost"])
  -- the ROOT-level face: a lakefile root missing from its row fires
  && (verdict ({ name := "Kit", srcDir := "kit",
                 roots := ["Kit", "Kit.Extra"] : LakeLib } :: exclLibs)
        [] [] #[{ dir := "Kit", srcDir := "kit", roots := #[`Kit] :
          Gates.PkgSpec }]
        (fun _ => true) (fun _ _ => true)
      == [.ungatedRoot "Kit" "Kit.Extra"])
  -- the ROOT-level face: every lakefile root IN the row is silent
  && (verdict ({ name := "Kit", srcDir := "kit", roots := ["Kit"] : LakeLib }
        :: exclLibs)
        [] [] #[{ dir := "Kit", srcDir := "kit", roots := #[`Kit] :
          Gates.PkgSpec }]
        (fun _ => true) (fun _ _ => true) == [])
  -- the stale row fires (the row's root kept cone-tabled — the cone
  -- face stays out of this fixture's finding)
  && (verdict exclLibs [] []
        #[{ dir := "Ghost", srcDir := "ghost", roots := #[`Kit] :
          Gates.PkgSpec }]
        (fun _ => true) (fun _ _ => true) == [.stale "Ghost"])
  -- the missing source fires
  && (verdict ({ name := "Kit", srcDir := "kit" : LakeLib } :: exclLibs)
        [] [] #[{ dir := "Kit", srcDir := "kit", roots := #[`Kit.Nowhere] :
          Gates.PkgSpec }]
        (fun _ => true) (fun _ _ => false)
      == [.noSource "Kit" "Kit.Nowhere"])
  -- silence on an agreeing pair (the exclusions skipped; the test
  -- battery's list × the exes agreeing; the gated root cone-tabled)
  && (verdict ({ name := "Kit", srcDir := "kit" : LakeLib } :: exclLibs)
        ["KitTests"] ["KitTests"]
        #[{ dir := "Kit", srcDir := "kit", roots := #[`Kit] : Gates.PkgSpec }]
        (fun _ => true) (fun _ _ => true) == [])
  -- a STALE EXCLUSION fires (the exclusion name missing from the
  -- lakefile — the loud list never goes stale silently)
  && (verdict [{ name := "Kit", srcDir := "kit" : LakeLib }]
        [] [] #[{ dir := "Kit", srcDir := "kit", roots := #[`Kit] :
          Gates.PkgSpec }]
        (fun _ => true) (fun _ _ => true)
      == expectedUngated.map fun (n, _) => .stale n)
  -- a TESTGHOST fires (a test_libs entry naming no lakefile exe)
  && (verdict exclLibs [] ["GhostTests"] #[] (fun _ => true)
        (fun _ _ => true) == [.testedGhost "GhostTests"])
  -- an UNTESTEDEXE fires (a Tests-suffixed exe outside test_libs —
  -- builds ≠ tests: a test the battery never runs)
  && (verdict exclLibs ["GhostTests"] [] #[] (fun _ => true)
        (fun _ _ => true) == [.untestedExe "GhostTests"])
  -- a CONEUNTABLED fires (a gated row root with no cone-table row —
  -- 06 §8's loud gap, caught at the registry too)
  && (verdict ({ name := "Kit", srcDir := "kit" : LakeLib } :: exclLibs)
        ["KitTests"] ["KitTests"]
        #[{ dir := "Kit", srcDir := "kit", roots := #[`Ghost] :
          Gates.PkgSpec }]
        (fun _ => true) (fun _ _ => true)
      == [.coneUntabled "Kit" "Ghost"])
  -- a CONEGHOST fires (a cone-table root with no source anywhere — the
  -- REAL coneTable is the verdict's input, so the hosted predicate
  -- denies exactly one real row: SchemaCore — and that ghost is THE
  -- finding; every other row stays hosted)
  && (verdict exclLibs [] [] #[] (fun r => r != "SchemaCore")
        (fun _ _ => true) == [.coneGhost "SchemaCore"])

/-! ## The gate -/

/-- The lakefile's path (the exe runs from the repo root). -/
def lakefilePath : System.FilePath := "lakefile.toml"

/-- The justfile's path (the test battery's ONE list lives there). -/
def justfilePath : System.FilePath := "justfile"

/-- A cone root's source host under a srcDir: the root's module FILE
    (`srcDir/Root.lean`) or its module DIRECTORY (`srcDir/Root/` — the
    cone rows name module ROOTS: `ComponentTests` hosts
    `ComponentTests.Main`). -/
def hostsRoot (srcDir : String) (r : Lean.Name) : IO Bool := do
  let dir : System.FilePath :=
    { toString := srcDir } / (r.toString.replace "." "/")
  let fileExists ←
    (Lean.modToFilePath ({ toString := srcDir } : System.FilePath) r "lean").pathExists
  let dirExists ← dir.isDir
  return fileExists || dirExists

/-- `gates packages-check` — the gated table × lakefile agreement (both
directions) + every row root's source file + the justfile test battery
× the lakefile exes + the cone table × the gated table (both
directions). Exit 1 on any finding or a failed self-check. -/
def run : IO UInt32 := do
  unless selfCheck do
    IO.eprintln "packages-check: SELF-CHECK FAILED — the drift verdict did \
      not fire on the disagreeing fixtures (the guard's tooth is broken; \
      fail closed)"
    return 1
  unless ← lakefilePath.pathExists do
    IO.eprintln s!"packages-check: {lakefilePath} absent — the guard reads \
      the lakefile from the repo root"
    return 1
  let lakeText ← IO.FS.readFile lakefilePath
  let libs := parseLakefile lakeText
  if libs.isEmpty then
    IO.eprintln "packages-check: no [[lean_lib]] rows parsed — the scan saw \
      nothing (a scan that cannot see the lakefile cannot guard it; fail \
      closed)"
    return 1
  unless ← justfilePath.pathExists do
    IO.eprintln s!"packages-check: {justfilePath} absent — the guard reads \
      the test battery's list from the justfile"
    return 1
  let testLibs := parseTestLibs (← IO.FS.readFile justfilePath)
  if testLibs.isEmpty then
    IO.eprintln "packages-check: no test_libs row parsed from the justfile — \
      the scan saw nothing (a scan that cannot see the battery's list \
      cannot guard it; fail closed)"
    return 1
  let exes := parseLakefileExes lakeText
  if exes.isEmpty then
    IO.eprintln "packages-check: no [[lean_exe]] rows parsed — the scan saw \
      nothing (a scan that cannot see the exes cannot guard the battery; \
      fail closed)"
    return 1
  -- the source-existence faces: the IO walks FIRST (the verdict stays
  -- pure — the Impact fixture discipline); a present root is its name
  let mut present : List String := []
  for p in Gates.gatedPackages do
    for r in p.roots do
      if ← (Lean.modToFilePath p.srcDir r "lean").pathExists then
        present := r.toString :: present
  -- the cone face: a root is HOSTED if some lakefile srcDir carries its
  -- module file or directory (the lakefile's srcDirs are the build
  -- shape's own mount list — no third table is consulted)
  let mut hosted : List String := []
  for (r, _) in LintKit.coneTable do
    let mut found := false
    for lib in libs do
      unless found do
        if ← hostsRoot lib.srcDir r then
          found := true
    if found then
      hosted := r.toString :: hosted
  let findings := verdict libs exes testLibs Gates.gatedPackages
    (fun root => hosted.contains root)
    (fun _ root => present.contains root)
  if findings.isEmpty then
    IO.println s!"packages-check: clean — {Gates.gatedPackages.size} table \
      row(s) = {libs.length} lakefile librar(y/ies), every root's source \
      present, {exes.length} exe(s) = the justfile battery's \
      {testLibs.length} test exe(s), all {LintKit.coneTable.length} cone \
      rows hosted (the single gated set: Gates.Packages' table)"
    return 0
  let mut failed := false
  for f in findings do
    match f with
    | .ungated lib =>
        IO.eprintln s!"packages-check: UNGATED {lib} — a lakefile library \
          with no Gates.Packages row (the loud gap: a new library without \
          its gates row passes every gate silently); land its honest row"
        failed := true
    | .ungatedRoot lib root =>
        IO.eprintln s!"packages-check: UNGATEDROOT {lib}: {root} — a \
          lakefile root missing from its Gates.Packages row's roots (the \
          module escapes the per-root sweeps while the row LOOKS \
          covered); land the root in the row"
        failed := true
    | .stale dir =>
        IO.eprintln s!"packages-check: STALE {dir} — a table row naming no \
          lakefile library (the row outlived its lib); delete it or fix it"
        failed := true
    | .noSource dir root =>
        IO.eprintln s!"packages-check: NOSOURCE {dir}: {root} — the row root \
          has no source file under its srcDir (a typo'd root sweeps \
          nothing); fix the row"
        failed := true
    | .testedGhost exe =>
        IO.eprintln s!"packages-check: TESTGHOST {exe} — a justfile \
          test_libs entry naming no lakefile [[lean_exe]] (a typo'd test \
          loop step); fix the justfile's list"
        failed := true
    | .untestedExe exe =>
        IO.eprintln s!"packages-check: UNTESTEDEXE {exe} — a lakefile \
          Tests-suffixed exe missing from the justfile's test_libs (builds \
          ≠ tests: a test the battery never runs); land its entry"
        failed := true
    | .coneUntabled dir root =>
        IO.eprintln s!"packages-check: CONEUNTABLED {dir}: {root} — the row \
          root's cone has no LintKit.Cone.coneTable entry (the module \
          escapes the cone rule silently — the loud gap, 06 §8); land the \
          root's cone row deliberately"
        failed := true
    | .coneGhost root =>
        IO.eprintln s!"packages-check: CONEGHOST {root} — a cone-table row \
          with no source file or module directory under any lakefile \
          srcDir (the row outlived its code); delete it or fix it"
        failed := true
  if failed then return 1
  return 0

end Gates.PackagesCheck

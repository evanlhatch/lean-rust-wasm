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
2. STALE — a table row whose `dir` names no lakefile library (the row
   outlived its lib — the drift in the deleted direction).
3. NOSOURCE — a row root with no source file under its row's srcDir
   (a typo'd root sweeps nothing — the silent-vacuity face of the same
   lapse).

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
import Gates.Packages

namespace Gates.PackagesCheck

/-! ## The lakefile scan (the conservative line walk) -/

/-- One lakefile library row (the scan's product): the lib name + its
    srcDir. -/
structure LakeLib where
  name : String
  srcDir : String
  deriving Repr, DecidableEq, Inhabited

/-- The value of a `key = "value"` row, as data (the first chunk before
    the closing quote); `none` when the line is not that row. -/
def strValue (key line : String) : Option String :=
  match line.trimAscii.toString.dropPrefix? (key ++ " = \"") with
  | some rest => (rest.toString.splitOn "\"").head?
  | none => none

/-- The lakefile scan: the `[[lean_lib]]` blocks' (name, srcDir) rows.
    A lib block missing either row contributes nothing (the lakefile's
    own convention: srcDir defaults, but `name` is mandatory — a
    nameless block is a malformed lakefile, not a hidden library). -/
def parseLibs : List String → Bool → Option String → Option String →
    List LakeLib → List LakeLib
  | [], _, some n, some d, acc => { name := n, srcDir := d } :: acc
    -- the EOF flush: the file's LAST lib block (a wildcard arm before
    -- this one shadowed it — the planted GhostLib tooth caught it)
  | [], _, _, _, acc => acc
  | line :: rest, inBlock, name, srcDir, acc =>
      let t := line.trimAscii.toString
      if t.startsWith "#" then
        parseLibs rest inBlock name srcDir acc  -- a comment
      else if t.startsWith "[[lean_lib]]" then
        -- a new lib block: flush the previous one
        let acc := match name, srcDir with
          | some n, some d => { name := n, srcDir := d } :: acc
          | _, _ => acc
        parseLibs rest true none none acc
      else if t.startsWith "[[" then
        -- a different block kind ([[lean_exe]], [[require]]): flush + close
        let acc := match name, srcDir with
          | some n, some d => { name := n, srcDir := d } :: acc
          | _, _ => acc
        parseLibs rest false none none acc
      else if let some v := strValue "name" t then
        -- capture ONLY inside a [[lean_lib]] block — an [[lean_exe]]'s
        -- name row is an exe, never a library
        if inBlock then parseLibs rest inBlock (some v) srcDir acc
        else parseLibs rest inBlock none none acc
      else if let some v := strValue "srcDir" t then
        if inBlock then parseLibs rest inBlock name (some v) acc
        else parseLibs rest inBlock none none acc
      else
        parseLibs rest inBlock name srcDir acc

/-- The scan over lakefile text (the exe runs from the repo root). -/
def parseLakefile (text : String) : List LakeLib :=
  parseLibs (text.splitOn "\n") false none none []

/-! ## The verdict (ctors, never strings — 09 §8) -/

/-- One drift finding. -/
inductive Finding where
  /-- A lakefile library with no table row — THE loud gap. -/
  | ungated (lib : String)
  /-- A table row naming no lakefile library. -/
  | stale (dir : String)
  /-- A row root with no source file under its srcDir. -/
  | noSource (dir root : String)
  deriving DecidableEq, Repr

/-- The NAMED table exclusions: lakefile libraries whose row is
    deliberately ABSENT today, each with its reason in the comment —
    the guard refuses nothing for these, but a stale entry (a lib that
    no longer exists, or one whose reason has been remedied) is still a
    finding. Everything else missing a row is the loud gap. -/
def expectedUngated : List (String × String) :=
  [ ("LintKitTestsLib", "the linter's own rig — LintKitFixtures.Clean turns \
      the census linters ON; its consumers are the LintKitTests pins")
  , ("SchemaTestsLib", "PENDING the schema owner: dupDefBodies \
      (ghostMachineKeys/ticketMachineKeys)")
  ]

/-- The pure verdict. `srcExists srcDir root` answers whether the root
    module's source file exists (injected so the teeth stay pure — the
    Impact fixture discipline). -/
def verdict (libs : List LakeLib) (table : Array Gates.PkgSpec)
    (srcExists : String → String → Bool) : List Finding :=
  let tableDirs := table.toList.map (·.dir)
  let libNames := libs.map (·.name)
  -- 1. every lakefile library must have its row
  let ungated := libs.filterMap fun l =>
    if tableDirs.contains l.name then none
    else if expectedUngated.any fun (n, _) => n == l.name then none
    else some (.ungated l.name)
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
  ungated ++ stale ++ staleExcl ++ noSource

/-! ## The negative control (the guard's own tooth) -/

/-- The NAMED table exclusions as fixture lib rows (the self-check's
    stand-ins for the real lakefile's rows). -/
def exclLibs : List LakeLib :=
  expectedUngated.map fun (n, _) => { name := n, srcDir := "excluded" }

/-- The verdict MUST fire on the disagreeing fixtures and MUST stay
    silent on an agreeing one (the exclusions skipped, a stale
    exclusion caught) — fail closed. -/
def selfCheck : Bool :=
  -- the loud gap fires on the missing row (the exclusions present as
  -- lib rows and skipped; the unexcluded Ghost gap is THE finding)
  (verdict ({ name := "Ghost", srcDir := "ghost" : LakeLib } :: exclLibs)
    #[] (fun _ _ => true) == [.ungated "Ghost"])
  -- the stale row fires
  && (verdict exclLibs
        #[{ dir := "Ghost", srcDir := "ghost", roots := #[`Ghost] :
          Gates.PkgSpec }]
        (fun _ _ => true) == [.stale "Ghost"])
  -- the missing source fires
  && (verdict ({ name := "Kit", srcDir := "kit" : LakeLib } :: exclLibs)
        #[{ dir := "Kit", srcDir := "kit", roots := #[`Kit.Nowhere] :
          Gates.PkgSpec }]
        (fun _ _ => false) == [.noSource "Kit" "Kit.Nowhere"])
  -- silence on an agreeing pair (the exclusions skipped)
  && (verdict ({ name := "Kit", srcDir := "kit" : LakeLib } :: exclLibs)
        #[{ dir := "Kit", srcDir := "kit", roots := #[`Kit] : Gates.PkgSpec }]
        (fun _ _ => true) == [])
  -- a STALE EXCLUSION fires (the exclusion name missing from the
  -- lakefile — the loud list never goes stale silently)
  && (verdict [{ name := "Kit", srcDir := "kit" : LakeLib }]
        #[{ dir := "Kit", srcDir := "kit", roots := #[`Kit] : Gates.PkgSpec }]
        (fun _ _ => true)
      == expectedUngated.map fun (n, _) => .stale n)

/-! ## The gate -/

/-- The lakefile's path (the exe runs from the repo root). -/
def lakefilePath : System.FilePath := "lakefile.toml"

/-- `gates packages-check` — the gated table × lakefile agreement (both
directions) + every row root's source file. Exit 1 on any finding or a
failed self-check. -/
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
  let libs := parseLakefile (← IO.FS.readFile lakefilePath)
  if libs.isEmpty then
    IO.eprintln "packages-check: no [[lean_lib]] rows parsed — the scan saw \
      nothing (a scan that cannot see the lakefile cannot guard it; fail \
      closed)"
    return 1
  -- the source-existence face: the IO walk FIRST (the verdict stays
  -- pure — the Impact fixture discipline); a present root is its name
  let mut present : List String := []
  for p in Gates.gatedPackages do
    for r in p.roots do
      if ← (Lean.modToFilePath p.srcDir r "lean").pathExists then
        present := r.toString :: present
  let findings := verdict libs Gates.gatedPackages
    (fun _ root => present.contains root)
  if findings.isEmpty then
    IO.println s!"packages-check: clean — {Gates.gatedPackages.size} table \
      row(s) = {libs.length} lakefile librar(y/ies), every root's source \
      present (the single gated set: Gates.Packages' table)"
    return 0
  let mut failed := false
  for f in findings do
    match f with
    | .ungated lib =>
        IO.eprintln s!"packages-check: UNGATED {lib} — a lakefile library \
          with no Gates.Packages row (the loud gap: a new library without \
          its gates row passes every gate silently); land its honest row"
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
  if failed then return 1
  return 0

end Gates.PackagesCheck

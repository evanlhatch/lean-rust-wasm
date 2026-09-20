/-
LintKit.TextLints — source-text lints run by the `guestlang-lint` driver
over each linted module's `.lean` file (no elaboration involvement, so they
work on packages that never import LintKit):

* `linter.guestlang.noLinterDisable` (flatland doctrine rule): a
  `set_option linter.* false` opt-out must carry an adjacent justification —
  a comment on the same line or the line directly above containing
  "because". Bare opt-outs are unreviewable drift.
* `linter.guestlang.testImportDiscipline` (notes/lean-doctrine.md §4): files
  under a `Tests/` directory import TestKit (the blessed surface), never
  LSpec directly.
* `linter.guestlang.importBan` (notes/single-lake-migration.md §3): files
  under a banned directory prefix must not import the banned module roots —
  the per-package core-only-ness that used to be a lakefile boundary
  (no mathlib/Dbsp require), held as DATA so it survives the single-lake
  migration (a package's discipline ratchets in when it absorbs).

All are pure `String → Array TextFinding`, unit-tested in LintKit's own
Tests with positive and negative controls. The options are declared at top
level (see LintKit.Basic's header note).
-/
module

public import LintKit.Basic

public meta section

open Lean

register_option linter.guestlang.noLinterDisable : Bool := {
  defValue := true
  descr := "text lint: `set_option linter.* false` requires an adjacent comment \
    justifying it (same or previous line, containing \"because\")"
}

register_option linter.guestlang.testImportDiscipline : Bool := {
  defValue := true
  descr := "text lint: files under Tests/ import TestKit, never LSpec directly"
}

register_option linter.guestlang.importBan : Bool := {
  defValue := true
  descr := "text lint: files under a banned directory prefix import no banned \
    module root (the single-lake migration's dependency discipline as data)"
}

register_option linter.guestlang.noNewPartial : Bool := {
  defValue := true
  descr := "text lint: no new `partial def` (a per-file legacy allowance ratchets \
    the existing ones down); use structural or well-founded recursion"
}

register_option linter.guestlang.noReprInEmit : Bool := {
  defValue := true
  descr := "text lint: no `repr` in Emit/ modules (Repr is not a stable format)"
}

register_option linter.guestlang.noFormatInDebug : Bool := {
  defValue := true
  descr := "text lint: Debug.lean calls emitter functions, never re-renders"
}

register_option linter.guestlang.coreHasNoClaim : Bool := {
  defValue := true
  descr := "text lint: a \"core has no X\" comment must cite the check run"
}

register_option linter.guestlang.staleNotesPath : Bool := {
  defValue := true
  descr := "text lint: stale notes-subdirectory path references (the \
    flatland-era `notes` subdir does not exist in this repo)"
}

register_option linter.guestlang.nolintReason : Bool := {
  defValue := true
  descr := "text lint: `@[nolint]` requires the reason string"
}

namespace LintKit

/-- A source-text lint finding. -/
structure TextFinding where
  file    : String
  line    : Nat  -- 1-based
  linter  : Name
  message : String
  deriving Repr, Inhabited

/-- Does `line` (a source line) carry a justification comment containing
"because" (case-insensitive)? -/
private def justified (line : String) : Bool :=
  let comment := String.join ((line.splitOn "--").drop 1)
  (comment.toLower.splitOn "because").length > 1

/-- `noLinterDisable`: flag bare `set_option linter.* false` opt-outs. -/
def checkNoLinterDisable (file : String) (content : String) : Array TextFinding := Id.run do
  let lines := (content.splitOn "\n").toArray
  let mut out := #[]
  for h : i in [:lines.size] do
    let line := lines[i]
    let t := line.trimAscii.toString
    unless t.startsWith "set_option linter." do continue
    -- must set a linter option to `false` (as a token before any `in`/comment)
    let head := (t.splitOn "--").headD ""
    let toks := head.splitOn.filter (!·.isEmpty)
    let falseIdx? := toks.findIdx? (· == "false")
    let inIdx? := toks.findIdx? (· == "in")
    let disables : Bool := match falseIdx?, inIdx? with
      | some f, some n => f < n
      | some _, none => true
      | none, _ => false
    unless disables do continue
    if justified line then continue
    if i > 0 && justified lines[i - 1]! then continue
    out := out.push { file, line := i + 1
                      linter := `linter.guestlang.noLinterDisable
                      message := "`set_option linter.* false` without a \
                        justification comment containing \"because\" (same \
                        line or line above)" }
  return out

/-- Per-line code/comment split: nested block comments are tracked,
doc comments count as comments, a line comment runs to end of line, and
string LITERALS are tracked (their contents land in neither channel —
a format string mentioning a comment opener must not fool the scanner).
APPROXIMATION: char literals containing quotes confuse the string state —
accepted (heuristic gates, not a parser). -/
def splitCodeComments (content : String) : Array (Nat × String × String) := Id.run do
  let mut out := #[]
  let mut depth : Nat := 0
  let mut inStr : Bool := false
  let mut i : Nat := 1
  for line in content.splitOn "\n" do
    let mut code := ""
    let mut comment := ""
    let mut cs := line.toList
    while true do
      match depth, inStr, cs with
      | _, _, [] => break
      | 0, true, '\\' :: c :: rest =>        -- string escape
        code := code ++ "\\" ++ c.toString
        cs := rest
      | 0, true, '"' :: rest =>
        inStr := false
        code := code ++ "\""
        cs := rest
      | 0, true, _ :: rest =>
        cs := rest                            -- string content: neither channel
      | 0, false, '"' :: rest =>
        inStr := true
        code := code ++ "\""
        cs := rest
      | 0, false, '-' :: '-' :: _ =>
        comment := comment ++ String.ofList cs
        break
      | 0, false, '/' :: '-' :: rest =>
        depth := 1
        comment := comment ++ " "
        cs := rest
      | d, false, '/' :: '-' :: rest =>
        depth := d + 1
        cs := rest
      | d, false, '-' :: '/' :: rest =>
        depth := d - 1
        comment := comment ++ " "
        cs := rest
      | 0, false, c :: rest =>
        code := code ++ c.toString
        cs := rest
      | _, false, c :: rest =>
        comment := comment ++ c.toString
        cs := rest
      | _, true, c :: _ =>
        -- unreachable: inStr is only set at depth 0; defensive reset
        inStr := false
        comment := comment ++ c.toString
        cs := cs.drop 1
    out := out.push (i, code, comment)
    i := i + 1
  return out

/-- The import-ban table (the single-lake migration's discipline rows):
`(dirPrefix, bannedRoots, reason)`. A source file whose path starts with
`dirPrefix` must not `import` a module whose name is or starts with one of
`bannedRoots` (name-boundary exact: `Mathlib.Data` matches, `MathlibX` does
not). Rows carry the DISCIPLINE each package already enforces through its
(dead or dying) lakefile's require set; a package's row lands when its
discipline is ratcheted in and keeps firing after absorption — the physical
`lean/<dir>/` layout does not move. Notes/canon: the lakefile boundary dies,
the rule survives as this table. -/
def importBans : List (String × List String × String) :=
  [("lean/codegen-core/",
    ["Mathlib", "Dbsp", "Machines", "Substrait", "SchemaLang", "GuestlangStd",
     "Faults", "Ledger", "QLang", "Proofkit", "FeatureFlags", "WasmBackend",
     "EdgePython"],
    "codegen-core is core-only: it imports nothing above TestKit/LintKit/LSpec \
      (the D1 doctrine — every downstream package's internals import it)"),
   ("lean/substrait/",
    ["Mathlib", "Dbsp", "Machines", "SchemaLang", "GuestlangStd", "Faults",
     "Ledger", "QLang", "Proofkit", "FeatureFlags", "WasmBackend", "EdgePython"],
    "substrait is core-only: the typed query language owns no mathlib cone \
      (the package's dependency policy)"),
   ("lean/TestKit/",
    ["Mathlib", "Dbsp", "Machines", "SchemaLang", "GuestlangStd", "Substrait",
     "CodegenCore", "Faults", "Ledger", "QLang", "Proofkit", "FeatureFlags",
     "WasmBackend", "EdgePython"],
    "TestKit is core + LSpec only — every package's test lane requires it, so \
      its closure must stay cheap"),
   ("lean/LintKit/",
    ["Mathlib", "Dbsp", "Machines", "TestKit", "LSpec", "SchemaLang",
     "GuestlangStd", "Substrait", "CodegenCore", "Faults", "Ledger", "QLang",
     "Proofkit", "FeatureFlags", "WasmBackend", "EdgePython"],
    "LintKit is pure Lean core + meta code — the linter must never sit in the \
      closure it lints (core-only per the lakefile's contract)")]

/-- Is `mod` (a module-name token from an import line) exactly `root` or a
`root.`-prefixed child? Name-boundary exact, unlike a raw string prefix. -/
def importsRoot (mod : String) (root : Name) : Bool :=
  let r := root.toString
  mod == r || mod.startsWith (r ++ ".")

/-- `importBan`: for each table row whose `dirPrefix` matches the file, an
`import` line naming a banned root is a finding. Code-channel only (the
comment/string scanner) — a commented-out import never fires. -/
def checkImportBan (file : String) (content : String) : Array TextFinding := Id.run do
  let mut out := #[]
  for (dirPrefix, roots, reason) in importBans do
    unless (file.splitOn dirPrefix).length > 1 do continue
    for (i, code, _) in splitCodeComments content do
      let toks := code.trimAscii.toString.splitOn.filter (!·.isEmpty)
      if toks.head? == some "import" then
        for t in toks.tail do
          -- a second `import` on the line restarts the token scan
          if t == "import" then continue
          for r in roots do
            if importsRoot t r.toName then
              out := out.push { file, line := i
                                linter := `linter.guestlang.importBan
                                message := s!"import of `{t}` under `{dirPrefix}` \
                                  violates the dependency discipline: {reason}" }
  return out

/-- Is `file` a TEST file? Path-shape-robust (the single-lake lesson): the
old predicate matched the substring `/Tests/` — true for the absolute
cwd-relative paths of the per-package runs and for absolute paths, but
FALSE for the root-run's relative `lean/<dir>/<Pkg>Tests/…` paths (the §5
renamed test roots). A test file is any file under a path component named
`Tests` or ending in `Tests` (the renamed per-package test roots). -/
def isTestsFile (file : String) : Bool :=
  (file.splitOn "/").any fun c => c == "Tests" || c.endsWith "Tests"

/-- `testImportDiscipline`: files under `Tests/` must not `import LSpec`,
nor drive LSpec directly (`LSpec.lspecIO` etc.) — the runner goes through
TestKit so the harness discipline (controls, verdicts) holds. -/
def checkTestImportDiscipline (file : String) (content : String) : Array TextFinding := Id.run do
  unless isTestsFile file do return #[]
  let mut out := #[]
  for (i, code, _comment) in splitCodeComments content do
    let t := code.trimAscii.toString
    let toks := t.splitOn.filter (!·.isEmpty)
    if toks.head? == some "import" then
      let mods := toks.tail
      if mods.any (fun m => m == "LSpec" || m.startsWith "LSpec.") then
        out := out.push { file, line := i
                          linter := `linter.guestlang.testImportDiscipline
                          message := "Tests file imports LSpec directly — \
                            import TestKit (the blessed surface re-exports what \
                            tests need)" }
    else if (t.splitOn "lspecIO").length > 1 || (t.splitOn "LSpec.").length > 1 then
      out := out.push { file, line := i
                        linter := `linter.guestlang.testImportDiscipline
                        message := "Tests file drives LSpec directly — route \
                          through TestKit (`mainOfSuites`/`runCheckM`)" }
  return out

/-- Legacy `partial def` allowance (file-name suffix → max count). The
ratchet: a file may carry AT MOST its listed count; any `partial def`
elsewhere — or any overage — is a finding. Tighten the counts as the
runbook's W3.1/W5.3 work shrinks them. -/
def partialAllowance : List (String × Nat) :=
  [("wasm-backend/WasmBackend.lean", 9),
   ("wasm-backend/WasmBackend/Correct.lean", 1),
   ("schema-lang/SchemaLang/Validate.lean", 1),
   ("schema-lang/SchemaLang/Meta/Register/Provenance.lean", 1),
   ("schema-lang/SchemaLang/Meta/Register/Updates.lean", 1),
   ("substrait/Substrait/Emit/Text.lean", 3),
   ("codegen-core/CodegenCore/Emit/Rust.lean", 1),
   ("LintKit/LintKit/DupDefBodies.lean", 1)]

/-- `noNewPartial`: `partial` defeats totality proofs and the compiler
correctness story — new sites need design review, not a keystroke. -/
def checkNoNewPartial (file : String) (content : String) : Array TextFinding := Id.run do
  let allowed := (partialAllowance.find? fun (s, _) =>
    (file.splitOn s).length > 1).map (·.2)
  let mut out := #[]
  let mut count := 0
  for (i, code, _) in splitCodeComments content do
    -- test files are exempt: generators/fixtures don't ship proofs
    if isTestsFile file then continue
    if code.trimAscii.toString.startsWith "partial def" then
      count := count + 1
      match allowed with
      | some max =>
        if count > max then
          out := out.push { file, line := i
                            linter := `linter.guestlang.noNewPartial
                            message := s!"`partial def` beyond this file's legacy \
                              allowance ({max}) — the ratchet only tightens; see \
                              notes/lean-doctrine.md (fuel/WF recursion instead)" }
      | none =>
        out := out.push { file, line := i
                          linter := `linter.guestlang.noNewPartial
                          message := "new `partial def` — partiality blocks \
                            correctness theorems; use structural or well-founded \
                            recursion (notes/lean-doctrine.md)" }
  return out

/-- `noReprInEmit`: `Repr` output is not a stable format — emitters spell
types/values through their own renderer (Docs.lean's convention, now
structural). Applies to modules under an `Emit/` directory. -/
def checkNoReprInEmit (file : String) (content : String) : Array TextFinding := Id.run do
  unless (file.splitOn "/Emit/").length > 1 do return #[]
  let mut out := #[]
  for (i, code, _) in splitCodeComments content do
    let toks := code.splitOn
    if toks.any (fun t => t == "repr" || t == "reprStr" || t == "reprPrec"
        || t.startsWith "(repr" || t.endsWith "repr") then
      out := out.push { file, line := i
                        linter := `linter.guestlang.noReprInEmit
                        message := "`repr` in an emitter — Repr is not a stable \
                          format; use the target's own spelling (tyWit etc.)" }
  return out

/-- `noFormatInDebug`: debug commands call emitter functions; they never
re-render (a second renderer is a second place to drift). -/
def checkNoFormatInDebug (file : String) (content : String) : Array TextFinding := Id.run do
  unless (file.splitOn "/").getLastD "" == "Debug.lean" do return #[]
  let mut out := #[]
  for (i, code, _) in splitCodeComments content do
    if (code.splitOn "Std.Format").length > 1 || (code.splitOn ".pretty").length > 1
        || (code.splitOn "Format.").length > 1 then
      out := out.push { file, line := i
                        linter := `linter.guestlang.noFormatInDebug
                        message := "Debug.lean re-renders — debug views call the \
                          emitter functions (worldOf etc.), never reformat" }
  return out

/-- `coreHasNoClaim`: a claim of the form core-lacks-X in a comment must
cite the check run (the doctrine's rule: ~20 stale claims of this shape
were found hand-rolling core functions). Accept if the comment — a
docstring spans LINES, so the claim line plus the two following lines —
contains \"check\"/\"http\". -/
def checkCoreHasNoClaim (file : String) (content : String) : Array TextFinding := Id.run do
  let parts := splitCodeComments content
  let mut out := #[]
  for h : idx in [:parts.size] do
    let (i, _, comment) := parts[idx]
    let low := comment.toLower
    if (low.splitOn "core has no").length > 1 then
      let window := ((List.range 3).filterMap fun k =>
        parts[idx + k]? |>.map (·.2.2)).foldl (· ++ ·.toLower) low
      let cited := (window.splitOn "check").length > 1 || (window.splitOn "http").length > 1
      unless cited do
        out := out.push { file, line := i
                          linter := `linter.guestlang.coreHasNoClaim
                          message := "\"core has no X\" without a citation — cite \
                            the check you ran (the claim rots) or use the core def" }
  return out

/-- `staleNotesPath`: the flatland-era notes SUBDIRECTORY does not exist
in this repo; comment references to it mislead. Point at a real file in
notes/ or name the flatland doc explicitly. (Comment-scoped: string
literals — e.g. this lint's own messages — are exempt.) -/
def checkStaleNotesPath (file : String) (content : String) : Array TextFinding := Id.run do
  let mut out := #[]
  for (i, _code, comment) in splitCodeComments content do
    -- a reference naming flatland explicitly is an honest pointer (the
    -- docs live in the flatland repo); a bare one pretends a local path.
    if (comment.splitOn "notes/lean/").length > 1
        && (comment.toLower.splitOn "flatland").length == 1 then
      out := out.push { file, line := i
                        linter := `linter.guestlang.staleNotesPath
                        message := "stale path reference — the flatland-era notes \
                          subdirectory does not exist here; reference a real file \
                          in notes/ or name the flatland doc" }
  return out

/-- `nolintReason`: `@[nolint ...]` must carry the reason string — a bare
opt-out is unreviewable drift (the attribute's descr already says so; this
makes it structural). -/
def checkNolintReason (file : String) (content : String) : Array TextFinding := Id.run do
  let mut out := #[]
  for (i, code, _) in splitCodeComments content do
    if (code.splitOn "@[nolint").length > 1 then
      let quotes := (code.splitOn "\"").length - 1
      if quotes < 2 then
        out := out.push { file, line := i
                          linter := `linter.guestlang.nolintReason
                          message := "`@[nolint]` without a reason string — \
                            `@[nolint <linter> \"why\"]`; bare opt-outs are \
                            unreviewable" }
  return out

/-- All text lints over one source file. -/
def runTextLints (file : String) (content : String) : Array TextFinding :=
  checkNoLinterDisable file content ++ checkTestImportDiscipline file content
    ++ checkImportBan file content ++ checkNoNewPartial file content
    ++ checkNoReprInEmit file content ++ checkNoFormatInDebug file content
    ++ checkCoreHasNoClaim file content ++ checkStaleNotesPath file content
    ++ checkNolintReason file content

end LintKit

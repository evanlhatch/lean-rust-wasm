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

Both are pure `String → Array TextFinding`, unit-tested in LintKit's own
Tests with positive and negative controls. The options are declared at top
level (see LintKit.Basic's header note).
-/
import LintKit.Basic

open Lean

@[nolint linter.guestlang.packageNamespace "option declarations must be top-level: the builtin_env_linter registration checks `env.contains <raw option name>` at attribute time (see LintKit.Basic header)"]
register_option linter.guestlang.noLinterDisable : Bool := {
  defValue := true
  descr := "text lint: `set_option linter.* false` requires an adjacent comment \
    justifying it (same or previous line, containing \"because\")"
}

@[nolint linter.guestlang.packageNamespace "option declarations must be top-level: the builtin_env_linter registration checks `env.contains <raw option name>` at attribute time (see LintKit.Basic header)"]
register_option linter.guestlang.testImportDiscipline : Bool := {
  defValue := true
  descr := "text lint: files under Tests/ import TestKit, never LSpec directly"
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

/-- `testImportDiscipline`: files under `Tests/` must not `import LSpec`. -/
def checkTestImportDiscipline (file : String) (content : String) : Array TextFinding := Id.run do
  unless (file.splitOn "/Tests/").length > 1 do return #[]
  let lines := (content.splitOn "\n").toArray
  let mut out := #[]
  for h : i in [:lines.size] do
    let line := lines[i]
    let t := line.trimAscii.toString
    let toks := t.splitOn.filter (!·.isEmpty)
    unless toks.head? == some "import" do continue
    let mods := toks.tail
    if mods.any (fun m => m == "LSpec" || m.startsWith "LSpec.") then
      out := out.push { file, line := i + 1
                        linter := `linter.guestlang.testImportDiscipline
                        message := "Tests file imports LSpec directly — \
                          import TestKit (the blessed surface re-exports what \
                          tests need)" }
  return out

/-- All text lints over one source file. -/
def runTextLints (file : String) (content : String) : Array TextFinding :=
  checkNoLinterDisable file content ++ checkTestImportDiscipline file content

end LintKit

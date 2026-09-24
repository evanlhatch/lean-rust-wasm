/-
LintKit.TextLints — source-text lints run by the driver over each linted
module's `.lean` file (no elaboration involvement, so they work on
packages that never import LintKit; mined from
legacy/lean/LintKit/LintKit/TextLints.lean).

Ported here (the task's two rows; the legacy's other text lints arrive
with their first consumer — nothing-without-a-consumer):

* `linter.guestlang.noNewPartial` — no NEW `partial def` (the ratchet).
  The task premise was "the tree has the legacy-free zero"; the
  CURRENT tree carries exactly four (verified 2026-04 sweep):
  `SchemaCore/Describe.lean` (3, meta-level Expr walkers) and
  `Gates/KernelCheck.lean` (1, the olean walker). The allowance table
  `partialAllowance` is seeded at those counts — a per-file MAX that
  only tightens: any new file, or any overage, is a finding. Test
  files are exempt (generators/fixtures don't ship proofs).

* `linter.guestlang.nolintReason` — every `@[nolint ...]` must carry a
  non-empty reason string; a bare opt-out is unreviewable drift.

Both are pure `String → String → Array TextFinding` (file, content),
unit-tested with positive and negative controls. The shared machinery:
`splitCodeComments` (the per-line code/comment scanner — string literal
contents land in NEITHER channel) and `isTestsFile` (path-shape-robust
test-file detection).

The options are declared at top level (LintKit.Basic's header note).
-/
module

public import LintKit.Basic

public meta section

open Lean

register_option linter.guestlang.noNewPartial : Bool := {
  defValue := true
  descr := "text lint: no new `partial def` (a per-file legacy allowance ratchets \
    the existing ones down); use structural or well-founded recursion"
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

/-- Is `file` a TEST file? Path-shape-robust: any file under a path
component named `Tests` or ending in `Tests` (the per-package test
roots, e.g. `kit/KitTests/Main.lean`). -/
def isTestsFile (file : String) : Bool :=
  (file.splitOn "/").any fun c => c == "Tests" || c.endsWith "Tests"

/-! ## noNewPartial -/

/-- The `partial def` allowance ratchet (file-name suffix → max count),
seeded at the CURRENT tree's verified counts (see the module header).
The ratchet: a file may carry AT MOST its listed count; any `partial def`
elsewhere — or any overage — is a finding. Tighten as the walkers are
made total. -/
def partialAllowance : List (String × Nat) :=
  [("SchemaCore/Describe.lean", 3),
   ("Gates/KernelCheck.lean", 1)]

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
                            message := s!"`partial def` beyond this file's \
                              allowance ({max}) — the ratchet only tightens; \
                              use structural or well-founded recursion" }
      | none =>
        out := out.push { file, line := i
                          linter := `linter.guestlang.noNewPartial
                          message := "new `partial def` — partiality blocks \
                            correctness theorems; use structural or \
                            well-founded recursion" }
  return out

/-! ## nolintReason -/

/-- `nolintReason`: `@[nolint ...]` must carry the reason string — a bare
opt-out is unreviewable drift (the attribute's descr already says so;
this makes it structural). -/
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

end LintKit

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

The enforcement wave's two (the audit's gaps 4 + 5, same shape):

* `linter.guestlang.noLinterSetOption` — no `set_option linter.* false`
  in non-test sources (06 §7's bypass ban): a silenced linter is
  unreviewable drift — the finding is the honest face. Enabling
  (`true`) is fine (the census linters' fixtures do exactly that);
  only the `false` spelling bans. Current tree: ZERO sites (the
  audit's own sweep — ContractsTests' `linter.defProp` row is a test
  file, the fixtures only enable).
* `linter.guestlang.bareExample` — a bare `example` in a gated non-test
  source is the BLIND SPOT: examples are anonymous, so a `sorry` in an
  example's body evades every decl-level sweep (the axiom report, the
  kernel check — nothing collects an anonymous term). Examples in test
  roots are the teeth (the sweep's own convention); examples in source
  roots must carry the per-file allowance's count or move to a test
  root. Seeded at the CURRENT tree's verified counts (the
  partialAllowance ratchet shape — a per-file MAX, only tightens).

All are pure `String → String → Array TextFinding` (file, content),
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

register_option linter.guestlang.noLinterSetOption : Bool := {
  defValue := true
  descr := "text lint: no `set_option linter.* false` in non-test sources — \
    a silenced linter is unreviewable drift (06 §7's bypass ban)"
}

register_option linter.guestlang.bareExample : Bool := {
  defValue := true
  descr := "text lint: a bare `example` in a gated non-test source is the \
    axiom-sweep blind spot (a `sorry` in an anonymous term evades every \
    decl-level sweep); per-file allowance ratchets the seeded sites"
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

/-- The text-lint scan skeleton (the scan→allowlist-filter→emit face
the text lints shared): the two exempt faces — test files (fixtures
are the lint rigs' own territory) and the file's allowlist rows (the
ratchet's per-file exceptions, (suffix, reason)) — then the
comment/string-split code channel's line walk. `none` = an exempt
file, never scanned; the linters fold their own verdict over the
lines. -/
def scannedLines (file content : String) (allowlist : List (String × String)) :
    Option (Array (Nat × String × String)) :=
  if isTestsFile file then none
  else if (allowlist.find? fun (s, _) => (file.splitOn s).length > 1).isSome then none
  else some (splitCodeComments content)

/-! ## noNewPartial -/

/-- The `partial def` allowance ratchet (file-name suffix → max count),
seeded at the CURRENT tree's verified counts (see the module header).
The ratchet: a file may carry AT MOST its listed count; any `partial def`
elsewhere — or any overage — is a finding. Tighten as the walkers are
made total.

The rows' written reasons (the totality rule, 09 §1 — each site's doc
names its own):
- `SchemaCore/Describe.lean` 3: the `Expr` subterm walks are not
  structural (the totality engine cannot see the term's size).
- `Gates/KernelCheck.lean` 1: `walkOleans` — the directory-tree
  recursion terminates by the FS's finiteness, not a structural
  measure. (The sweep's poll loop was made TOTAL at the lint's
  finding: its budget discipline became the explicit poll-round fuel.)
- `Gates/Common.lean` 1: `pkgPool` — a GENUINELY UNBOUNDED wait: the
  pool's RSS budget bounds ADMISSION, not completion (there is no
  per-child wall-clock budget — a hung shard child hangs the pool,
  by design: queueing, never dropping, never killing), so no honest
  fuel exists; the loop is the wait-on-process itself. The honest
  bound's price would be a kill/budget the pool does not have — a
  behavior change. The allowance names the unboundedness; it does not
  paper over it. -/
def partialAllowance : List (String × Nat) :=
  [("SchemaCore/Describe.lean", 3),
   ("Gates/KernelCheck.lean", 1),
   ("Gates/Common.lean", 1)]

/-- `noNewPartial`: `partial` defeats totality proofs and the compiler
correctness story — new sites need design review, not a keystroke. -/
def checkNoNewPartial (file : String) (content : String) : Array TextFinding := Id.run do
  let allowed := (partialAllowance.find? fun (s, _) =>
    (file.splitOn s).length > 1).map (·.2)
  -- the allowance is COUNT-based, not an exemption (an overage still
  -- fires) — the ratchet's rows ride the per-line verdict, not the
  -- skeleton's allowlist filter
  let some lines := scannedLines file content [] | return #[]
  let mut out := #[]
  let mut count := 0
  for (i, code, _) in lines do
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

/-! ## noLinterSetOption -/

/-- `noLinterSetOption`: `set_option linter.* false` in a non-test source
bans the linter's finding at the door — the silenced linter is the
drift. Token-shape check (the third token must be the literal `false`):
enabling a census linter (`true`) is the fixtures' own shape and stays
quiet. -/
def checkNoLinterSetOption (file : String) (content : String) : Array TextFinding := Id.run do
  let some lines := scannedLines file content [] | return #[]
  let mut out := #[]
  for (i, code, _) in lines do
    let toks := code.trimAscii.toString.splitOn.filter (!·.isEmpty)
    match toks with
    | "set_option" :: nm :: "false" :: _ =>
        if (nm.splitOn ".").head?.getD "" == "linter" then
          out := out.push { file, line := i
                            linter := `linter.guestlang.noLinterSetOption
                            message := "`set_option linter.* false` in a \
                              non-test source — a silenced linter is \
                              unreviewable drift (06 §7); fix the finding or \
                              carry the named `@[nolint]`/allowance row" }
    | _ => pure ()
  return out

/-! ## bareExample -/

/-- The bare-`example` allowance ratchet (file-name suffix → max count),
seeded at the CURRENT tree's verified counts — a per-file MAX that only
tightens; any new file, or any overage, is a finding. The rows' written
reasons (the blind spot's honest ledger — each file's examples are the
run-level `rfl` smoke suite over that module's faces; conversion to
named theorems would trade the anonymity for decl-namespace noise while
the bodies stay rung-4 computation):

- `SchemaCore/Codec.lean` 16, `SchemaCore/Value.lean` 12: the codec /
  value-model encoding smoke rows (`encVal .bool (.bool false) = [0]`).
- `SchemaCore/Dependent.lean` 10, `SchemaCore/Witness.lean` 7,
  `SchemaCore/Profile.lean` 7, `SchemaCore/Pred.lean` 7,
  `SchemaCore/Fold.lean` 7, `SchemaCore/Derive.lean` 7,
  `SchemaCore/Confluence.lean` 6, `SchemaCore/Describe.lean` 3,
  `SchemaCore/RowVals.lean` 2: the derive/fold/pred faces' run-level
  rfl rows. -/
def bareExampleAllowance : List (String × Nat) :=
  [("SchemaCore/Codec.lean", 16),
   ("SchemaCore/Value.lean", 12),
   ("SchemaCore/Dependent.lean", 10),
   ("SchemaCore/Witness.lean", 7),
   ("SchemaCore/Profile.lean", 7),
   ("SchemaCore/Pred.lean", 7),
   ("SchemaCore/Fold.lean", 7),
   ("SchemaCore/Derive.lean", 7),
   ("SchemaCore/Confluence.lean", 6),
   ("SchemaCore/Describe.lean", 3),
   ("SchemaCore/RowVals.lean", 2)]

/-- `bareExample`: an anonymous `example` in a gated non-test source is
the axiom-sweep blind spot — the decl-level sweeps (axiom report,
kernel check) collect CONSTANTS; an example elaborates to nothing. -/
def checkBareExample (file : String) (content : String) : Array TextFinding := Id.run do
  let allowed := (bareExampleAllowance.find? fun (s, _) =>
    (file.splitOn s).length > 1).map (·.2)
  -- the allowance is COUNT-based, not an exemption (an overage still
  -- fires) — the partialAllowance ratchet's shape
  let some lines := scannedLines file content [] | return #[]
  let mut out := #[]
  let mut count := 0
  for (i, code, _) in lines do
    let t := code.trimAscii.toString
    if t == "example" || t.startsWith "example " then
      count := count + 1
      match allowed with
      | some max =>
        if count > max then
          out := out.push { file, line := i
                            linter := `linter.guestlang.bareExample
                            message := s!"bare `example` beyond this file's \
                              allowance ({max}) — the ratchet only tightens; \
                              examples are anonymous, so a `sorry` in the body \
                              evades every decl-level sweep (move to a test \
                              root or name the theorem)" }
      | none =>
        out := out.push { file, line := i
                          linter := `linter.guestlang.bareExample
                          message := "bare `example` in a gated source root — \
                            examples are anonymous, so a `sorry` in the body \
                            evades every decl-level sweep (move to a test \
                            root or name the theorem)" }
  return out

/-! ## nolintReason -/

/-- `nolintReason`: `@[nolint ...]` must carry the reason string — a bare
opt-out is unreviewable drift (the attribute's descr already says so;
this makes it structural). -/
def checkNolintReason (file : String) (content : String) : Array TextFinding := Id.run do
  let some lines := scannedLines file content [] | return #[]
  let mut out := #[]
  for (i, code, _) in lines do
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

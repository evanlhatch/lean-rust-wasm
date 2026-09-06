/-
# TestKit.Golden — the golden-file driver, generalized

LeanSubstrait's golden driver (emit text, byte-compare against a committed
file, `--update` regenerates) was hand-rolled inside its Tests/Main.lean.
The pattern recurs — Codegen artifacts, future DSL surfaces — so it lives
here once.

The discipline (lean4-mlir's byte-tie, adapted): the golden is COMMITTED,
CI regenerates and diffs; a mismatch is drift, not a test you skip. The
`--update` path exists for deliberate changes only.
-/

import TestKit.Harness

namespace TestKit.Golden

/-- Check emitted text against a golden file. `update = true` regenerates
    the golden (the deliberate-change path); otherwise a byte difference is
    a failure carrying a diff-shaped message. -/
def checkAgainstGolden (name : String) (emitted : String) (path : System.FilePath)
    (update : Bool) : IO TestKit.CheckResult := do
  if update then
    IO.FS.writeFile path emitted
    return (.ok () : TestKit.CheckResult)
  else
    try
      let golden ← IO.FS.readFile path
      if emitted == golden then return (.ok () : TestKit.CheckResult)
      else
        let msg := s!"{name}: emitted text differs from golden ({path})\n--- emitted ---\n{emitted}\n--- golden ---\n{golden}\n(run with --update to regenerate)"
        return (.error msg : TestKit.CheckResult)
    catch _ =>
      return (.error s!"{name}: golden file missing: {path}; run with --update to generate" : TestKit.CheckResult)

end TestKit.Golden

/-
# TestKit.Harness — the CheckResult ↔ LSpec bridge, one copy

Before this module: Dbsp wrote `checkPasses` + a priority-100 Testable
instance by hand; Machines/Codegen/Flatland/FlatlandDsl each reinvented
`assert`/`assertEq` and the PASS/FAIL driver loop. Now: one copy.

The discipline this enforces:

- **Every check returns data** (`CheckResult`), never prints inside a check.
  Printing is the driver's job (LSpec's runner), so suites compose.
- **The failure message survives** — the priority-100 Testable instance
  carries the `Except.error` string into LSpec's failure report.
- **`lake test` works** for any package whose driver is `mainOfSuite`
  (LSpec's `@[test_driver]` registration).
-/

import LSpec

namespace TestKit

open LSpec

/-- A check result: `.ok ()` or `.error message`. The value level of the
    test suite — everything reduces to this. -/
abbrev CheckResult := Except String Unit

/-- Boolean assertion with message. -/
def assert (cond : Bool) (msg : String) : CheckResult :=
  if cond then .ok () else .error msg

/-- Equality assertion with got/expected in the failure message. -/
def assertEq [BEq α] [ToString α] (name : String) (got expected : α) : CheckResult :=
  if got == expected then .ok () else .error s!"{name}: got {got}, expected {expected}"

/-- Sequencing: first failure wins. -/
def andThen (a b : CheckResult) : CheckResult :=
  match a with | .ok () => b | .error e => .error e

/-- Fold a list of named checks into one CheckResult (names the failure). -/
def allOf (checks : List (String × CheckResult)) : CheckResult :=
  checks.foldl (fun acc (n, r) => andThen acc (match r with
    | .ok () => .ok ()
    | .error e => .error s!"{n}: {e}")) (.ok ())

/-- Lift a check result to a Prop for LSpec. -/
def checkPasses (r : CheckResult) : Prop :=
  match r with
  | .ok () => True
  | .error _ => False

/-- Testable for `checkPasses r` (priority 100 — beats the default
    decidable-prop instance at 25, so the failure message survives). -/
instance (priority := 100) (r : CheckResult) : Testable (checkPasses r) :=
  match r with
  | .ok () => .isTrue trivial
  | .error e => .isFailure 0 0 e

/-- A named check as a TestSeq node. -/
def testCheck (name : String) (r : CheckResult) (next : TestSeq := .done) : TestSeq :=
  test name (checkPasses r) next

/-- Fold named checks into a TestSeq, preserving order and names. -/
def suiteOf (checks : List (String × CheckResult)) : TestSeq :=
  checks.foldr (fun (n, r) acc => testCheck n r acc) .done

/-- The standard driver: run the suites, return the exit code.
    Each pair is (group-name, tests). -/
def mainOfSuites (groups : List (String × TestSeq)) : IO UInt32 :=
  LSpec.lspecIO (.ofList (groups.map fun (n, t) => (n, [t]))) []

/-- The one-liner for the common case: one group of named checks. -/
def mainOfChecks (groupName : String) (checks : List (String × CheckResult)) : IO UInt32 :=
  mainOfSuites [(groupName, suiteOf checks)]

end TestKit

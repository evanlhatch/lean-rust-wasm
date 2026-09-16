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

module

public import LSpec

@[expose] public section

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

/-- Error assertion: `r` must be `.error` AND its message must contain
    every substring. Substring matching is deliberate here — this is for
    pin-checking that a diagnostic path fires, not for replacing structured
    diagnostics (doctrine §4). -/
def expectErrorContaining (substrings : List String) (r : Except String α) : CheckResult :=
  match r with
  | .ok _ => .error s!"expected an error containing {substrings}, got .ok"
  | .error e =>
    match substrings.find? (fun s => (e.splitOn s).length == 1) with
    | none => .ok ()
    | some s => .error s!"error message missing '{s}': {e}"

/-- Pointwise equality over a finite domain: the first mismatch is an error
    naming the index (the input's identity in the domain) and the values
    (Dbsp/Tests' hand-rolled loop-witness, once). -/
def assertPointwiseEq [BEq β] [ToString β] (name : String) (f g : α → β) (domain : List α)
    : CheckResult :=
  match domain.zipIdx.find? (fun (a, _) =>
      match f a == g a with | true => false | false => true) with
  | none => .ok ()
  | some (a, i) =>
    .error s!"{name}: mismatch at domain index {i}: got {f a}, expected {g a}"

/-- Substring assertion with name. -/
def assertContains (name haystack needle : String) : CheckResult :=
  if (haystack.splitOn needle).length > 1 then .ok ()
  else .error s!"{name}: expected to find '{needle}' in '{haystack}'"

/-- CheckM: a StateT accumulator of named CheckResults for IO drivers
    (substrait Tests' `results := results ++ …` pattern, once), with a
    HARD-ABORT channel. `errorAbort` records a failure THEN jumps the
    rest of the driver — the eval-error semantics (abort the remaining
    sections, keep everything recorded). The ExceptT sits OUTSIDE the
    StateT, so a throw does NOT unwind the accumulator. -/
abbrev CheckM := ExceptT String (StateT (List (String × CheckResult)) IO)

/-- Append a named check to the accumulator. -/
def check (name : String) (r : CheckResult) : CheckM Unit :=
  modify (· ++ [(name, r)])

/-- Record a failure AND abort the rest of the driver — the recorded
    row survives (checked before the throw); `runCheckM` reports it,
    `runCheckMCollect` keeps it. -/
def errorAbort (name : String) (msg : String) : CheckM α := do
  check name (.error msg)
  throw msg

/-- Run a CheckM driver: print each failure with its name, exit code 0 iff
    every check passed (an aborted driver = nonzero — the abort row is
    reported). -/
def runCheckM (m : CheckM Unit) : IO UInt32 := do
  let (_, results) ← (ExceptT.run m).run []
  let mut failures := 0
  for (name, r) in results do
    match r with
    | .ok () => IO.println s!"✓ {name}"
    | .error e =>
      IO.println s!"× {name}: {e}"
      failures := failures + 1
  if failures == 0 then IO.println s!"{results.length} checks passed"
  return if failures == 0 then 0 else 1

/-- Run a CheckM driver and return the collected results (abort rows
    included) — the LSpec-display path (`mainOfSuites` + `suiteOf`)
    keeps working off the same accumulator. -/
def runCheckMCollect (m : CheckM Unit) : IO (List (String × CheckResult)) :=
  (ExceptT.run m).run [] |>.map (·.2)

/-- The shared driver loop: run each spec's verdict getter, print the
    verdict, count failures — exit-code semantics for drivers. One copy
    (PropSpec.runSpecs / DetSpec.runDets / DiffSpec.runDiffs used to
    re-implement this exact loop three times). -/
def runVerdicts {α : Type} (specs : List α) (get : α → IO (Bool × String)) : IO UInt32 := do
  let mut failures := 0
  for ps in specs do
    let (ok, verdict) ← get ps
    IO.println verdict
    if !ok then failures := failures + 1
  return if failures == 0 then 0 else 1

end TestKit

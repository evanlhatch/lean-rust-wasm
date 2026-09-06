/-
# TestKit Tests — the harness tests itself

1. Harness: assertEq/checkPasses carry failure messages into LSpec output.
2. PropSpec: a true property passes; its sabotaged sibling is caught —
   and a VACUOUS control (one the sampler can't reach) is flagged.
3. Golden: check/update/mismatch paths against a temp file.
-/
import TestKit
import Plausible

open TestKit LSpec Plausible

/-- The harness checks. -/
def harnessChecks : List (String × CheckResult) :=
  [ ("assert-ok", assert (1 + 1 == 2) "arith broke")
  , ("assertEq-ok", assertEq "eq" (1 + 1) 2)
  , ("allOf-ok", allOf [("a", .ok ()), ("b", .ok ())]) ]

/-- A true property: list reverse is an involution. -/
def revProp : TestSeq :=
  checkPlausibleIO "reverse∘reverse = id"
    (∀ (l : List Nat), l.reverse.reverse = l)
    .done { numInst := 200, randomSeed := some 7 }

/-- Its negative control: reverse = id (false for length ≥ 2 lists — the
    sampler generates those quickly). -/
def revControl : TestSeq :=
  checkPlausibleIO "sabotaged: reverse = id (must be caught)"
    (∀ (l : List Nat), l.reverse = l)
    .done { numInst := 200, randomSeed := some 7 }

/-- A VACUOUS control: sabotage the sampler can't reach (lists are short at
    small sizes but `l.reverse == [] ∧ l ≠ []` is simply never true — the
    control must be CATCHABLE-in-principle but unprovable... no: this one is
    unsatisfiable-as-property yet never-falsified-by-sampling: it asserts
    every generated list has length < 1000, which holds vacuously at small
    sizes). A PropSpec with this as its control must be FLAGGED. -/
def vacuousProp : TestSeq :=
  checkPlausibleIO "vacuous property (passes)"
    (∀ (l : List Nat), l.length < 1000)
    .done { numInst := 50, randomSeed := some 7 }

def vacuousControl : TestSeq :=
  checkPlausibleIO "vacuous control (also passes — must be flagged)"
    (∀ (l : List Nat), l.length < 999)
    .done { numInst := 50, randomSeed := some 7 }

def main : IO UInt32 := do
  let mut failures := 0
  -- harness suite
  let code ← TestKit.mainOfSuites [("harness", suiteOf harnessChecks)]
  if code != 0 then failures := failures + 1
  -- PropSpec: the good pair passes
  let (ok1, v1) ← (PropSpec.mk "reverse involution" revProp revControl
    "reverse = id").runIO
  IO.println v1
  if !ok1 then failures := failures + 1
  -- PropSpec: the vacuous pair is FLAGGED (property passes, control not caught)
  let (ok2, v2) ← (PropSpec.mk "vacuous demo" vacuousProp vacuousControl
    "nearly-identical threshold").runIO
  IO.println v2
  if ok2 then
    IO.println "FAIL: vacuous pair was not flagged"
    failures := failures + 1
  -- golden: write, match, mismatch
  let tmp : System.FilePath := "/tmp/testkit-golden-demo.txt"
  let r1 ← Golden.checkAgainstGolden "demo" "hello golden\n" tmp true
  let r2 ← Golden.checkAgainstGolden "demo" "hello golden\n" tmp false
  let r3 ← Golden.checkAgainstGolden "demo" "drifted\n" tmp false
  match r1, r2, r3 with
  | .ok (), .ok (), .error _ => IO.println "✓ golden paths"
  | _, _, _ => IO.println "FAIL: golden paths"; failures := failures + 1
  if failures == 0 then IO.println "all checks passed" else IO.eprintln s!"{failures} FAILURES"
  return if failures == 0 then 0 else 1

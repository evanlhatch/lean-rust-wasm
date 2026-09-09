/-
# TestKit Tests — the harness tests itself

1. Harness: assertEq/checkPasses carry failure messages into LSpec output.
2. PropSpec: a true property passes; its sabotaged sibling is caught —
   and a VACUOUS control (one the sampler can't reach) is flagged.
3. Golden: check/update/mismatch paths against a temp file.
4. DetSpec: the deterministic +/− discipline — a good pair passes, a
   vacuous control is flagged LOUDER than a failure.
5. Harness additions: expectErrorContaining / assertPointwiseEq /
   assertContains, each with a negative control that MUST fail.
6. CheckM: the accumulator driver reports failures and exit codes.
7. GateKit: byteTie detects drift, writes under update; parseGateArgs
   accepts exactly --check / --update / --help.
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

/-- DetSpec: a good pair — check passes, sabotaged sibling errors. -/
def detGood : DetSpec :=
  ⟨"pointwise negation",
    assertPointwiseEq "neg" (fun n : Nat => n + 0) (fun n => n) [0, 1, 2],
    assertPointwiseEq "neg (sabotaged)" (fun n : Nat => n + 1) (fun n => n) [0, 1, 2],
    "off-by-one sibling"⟩

/-- DetSpec with a VACUOUS control: the control passes, so the pair must be
    flagged as a failure. -/
def detVacuous : DetSpec :=
  ⟨"vacuous control demo",
    assert (1 + 1 == 2) "arith broke",
    assert (1 + 1 == 2) "arith broke",
    "identical sibling (passes — must be flagged)"⟩

/-- DetSpec with a failing check: must be flagged, differently from vacuous. -/
def detFailing : DetSpec :=
  ⟨"failing check demo",
    assertEq "eq" (1 + 1) 3,
    .error "control errors as required",
    "erroring sibling"⟩

/-- Harness additions, each with its negative control as a DetSpec pair. -/
def harnessAdditionSpecs : List DetSpec :=
  [ ⟨"expectErrorContaining catches all substrings",
      expectErrorContaining ["universe", "unknown ref"]
        (.error "universeCheck: unknown ref 'Foo'" : Except String Unit),
      expectErrorContaining ["universe", "MISSING"]
        (.error "universeCheck: unknown ref 'Foo'" : Except String Unit),
      "substring absent from message"⟩
  , ⟨"expectErrorContaining rejects .ok",
      expectErrorContaining ["boom"] (.error "boom" : Except String Unit),
      expectErrorContaining ["boom"] (.ok () : Except String Unit),
      ".ok sibling (expectError errors on it — must be caught)"⟩
  , ⟨"assertPointwiseEq catches a known index",
      -- g diverges from f exactly at domain index 2; the error must name it
      assertContains "idx witness"
        (match assertPointwiseEq "pw" (fun n : Nat => n) (fun n => if n == 2 then 99 else n)
            [0, 1, 2, 3] with
          | .error e => e | .ok () => "") "domain index 2",
      assertPointwiseEq "pw" (fun n : Nat => n) (fun n => if n == 2 then 99 else n) [0, 1, 2, 3],
      "raw mismatch result (must error)"⟩
  , ⟨"assertContains finds the needle",
      assertContains "haystack" "the quick brown fox" "quick",
      assertContains "haystack" "the quick brown fox" "MISSING",
      "absent needle (must error)"⟩ ]

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
  -- DetSpec: the good pair passes via runDets
  let detCode ← runDets [detGood]
  if detCode != 0 then failures := failures + 1
  -- DetSpec negative controls (evaluated via the pure runner):
  -- vacuous control must be flagged; failing check must be flagged.
  let (vacOk, vacVerdict) := detVacuous.run
  IO.println vacVerdict
  if vacOk then
    IO.println "FAIL: vacuous DetSpec control was not flagged"
    failures := failures + 1
  let (failOk, failVerdict) := detFailing.run
  IO.println failVerdict
  if failOk then
    IO.println "FAIL: failing DetSpec check was not flagged"
    failures := failures + 1
  -- Harness additions (positive + negative control per assertion)
  let hCode ← runDets harnessAdditionSpecs
  if hCode != 0 then failures := failures + 1
  -- CheckM: all-pass driver exits 0; a driver with one failure exits 1
  -- and names the failing check.
  let cmOk ← runCheckM do
    check "cm-assert" (assert (2 * 2 == 4) "mul broke")
    check "cm-contains" (assertContains "cm" "abcdef" "cde")
  if cmOk != 0 then failures := failures + 1
  let cmBad ← runCheckM do
    check "cm-pass" (.ok ())
    check "cm-FAIL" (.error "deliberate failure (must exit 1)")
  if cmBad == 0 then
    IO.println "FAIL: CheckM driver swallowed a failure"
    failures := failures + 1
  -- GateKit: byteTie write / match / drift-detection against a temp file
  let gtmp : System.FilePath := "/tmp/testkit-gatekit-demo.txt"
  let gWrite ← GateKit.byteTie "gate-demo" gtmp (pure "committed bytes\n") true
  let gMatch ← GateKit.byteTie "gate-demo" gtmp (pure "committed bytes\n") false
  let gDrift ← GateKit.byteTie "gate-demo" gtmp (pure "drifted bytes\n") false
  if gWrite != 0 || gMatch != 0 || gDrift == 0 then
    IO.println "FAIL: byteTie write/match/drift paths"
    failures := failures + 1
  else IO.println "✓ byteTie write/match/drift paths"
  -- GateKit: parseGateArgs accepts exactly the uniform surface
  let argsOk :=
    GateKit.parseGateArgs [] == some false &&
    GateKit.parseGateArgs ["--check"] == some false &&
    GateKit.parseGateArgs ["--update"] == some true &&
    GateKit.parseGateArgs ["--help"] == none &&
    GateKit.parseGateArgs ["--bogus"] == none
  if !argsOk then
    IO.println "FAIL: parseGateArgs surface"
    failures := failures + 1
  else IO.println "✓ parseGateArgs surface"
  if failures == 0 then IO.println "all checks passed" else IO.eprintln s!"{failures} FAILURES"
  return if failures == 0 then 0 else 1

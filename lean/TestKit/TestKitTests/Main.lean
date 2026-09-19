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
8. DiffSpec: the corruption-negative discipline for differential gates —
   a good gate (positive + 2 context-naming corruptions) passes; an
   IDENTITY corruption (gate vacuous), a context-poor rejection, and an
   empty corruption list are each flagged as gate failures.
-/
import TestKit
import Plausible

open TestKit Plausible

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

-- ── DiffSpec: a miniature differential gate ──────────────────────────

/-- A tiny "replay fold" oracle: sums a column of cells; a cell over the
    bound is a divergence error naming the row, the value, and the bound
    (flatland ReplayGate's tick/column lesson, miniaturized). -/
def foldColumn (cells : List Nat) : CheckResult :=
  match cells.zipIdx.find? (fun (v, _) => v > 100) with
  | some (v, i) => .error s!"replay divergence at row {i}: cell value {v} exceeds bound 100"
  | none => .ok ()

/-- The clean input every spec below shares. -/
def cleanColumn : List Nat := [3, 10, 17, 24, 42]

/-- The good gate: positive passes, both corruptions are rejected WITH
    context. -/
def diffGood : DiffSpec := ⟨"replay fold rejects sabotaged cells",
  foldColumn cleanColumn,
  [ corrupt "oversized first cell" (fun c => 999 :: c.drop 1) cleanColumn foldColumn
      ["row 0", "exceeds bound"]
  , corrupt "oversized last cell" (fun c => c.take 4 ++ [999]) cleanColumn foldColumn
      ["row 4", "exceeds bound"] ]⟩

/-- GATE FAILURE demo 1: the identity "corruption" — the sabotage changes
    nothing, the check passes, the gate is vacuous. Must be flagged. -/
def diffVacuous : DiffSpec := ⟨"identity-corruption demo (must fail)",
  foldColumn cleanColumn,
  [ corrupt "identity sabotage" id cleanColumn foldColumn ]⟩

/-- GATE FAILURE demo 2: the corruption IS caught but the error lacks the
    required context (no row named). Must be flagged. -/
def diffNoContext : DiffSpec := ⟨"context-poor rejection demo (must fail)",
  foldColumn cleanColumn,
  [ corrupt "oversized first cell" (fun c => 999 :: c.drop 1) cleanColumn foldColumn
      ["tick 0", "old-assert"] ]⟩

/-- GATE FAILURE demo 3: no corruptions at all. Must be flagged. -/
def diffEmpty : DiffSpec := ⟨"corruption-free demo (must fail)",
  foldColumn cleanColumn, []⟩

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
  -- GateKit.audit: banned pattern present → finding; required present and
  -- clean text → none. Negative control: the empty rule list is vacuously
  -- clean ONLY here, in the test — a real emitter must never ship `[]`.
  let auditRules : List GateKit.AuditRule :=
    [ { name := "no-todo", pattern := "TODO", why := "unfinished emission" }
    , { name := "hdr", pattern := "package guestlang", required := true
      , why := "the WIT package header is the registry key" } ]
  let auditOk :=
    (GateKit.auditFindings auditRules "package guestlang: demo; x TODO y"
        == ["banned \"TODO\" present — unfinished emission"])
      && (GateKit.auditFindings auditRules "package guestlang: demo;" == [])
      && ((GateKit.auditFindings auditRules "no header here").length == 1)
      && (GateKit.auditFindings ([] : List GateKit.AuditRule) "anything" == [])
  if !auditOk then
    IO.println "FAIL: GateKit.auditFindings controls"
    failures := failures + 1
  else IO.println "✓ GateKit.auditFindings controls"
  -- DiffSpec: the good gate passes via runDiffs
  let diffCode ← runDiffs [diffGood]
  if diffCode != 0 then failures := failures + 1
  -- DiffSpec negative controls (pure runner): each bad gate shape must
  -- be flagged, with the right verdict shape.
  let (vacD, vacDVerdict) := diffVacuous.run
  IO.println vacDVerdict
  if vacD || (vacDVerdict.splitOn "unexpectedly succeeded").length == 1 then
    IO.println "FAIL: identity corruption was not flagged as 'unexpectedly succeeded'"
    failures := failures + 1
  let (noCtx, noCtxVerdict) := diffNoContext.run
  IO.println noCtxVerdict
  if noCtx || (noCtxVerdict.splitOn "lacks context").length == 1 then
    IO.println "FAIL: context-poor rejection was not flagged"
    failures := failures + 1
  let (empD, empDVerdict) := diffEmpty.run
  IO.println empDVerdict
  if empD || (empDVerdict.splitOn "VACUOUS").length == 1 then
    IO.println "FAIL: corruption-free gate was not flagged"
    failures := failures + 1
  if failures == 0 then IO.println "all checks passed" else IO.eprintln s!"{failures} FAILURES"
  return if failures == 0 then 0 else 1

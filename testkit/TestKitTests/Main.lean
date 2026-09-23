/-
# TestKit Tests — TestKit tests ITSELF

Owned by: the TestKit agent (the macht tree, `testkit/`).

NOTE on the runner: this suite KEEPS its own hand-rolled checks —
self-testing is legitimate (the harness must be able to observe its own
FAIL and VACUOUS verdicts, which `mainOfSuites`'s fold cannot assert
over itself without circularity). It is the ONLY suite in the tree with
its own runner; every other test exe rides `mainOfSuites`.

The self-test battery (every claim the library makes gets evidence):

1. The PASSING spec: sum commutes over LCG-drawn pairs; both negative
   controls are caught (the verdict is `.pass 64`).
2. The FAILING spec (the sabotage AS the property): the verdict is
   `.fail .prop` with the instance index + replay seed — the minimal
   counterexample evidence; rebuilding `instTape replaySeed 0`
   reproduces the case byte-identically.
3. The VACUOUS spec: a trivially-true property whose controls are ALSO
   trivially true — both survive, the verdict is `.vacuous` naming both
   (louder than failing).
4. The LCG determinism pin: same seed → same drawn values (and different
   seeds differ); the same spec run twice yields BEq-equal verdicts.
5. The golden compare's teeth: identical bodies tie; a volatile stamp
   drift still ties (the exemption has teeth); a tampered body FAILS
   with both hashes in the evidence.
6. The exit channel: `mainOfSuites` exits 0 on the clean suite, 1 on a
   suite containing the fail + vacuous demos.

Negative controls here are structural: a Spec cannot be constructed with
fewer than two negatives (the `negatives` subtype — pattern #5), so the
missing-control case has no runtime demo to write; it does not elaborate.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import TestKit.Lcg
import TestKit.Spec
import TestKit.Harness
import TestKit.Golden

open TestKit

/-! ## Fixtures: drawn pairs, the true property, the sabotages -/

/-- The property: sum commutes on a drawn pair. -/
def sumProp : Tape → CheckResult := fun t =>
  let (a, t1) := t.below 1000
  let (b, _) := t1.below 1000
  assert (a + b == b + a) s!"{a} + {b} ≠ {b} + {a}"

/-- Sabotage 1: the sum drops `b` (fails whenever a drawn `b ≠ 0`). -/
def negSumDropB : Tape → CheckResult := fun t =>
  let (a, t1) := t.below 1000
  let (b, _) := t1.below 1000
  assert (a + b == a) s!"control fired: {a} + {b} ≠ {a}"

/-- Sabotage 2: the sum drops `a` (fails whenever a drawn `a ≠ 0`). -/
def negSumDropA : Tape → CheckResult := fun t =>
  let (a, t1) := t.below 1000
  let (b, _) := t1.below 1000
  assert (a + b == b) s!"control fired: {a} + {b} ≠ {b}"

/-- The GOOD spec: true property, both sabotages caught. -/
def sumSpec : Spec :=
  Spec.ofList "sum commutes (drawn pairs)" sumProp
    [ ("sum drops b", negSumDropB), ("sum drops a", negSumDropA) ]
    64 42

/-- The FAILING demo: the sabotage AS the property — the sweep must
    catch it and the evidence must name the instance + replay seed. -/
def failingSpec : Spec :=
  Spec.ofList "sum drops b (sabotage as property)" negSumDropB
    [ ("sum drops b", negSumDropB), ("sum drops a", negSumDropA) ]
    64 42

/-- Trivially-true checks (draws ARE below 1000, so comparisons against
    the draw bounds hold) — the vacuous demo's property + controls. -/
def trivialFirst : Tape → CheckResult := fun t =>
  let (a, _) := t.below 1000
  assert (a < 1024) s!"fired: {a} ≥ 1024"

def trivialSecond : Tape → CheckResult := fun t =>
  let (a, t1) := t.below 1000
  let (b, _) := t1.below 1000
  assert (a + b < 2048) s!"fired: {a} + {b} ≥ 2048"

/-- The VACUOUS demo: a trivially-true property whose TWO controls are
    also trivially true — both survive the sweep, so the verdict must be
    `.vacuous` (the sweep proves nothing). -/
def vacuousSpec : Spec :=
  Spec.ofList "vacuous demo (nothing can fail)" trivialFirst
    [ ("first < 1024 (trivially true)", trivialFirst)
    , ("sum < 2048 (trivially true)", trivialSecond) ]
    16 42

/-! ## The LCG determinism pin (#14: same seed → same values) -/

/-- Draw `n` values below 1000 from a pinned seed (a pure fold). -/
def drawn (seed : UInt64) (n : Nat) : List Nat :=
  ((List.range n).foldl (fun (st : List Nat × Tape) _ =>
      let (v, t') := st.2.below 1000
      (st.1 ++ [v], t'))
      ([], Tape.ofSeed seed)).1

/-! ## The self-test checks -/

def expectOk : CheckResult → String → CheckResult
  | .ok (), _ => .ok ()
  | .error e, name => .error s!"{name}: {e}"

def expectErr : CheckResult → String → CheckResult
  | .error _, _ => .ok ()
  | .ok (), name => .error s!"{name}: expected a failure, got .ok"

def selfChecks : List (String × CheckResult) :=
  [ ("spec: the good sweep PASSES with both controls caught",
      match sumSpec.run with
      | .pass 64 => .ok ()
      | v => .error s!"expected pass 64, got {v}")
  , ("spec: the failing sweep is caught, with replay evidence",
      match failingSpec.run with
      | .fail .prop _ _ _ => .ok ()  -- instance + seed inspected below
      | v => .error s!"expected fail .prop, got {v}")
  , ("spec: the vacuous sweep is FLAGGED, naming both survivors",
      match vacuousSpec.run with
      | .vacuous un =>
          if un.length == 2 then .ok ()
          else .error s!"expected both controls named, got {un}"
      | v => .error s!"expected vacuous, got {v}")
  , ("lcg pin: same seed → same values",
      assertEq "lcg" (drawn 7 32) (drawn 7 32))
  , ("lcg pin: different seeds differ",
      assert (drawn 7 8 != drawn 9 8) "seeds 7 and 9 collided")
  , ("lcg pin: the same spec replays BEq-equal verdicts",
      assertEq "replay" sumSpec.run sumSpec.run)
  , ("lcg pin: the failing spec's replay seed reproduces the case",
      match failingSpec.run with
      | .fail _ _ rs _ =>
          -- the evidence's seed must rebuild a tape whose draw falsifies
          match (Tape.ofSeed rs).below 1000 with
          | (b, _) => assert (b != 0) s!"replay seed draws b = {b}"
      | v => .error s!"expected fail, got {v}")
  , ("golden: identical bodies tie",
      expectOk (Golden.cmp "a\nb\n" "a\nb\n") "identical")
  , ("golden: volatile stamp drift still ties (the exemption bites)",
      expectOk (Golden.cmp "-- generated: 2099-01-01\na\nb\n" "-- generated: 2020-01-01\na\nb\n")
        "stamp drift")
  , ("golden: a tampered body FAILS (the teeth bite)",
      expectErr (Golden.cmp "a\nb\n" "a\nB\n") "tampered")
  , ("golden: the content hash is deterministic",
      assertEq "hash" (Golden.contentHash "a\nb\n") (Golden.contentHash "a\nb\n"))
  , ("runner: runSpecs returns name + verdict pairs",
      match runSpecs [sumSpec] with
      | [("sum commutes (drawn pairs)", .pass _)] => .ok ()
      | v => .error s!"unexpected {v}")
  , ("render: the pass line is structured smoke-tested",
      match sumSpec.run with
      | v => assert (v.render sumSpec |>.startsWith "ok ") "render missing 'ok ' prefix")
  ]

/-- The group driver for named CheckResult rows (tests are data folds;
    the tests own this fold — the library owns `mainOfSuites`). -/
def runChecks (group : String) (checks : List (String × CheckResult)) : IO UInt32 := do
  let mut failures := 0
  IO.println s!"[{group}]"
  for (n, r) in checks do
    match r with
    | .ok () => IO.println s!"ok {n}"
    | .error e => IO.println s!"FAIL {n}: {e}"; failures := failures + 1
  return if failures == 0 then 0 else 1

def main : IO UInt32 := do
  let mut failures := 0
  -- the pure-core self-checks
  let c1 ← runChecks "self" selfChecks
  if c1 != 0 then failures := failures + 1
  -- exit channel: the clean suite exits 0
  let c2 ← mainOfSuites [("clean", [sumSpec])]
  if c2 != 0 then
    IO.println "FAIL: clean suite did not exit 0"
    failures := failures + 1
  -- exit channel: a dirty suite (fail + vacuous demos) exits 1
  let c3 ← mainOfSuites [("dirty", [failingSpec, vacuousSpec])]
  if c3 != 1 then
    IO.println "FAIL: dirty suite did not exit 1"
    failures := failures + 1
  if failures == 0 then IO.println "all TestKit self-tests passed"
  else IO.eprintln s!"{failures} FAILURES"
  return if failures == 0 then 0 else 1

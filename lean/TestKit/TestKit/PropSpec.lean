/-
# TestKit.PropSpec — property tests with a MANDATORY negative control

The vacuous-green lesson (2026-08, decoder sweep): plausible's samplers are
size-bounded, so `∀ n, n < 1000` passes trivially at small sizes — the
suite was green without exercising anything. The fix, systematized: every
property sweep ships a **negative control** — a deliberately-sabotaged
sibling property that the sampler MUST catch. If the control is not caught,
the sweep proves nothing, and the suite FAILS.

```lean
def mySpec : PropSpec "my property" propSuite
  (control := sabotagedSuite) (controlName := "sabotaged variant")
```

`PropSpec.runIO` passes iff the property passes AND the control is caught.
Both are reported; a vacuous property is louder than a failing one.

The property suites are `LSpec.TestSeq`s built with `checkPlausibleIO`
(seeded, shrinking) — see Substrait/Tests for the reference instance.
-/

import LSpec

namespace TestKit

open LSpec

/-- A property spec: the suite under test plus its negative control. -/
structure PropSpec where
  /-- Display name. -/
  name : String
  /-- The property suite (must PASS). -/
  suite : TestSeq
  /-- The sabotaged sibling (must FAIL — proves the sampler bites). -/
  control : TestSeq
  /-- Display name for the control (what sabotage was applied). -/
  controlName : String

/-- Run one spec: property passes, control is caught. Returns the LSpec
    report strings for the caller to print. -/
def PropSpec.runIO (ps : PropSpec) : IO (Bool × String) := do
  let (propOk, propMsg) ← ps.suite.runIO
  let (controlCaught, controlMsg) ← ps.control.runIO
  -- the control is EXPECTED to fail: caught = not-ok
  let ok := propOk && !controlCaught
  let verdict :=
    if ok then s!"✓ {ps.name} (property passed; control caught)"
    else if !propOk then s!"× {ps.name}: PROPERTY FAILED:\n{propMsg}"
    else s!"× {ps.name}: VACUOUS — the negative control ({ps.controlName}) \
          was NOT caught; the sweep proves nothing. Widen the generator or \
          sharpen the sabotage.\nControl output:\n{controlMsg}"
  return (ok, verdict)

/-- Run a list of specs; exit-code semantics for drivers. -/
def runSpecs (specs : List PropSpec) : IO UInt32 := do
  let mut failures := 0
  for ps in specs do
    let (ok, verdict) ← ps.runIO
    IO.println verdict
    if !ok then failures := failures + 1
  return if failures == 0 then 0 else 1

end TestKit

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

A sweep with MULTIPLE delivery classes runs its suite ONCE against N
controls (the ONE-suite/N-controls form — `controls`, default empty): the
property is sampled a single time, and EVERY control must be caught (each
is a coverage witness for one constructor family). The substrait expression
sweep is the reference: one `exprSuite`, three controls (calls / if_then /
casts) — previously three PropSpecs re-sampled the same suite three times.

The property suites are `LSpec.TestSeq`s built with `checkPlausibleIO`
(seeded, shrinking) — see Substrait/Tests for the reference instance.
-/

module

public import LSpec
public import TestKit.Harness

@[expose] public section

namespace TestKit

open LSpec

/-- A property spec: the suite under test plus its negative control(s). -/
structure PropSpec where
  /-- Display name. -/
  name : String
  /-- The property suite (must PASS). -/
  suite : TestSeq
  /-- The sabotaged sibling (must FAIL — proves the sampler bites). Used
      in the single-control form, when `controls` is empty. -/
  control : TestSeq := .done
  /-- Display name for the control (what sabotage was applied). -/
  controlName : String := ""
  /-- MULTI-CONTROL FORM: when non-empty, the suite runs ONCE and every
      listed (name, sabotaged suite) must FAIL — each is a coverage
      witness for one fragment of the generator. `control`/`controlName`
      are ignored in this form (kept with defaults so the single-control
      call sites construct unchanged). -/
  controls : List (String × TestSeq) := []

/-- Run one spec: property passes, control(s) are caught. Returns the LSpec
    report strings for the caller to print. -/
def PropSpec.runIO (ps : PropSpec) : IO (Bool × String) := do
  if ps.controls.isEmpty then
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
  else do
    -- the multi-control form: the suite executes ONCE; every control must
    -- be caught (a not-caught control = vacuity, louder than a failing
    -- property — the single-control discipline, extended to N witnesses).
    let (propOk, propMsg) ← ps.suite.runIO
    let mut uncaught : List (String × String) := []
    for (cn, csuite) in ps.controls do
      let (passes, cmsg) ← csuite.runIO
      -- a control is CAUGHT when its sabotaged suite FAILS (passes = false)
      if passes then uncaught := uncaught ++ [(cn, cmsg)]
    if !propOk then
      return (false, s!"× {ps.name}: PROPERTY FAILED:\n{propMsg}")
    if uncaught.isEmpty then
      return (true, s!"✓ {ps.name} (property passed; {ps.controls.length} \
        controls caught)")
    let vac := String.intercalate "\n"
      (uncaught.map fun (n, m) =>
        s!"  control '{n}' was NOT caught; the sweep proves nothing.\n{m}")
    return (false, s!"× {ps.name}: VACUOUS — \
      {uncaught.length}/{ps.controls.length} controls not caught:\n{vac}")

/-- Run a list of specs; exit-code semantics for drivers. -/
def runSpecs (specs : List PropSpec) : IO UInt32 :=
  runVerdicts specs fun ps => ps.runIO

end TestKit

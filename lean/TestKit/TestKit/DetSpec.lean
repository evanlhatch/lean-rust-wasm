/-
# TestKit.DetSpec — PropSpec's discipline for deterministic checks

PropSpec enforces positive-pass + control-caught for plausible sweeps.
Deterministic `CheckResult` suites hand-reinvent the same pattern at call
sites today (doctrine §4: "Deterministic checks deserve the same +/−
control discipline as PropSpec"). DetSpec is that discipline, once:

```lean
def mySpec : DetSpec := ⟨"lower preserves nullability",
  checkOk, sabotagedCheck, "nullability dropped"⟩
```

`DetSpec.run` is pure (`PropSpec.runIO`'s shape without the TestSeq IO):
the check must be `.ok`, the control must be `.error`. A control that
PASSES is vacuous — louder than a failure, because the suite then proves
nothing.
-/

import TestKit.Harness

namespace TestKit

/-- A deterministic spec: the check under test plus its negative control. -/
structure DetSpec where
  /-- Display name. -/
  name : String
  /-- The deterministic check (must be `.ok`). -/
  check : CheckResult
  /-- The sabotaged sibling (must be `.error` — proves the check bites). -/
  control : CheckResult
  /-- Display name for the control (what sabotage was applied). -/
  controlName : String

/-- Run one spec, pure: returns (passed?, verdict). Mirrors
    `PropSpec.runIO`'s messaging: a vacuous control is louder than a
    failing check. -/
def DetSpec.run (ds : DetSpec) : Bool × String :=
  let propOk := match ds.check with | .ok () => true | .error _ => false
  let controlCaught := match ds.control with | .ok () => false | .error _ => true
  let ok := propOk && controlCaught
  let verdict :=
    if ok then s!"✓ {ds.name} (check passed; control caught)"
    else if !propOk then
      match ds.check with
      | .error e => s!"× {ds.name}: CHECK FAILED: {e}"
      | .ok () => s!"× {ds.name}: CHECK FAILED"
    else
      match ds.control with
      | .ok () => s!"× {ds.name}: VACUOUS — the negative control ({ds.controlName}) \
          PASSED; the suite proves nothing. Sharpen the sabotage."
      | .error _ => s!"× {ds.name}: VACUOUS — the negative control ({ds.controlName}) \
          was not caught."
  (ok, verdict)

/-- Run a list of specs; prints verdicts, exit-code semantics for drivers. -/
def runDets (specs : List DetSpec) : IO UInt32 := do
  let mut failures := 0
  for ds in specs do
    let (ok, verdict) := ds.run
    IO.println verdict
    if !ok then failures := failures + 1
  return if failures == 0 then 0 else 1

end TestKit

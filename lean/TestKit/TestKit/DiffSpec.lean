/-
# TestKit.DiffSpec — corruption-negative discipline for golden/differential gates

PropSpec enforces positive-pass + control-caught for plausible sweeps;
DetSpec does it for deterministic checks. Golden/differential gates (the
byte-tie fold, the wasm differential oracle) had NO equivalent: the wasm
differential smoke shipped only positive invokes. Provenance: flatland's
`Tests/ReplayGate.lean:50-77` — after the positive golden fold, ≥2
engineered corruptions that MUST fail, and each failure must NAME context
(tick, column). An "unexpectedly succeeded" corruption is a gate failure,
louder than a check failure: the oracle is vacuous.

DiffSpec is that discipline, once:

```lean
let spec : DiffSpec := ⟨"oracle rejects sabotaged rows",
  check cleanInput,                       -- positive: must be `.ok`
  [ corrupt "oversized cell" setAt999 cleanInput check ["row 0", "bound"]
  , corrupt "renamed column" rename cleanInput check ["column"] ]⟩
```

A `Corruption` is the check's result on sabotaged input (must be
`.error`) plus the context substrings the error MUST carry
(`expectErrorContaining` from Harness — substring pin-checking, not a
replacement for structured diagnostics, doctrine §4). The discipline is
≥2 corruptions per gate; an EMPTY corruption list is flagged vacuous.
-/

import TestKit.Harness

namespace TestKit

/-- One engineered corruption: the check's result on sabotaged input
    (must be `.error`), plus the context the error must name. -/
structure Corruption where
  /-- Display name (what sabotage was applied). -/
  name : String
  /-- The check's result on the sabotaged input (must be `.error` —
      proves the gate bites). -/
  result : CheckResult
  /-- Context substrings the error MUST contain (flatland's
      tick/column lesson: a bare "mismatch" error is not enough). -/
  expectErrorContaining : List String := []

/-- Build a corruption declaratively: sabotage the input, run the check,
    keep the error. -/
def corrupt (name : String) (sabotage : α → α) (input : α)
    (check : α → Except String β) (expectErrorContaining : List String := []) : Corruption :=
  ⟨name,
    match check (sabotage input) with
    | .ok _ => .ok ()
    | .error e => .error e,
    expectErrorContaining⟩

/-- A golden/differential spec: the positive case (must pass) plus its
    engineered corruptions (each must fail, naming context). -/
structure DiffSpec where
  /-- Display name. -/
  name : String
  /-- The positive golden/differential case (must be `.ok`). -/
  check : CheckResult
  /-- The engineered corruptions (each must be `.error` naming its
      context — the anti-theater discipline is ≥2). -/
  corruptions : List Corruption

/-- Run one corruption: `.ok` is a gate failure ("unexpectedly
    succeeded"); `.error` must carry every required context substring.
    Returns `none` when the corruption behaves, `some why` otherwise. -/
def Corruption.run (c : Corruption) : Option String :=
  match c.result with
  | .ok () =>
    some s!"corruption '{c.name}' unexpectedly succeeded — the gate \
      proves nothing. Sharpen the sabotage or the check."
  | .error e =>
    match TestKit.expectErrorContaining c.expectErrorContaining (.error e : CheckResult) with
    | .ok () => none
    | .error why => some s!"corruption '{c.name}' was rejected, but the error lacks context: {why}"

/-- Run one spec, pure: returns (passed?, verdict). Mirrors
    `DetSpec.run`'s messaging: a passing corruption is louder than a
    failing check. ALL misbehaving corruptions are reported, not just
    the first. -/
def DiffSpec.run (ds : DiffSpec) : Bool × String :=
  match ds.check with
  | .error e => (false, s!"× {ds.name}: CHECK FAILED: {e}")
  | .ok () =>
    if ds.corruptions.isEmpty then
      (false, s!"× {ds.name}: VACUOUS — no corruptions; a differential gate \
        without engineered negatives proves nothing (the discipline is ≥2).")
    else
      let bad := ds.corruptions.filterMap Corruption.run
      if bad.isEmpty then
        (true, s!"✓ {ds.name} (positive passed; {ds.corruptions.length} \
          corruptions rejected with context)")
      else
        (false, s!"× {ds.name}: GATE FAILURE\n" ++
          String.intercalate "\n" (bad.map ("  - " ++ ·)))

/-- Run a list of specs; prints verdicts, exit-code semantics for drivers. -/
def runDiffs (specs : List DiffSpec) : IO UInt32 :=
  runVerdicts specs fun ds => pure ds.run

end TestKit

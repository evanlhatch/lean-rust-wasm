/-
# TestKit.Harness — the check runner + the verdict rendering + the driver

Owned by: the TestKit agent (the macht tree, `testkit/`).
Driving decisions: notes/v3/15-patterns.md #5 (the negatives MUST fail —
an uncaught control is the vacuity tripwire, louder than a failing
property) + #14 (the LCG discipline — the sweep is a pure fold over
pinned-seed tapes; failure evidence names the replay seed) +
notes/v3/04-verification.md §6 (verdicts are ctors, never strings — the
run is pure and structured; rendering is a separate surface).

Mined from: legacy/lean/TestKit/TestKit/PropSpec.lean (runIO's three-way
outcome: property failure / control caught / VACUOUS) + Harness.lean
(runVerdicts' driver loop + mainOfSuites' exit-code semantics). Fresh
here: no LSpec — the runner is a pure fold (`Spec.run : Spec → Verdict`),
the renderer turns ctors into lines, and `mainOfSuites` owns the only
IO: print + summary + exit channel.

The five questions (notes/v3/01-core.md):
- root: none — the verdict machinery over TestKit.Spec's suites.
- carrier grade: verdicts as constructors (never strings) — structured
data, rendering separate.
- spine reading: none — the run is a pure fold; the driver owns the
only IO.
- ladder rung: rung 1 — structural; the vacuity tripwire is a ctor.
- gate row: none — TestKit is outside Gates.Packages' gated set; the
test exes are its consumers.
-/

module

public import TestKit.Spec

@[expose] public section

namespace TestKit

/-- Instance `i`'s tape: `(i+1)` LCG steps from the pin — deterministic,
    disjoint per instance, replayable from `(seed, i)`. -/
def instTape (seed : UInt64) (i : Nat) : Tape := (Tape.ofSeed seed).advance (i + 1)

/-- The replay seed of instance `i`'s tape (the fail evidence's pin:
    rebuild `instTape replaySeed 0` to reproduce the case byte-identically). -/
def replaySeedOf (seed : UInt64) (i : Nat) : UInt64 := (instTape seed i).state

/-- Fold a property over the sweep; the FIRST failure wins.
    `none` = the property held on every instance. -/
def firstFailure (seed : UInt64) (numInst : Nat) (f : Tape → CheckResult) :
    Option (Nat × String) :=
  (List.range numInst).foldl (fun acc i =>
    match acc with
    | some _ => acc
    | none =>
        match f (instTape seed i) with
        | .ok () => none
        | .error e => some (i, e))
    none

/-- Run one spec — pure, structured: the seeded sweep (the prop must hold
    on every instance), the negatives must FAIL (each is a coverage
    witness), the vacuity tripwire (an uncaught control is louder than a
    failing property — but a failing property is reported first). -/
def Spec.run (sp : Spec) : Verdict :=
  match firstFailure sp.seed sp.numInst sp.prop with
  | some (i, e) => .fail .prop i (replaySeedOf sp.seed i) e
  | none =>
      let uncaught := sp.negatives.1.filterMap fun (n, f) =>
        match firstFailure sp.seed sp.numInst f with
        | none => some n
        | some _ => none
      match uncaught with
      | [] => .pass sp.numInst
      | _ => .vacuous uncaught

/-- Render a verdict as a line — structured at the core (Verdict's
    ctors), linear at the surface. Never the sole evidence: consumers
    pattern-match the Verdict, the render is for humans. -/
def Verdict.render (sp : Spec) : Verdict → String
  | .pass n =>
      s!"ok {sp.name}: PASS ({n} instances, {sp.negatives.1.length} controls caught, seed {sp.seed})"
  | .fail src i rs m =>
      let who := match src with
        | .prop => "property"
        | .control c => s!"control '{c}'"
      s!"FAIL {sp.name}: {who} broke at instance {i} (replay seed {rs}): {m}"
  | .vacuous un =>
      s!"FAIL {sp.name}: VACUOUS — {un.length}/{sp.negatives.1.length} controls NOT caught " ++
      s!"({String.intercalate ", " un}); the sweep proves nothing. " ++
      s!"Widen the generator or sharpen the sabotage."

/-- Run a list of specs, pure: name + verdict per spec. -/
def runSpecs (specs : List Spec) : List (String × Verdict) :=
  specs.map fun sp => (sp.name, sp.run)

/-- The test-exe driver: run every suite, render each verdict, one
    summary line, and the exit channel (0 iff every spec passed).
    The only IO in the kit. -/
def mainOfSuites (suites : List (String × List Spec)) : IO UInt32 := do
  let mut failures := 0
  let mut total := 0
  for (group, specs) in suites do
    IO.println s!"[{group}]"
    for sp in specs do
      let v := sp.run
      IO.println (v.render sp)
      total := total + 1
      match v with
      | .pass _ => pure ()
      | _ => failures := failures + 1
  IO.println s!"{total - failures}/{total} specs passed"
  return if failures == 0 then 0 else 1

end TestKit

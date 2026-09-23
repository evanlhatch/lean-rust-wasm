/-
# TestKit.MutSpec — mutation batteries over checkers (F1, the shift-left endpoint)

DetSpec pins ONE negative control; DiffSpec pins engineered corruptions.
A mutation battery pins a WHOLE MUTANT FAMILY at once: the checker under
test must refuse every mutant of a known-good base. `MutSpec` is that
discipline, once:

```lean
def wfBattery : MutSpec "universeCheck bites" baseUniverse
    mutateItem                     -- the mutant grammar (α → List α)
    (fun items => (universeCheck items).isEmpty)  -- the checker under test
    4                              -- refusalsExpected
```

`MutSpec.run` enforces FIVE gates, in order:

1. **POSITIVE** — `check base = true`. A battery whose checker refuses
   its own base is inverted: it can never exercise refusal.
2. **TEETH** — `refusalsExpected > 0`. A battery that declares no
   refusals is a vacuous declaration; it proves nothing.
3. **GRAMMAR NONEMPTY** — `mutate base` must not be `[]`. A grammar that
   produces zero mutants (a splice that silently no-ops on the base) is
   vacuous — LOUDER than a failing battery: the sweep exercised nothing.
4. **GRAMMAR DRIFT** — `(mutate base).length == refusalsExpected`. A
   mutant that vanishes silently is a silent loss of coverage; the
   declared count is pinned at run time, so the grammar cannot shrink
   without review.
5. **ALL REFUSED** — every mutant must be refused (`check m = false`). A
   surviving mutant is the loudest failure: the checker does not bite.

The GENERATIVE lane (`MutSpec.runGen`): the mutant SET is drawn from a
seeded `Plausible.Gen (List α)` through `TestKit.runGenPure` (pinned seed
AND size — the grammar itself is seeded). Same seed = same battery (the
snapshot-fixtures byte-tie law). Gates 3-5 run over the DRAWN set, so a
generator that silently trims its output fails the drift gate the same
way a hand-written grammar does.

Deliberate exclusions, matching the sibling Spec modules: no shrinking
(the battery is deterministic — a pinned seed, no search loop), no IO
inside a check (`run` is a pure `CheckResult`; drivers print via
`runMuts`), no `ToString` requirement on `α` (the survivor error names
the mutant's INDEX, not its body — keep `α` arbitrary).
-/

module

public import TestKit.Harness
public import Plausible.Gen
public import TestKit

@[expose] public section

namespace TestKit

/-- A mutation battery: a known-good base, a mutant grammar, the checker
    under test, and the DECLARED number of mutants the grammar must
    produce. `refusalsExpected` is the vacuity guard: 0 = a battery with
    no teeth; a live count mismatch = a silently-shrunk grammar. -/
structure MutSpec (α : Type) where
  /-- Display name. -/
  name : String
  /-- The known-good input (the checker MUST accept it). -/
  base : α
  /-- The mutant grammar: one leaf/ctor-swap per mutant. -/
  mutate : α → List α
  /-- The checker under test: `true` = accepts. -/
  check : α → Bool
  /-- Declared mutant count the grammar MUST produce (vacuity + drift
      guard). -/
  refusalsExpected : Nat

/-- Run one battery: the five gates (positive, teeth, grammar nonempty,
    drift, all-refused) in order. Pure. -/
def MutSpec.run {α : Type} (ms : MutSpec α) : CheckResult :=
  if !ms.check ms.base then
    .error s!"{ms.name}: POSITIVE FAILED — the checker refused the base; a \
      battery needs a base the checker accepts (`check base = true`)"
  else if ms.refusalsExpected == 0 then
    .error s!"{ms.name}: VACUOUS — refusalsExpected is 0; a battery that \
      declares no refusals proves nothing (the discipline floor is one)"
  else
    let mutants := ms.mutate ms.base
    if mutants.length == 0 then
      .error s!"{ms.name}: VACUOUS — the mutation grammar produced ZERO \
        mutants (declared {ms.refusalsExpected}); a checker with nothing to \
        refuse proves nothing. Fix the grammar or the base."
    else if mutants.length != ms.refusalsExpected then
      .error s!"{ms.name}: GRAMMAR DRIFT — the grammar produced \
        {mutants.length} mutants but declared {ms.refusalsExpected}. A \
        mutant that vanished silently is a silent coverage loss; align the \
        counts."
    else
      match mutants.zipIdx.find? (fun (m, _) => ms.check m) with
      | none => .ok ()
      | some (_, i) =>
        .error s!"{ms.name}: MUTANT SURVIVED — the checker ACCEPTED mutant \
          {i} of {ms.refusalsExpected}. The checker does not bite; sharpen \
          the mutation or the checker."

/-- The generative lane: draw the mutant SET from a seeded grammar and run
    the full discipline over the drawn set. `runGenPure` pins seed AND
    size — the same seed reproduces the same battery. -/
def MutSpec.runGen {α : Type} (ms : MutSpec α) (g : Plausible.Gen (List α))
    (seed size : Nat) : CheckResult :=
  match TestKit.runGenPure g seed size with
  | .error (.genError msg) => .error s!"{ms.name}: generative grammar draw failed: {msg}"
  | .ok mutants => { ms with mutate := fun _ => mutants }.run

/-- Fold a battery of specs (same `α`) into one CheckResult, naming each
    failure (first failure wins — Harness.allOf). -/
def MutSpec.runMany {α : Type} (specs : List (MutSpec α)) : CheckResult :=
  allOf (specs.map fun ms => (ms.name, ms.run))

/-- The (passed, verdict) reading for drivers (the DetSpec/DiffSpec
    shape). -/
def MutSpec.verdict {α : Type} (ms : MutSpec α) : Bool × String :=
  match ms.run with
  | .ok () =>
    (true, s!"✓ {ms.name}: base accepted, {ms.refusalsExpected} mutants refused")
  | .error e => (false, s!"× {ms.name}: {e}")

/-- Run a list of specs; prints verdicts, exit-code semantics for drivers
    (mirrors `runDets`/`runDiffs`). -/
def MutSpec.runMuts {α : Type} (specs : List (MutSpec α)) : IO UInt32 :=
  runVerdicts specs fun ms => pure ms.verdict

end TestKit

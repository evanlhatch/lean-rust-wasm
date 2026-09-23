/-
# TestKit.Baseline — the one gate record + the shared run loop

The wave's F2 doctrine: *a new baseline = one record*. Every drift gate's
shape is the same — a committed artifact at `path`, a fresh regeneration,
an acceptance predicate, a deliberate re-baseline lane, and a typed
digest-ish description of what the gate binds. This module owns that
shape once. Import-free by design: the gates' cheapest module
(Gates.Manifest, `Lean`-only today) must be able to require the record
without dragging in LSpec or the sweep machinery.

The `compare` contract: `compare committed fresh` answers "does the
committed artifact satisfy the gate, given the fresh regeneration?".
Two gate classes:

- ARTIFACT gates (gen-check per artifact, coverage, axiom report): the
  committed side is read from `path` by `runBaseline` and compared
  against the regenerated text. Absent/unreadable baselines FAIL —
  a vanished baseline verifies nothing.
- COMPUTED gates (no committed artifact — the gate IS the computation):
  `regenerate` produces the gate's finding text and `compare` judges it
  (`_committed` unused; the gate's verdict is over `fresh` alone —
  e.g. "empty findings = clean"). These route through `runComputed`,
  which skips the `path` read; `path` still names the audited surface
  for the report.

`write` is the deliberate re-baseline lane. The checkers (gen-check,
manifest-check, docs-check) refuse it with a descriptive `IO.userError`;
a writable gate (coverage) writes the committed artifact. The loop below
is CHECK-only — it never calls `write`; the `--write` modes keep their
own existing drivers (Gates.Driver.reportGate's accept-drift discipline).

Ownership: new here; f2 wave. The verdict loop reuses the `runVerdicts`
shape (TestKit.Harness): per-item `IO (Bool × String)` rows, a failure
count, an exit code.
-/

module

@[expose] public section

namespace TestKit

/-- One gate, as a baseline record (the F2 doctrine). The six fields the
    gates share: the committed artifact path, the fresh regeneration, the
    acceptance predicate over (committed, regenerated), the deliberate
    re-baseline lane, the typed digest-ish evidence, and the gate's name
    (the report rows and count lines key on it). -/
structure Baseline where
  path : System.FilePath
  regenerate : IO String
  compare : String → String → Bool
  write : String → IO Unit
  evidence : String
  name : String

/-- The pure check core: apply the gate's acceptance predicate to a
    (committed, fresh) pair. Tests and drivers call this directly; the
    IO entry points below only source the two strings. -/
def Baseline.check (b : Baseline) (committed fresh : String) : Bool :=
  b.compare committed fresh

/-- Check semantics: run the regeneration, read the committed artifact at
    `path`, and apply `compare`. A missing or directory `path` is a
    FAILED verdict — a gate whose baseline vanished (or never existed)
    verifies nothing. Never writes. -/
def runBaseline (b : Baseline) : IO Bool := do
  unless ← b.path.pathExists do return false
  if ← b.path.isDir then return false
  let fresh ← b.regenerate
  let committed ← IO.FS.readFile b.path
  pure (b.compare committed fresh)

/-- The COMPUTED-gate check: a gate with no committed artifact runs its
    regeneration and lets `compare` judge the finding text (the committed
    side is empty — there is no on-disk baseline to read; `path` names
    the audited surface only). -/
def runComputed (b : Baseline) : IO Bool := do
  let fresh ← b.regenerate
  pure (b.compare "" fresh)

/-- The one-line verdict for a run: `✓ in sync` / `✗ <detail>` with the
    evidence suffix (the "run → verdict" row the loops print). -/
def verdictLine (b : Baseline) (ok : Bool) (detail : String) : String :=
  if ok then s!"✓ {b.name}: run — in sync ({b.evidence})"
  else s!"✗ {b.name}: run — {detail} ({b.evidence})"

/-- The artifact-gate verdict row: `runBaseline` + its one-line verdict
    (a missing/absent baseline names itself in the row). -/
def baselineVerdict (b : Baseline) : IO (Bool × String) := do
  let ok ← runBaseline b
  pure (ok, verdictLine b ok
    (if ok then "in sync"
     else s!"DIFFERS/absent at {b.path}"))

/-- The COMPUTED-gate verdict row (see `runComputed`). -/
def computedVerdict (b : Baseline) : IO (Bool × String) := do
  let ok ← runComputed b
  pure (ok, verdictLine b ok
    (if ok then "clean"
     else "findings — see the gate's report"))

/-- The shared gates loop (C5): step every baseline through its check,
    print each "run → verdict" row, count the failures, print the count
    line, and return the exit code. Same shape as `runVerdicts` (specs ×
    verdict getter → rows → exit code); the baseline rows carry the
    record's evidence instead of a per-spec message. -/
def runBaselines (what : String) (get : Baseline → IO (Bool × String))
    (bs : List Baseline) : IO UInt32 := do
  let mut failures := 0
  for b in bs do
    let (ok, verdict) ← get b
    IO.println verdict
    if !ok then failures := failures + 1
  IO.println s!"{what}: {bs.length} baseline(s) run, {failures} failed"
  return if failures == 0 then 0 else 1

end TestKit

end -- @[expose] public section

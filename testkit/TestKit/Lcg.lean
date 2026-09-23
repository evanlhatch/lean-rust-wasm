/-
# TestKit.Lcg — the deterministic seeded generator (fresh, core-only)

Owned by: the TestKit agent (the macht tree, `testkit/`).
Driving decision: notes/v3/15-patterns.md #14 (the LCG discipline) —
generated data is seeded + deterministic; a failing case replays
byte-identically from its seed; "works on my seed" is never a bug report.

Mined from: legacy/lean/TestKit/TestKit.lean — the exact Knuth-64
recurrence (`s * 6364136223846793005 + 1442695040888963407`) and the
same-seed-replay discipline. Fresh here: the Plausible/`Gen` plumbing is
dropped (TestKit must not depend on Plausible/LSpec) and replaced by the
byte-tape reader — a pure, total reader over the LCG stream from which
any consumer folds its own fixtures.

Deliberate exclusions: no shrinking engine (the Spec's `shrinkNote` field
is a note until its first consumer — the leftover rule); no IO, no global
RNG state (the seeded sweep is a pure fold). Modulo bias in `Tape.below`
is accepted for a test kit and stated at the definition.

The five questions (notes/v3/01-core.md):
- root: Universe — one pure recurrence + a total tape reader.
- carrier grade: none — plain data (UInt64 state, pure draws).
- spine reading: none — the evidence discipline's substrate.
- ladder rung: rung 1 — `rfl`/structural; same-seed replay is by
construction.
- gate row: none — TestKit is outside Gates.Packages' gated set;
TestKitTests self-tests the tape discipline.
-/

module

@[expose] public section

namespace TestKit

/-- The shared deterministic LCG (Knuth 64): the stream's one recurrence.
    Mined verbatim from legacy TestKit — every consumer used to hand-copy
    these constants; TestKit owns the single copy. -/
def lcg : UInt64 → UInt64 := fun s => s * 6364136223846793005 + 1442695040888963407

/-- The byte-tape reader state: one UInt64 of LCG state. All draws are
    pure functions `Tape → value × Tape` — same tape, same value, so a
    failing case replays byte-identically from its seed (pattern #14). -/
structure Tape where
  state : UInt64
deriving BEq, Repr

/-- A fresh tape pinned to `seed`. -/
def Tape.ofSeed (s : UInt64) : Tape := ⟨s⟩

/-- One LCG step. -/
def Tape.step (t : Tape) : Tape := ⟨lcg t.state⟩

/-- Advance the tape `n` steps without drawing. -/
def Tape.advance (t : Tape) : Nat → Tape
  | 0 => t
  | n + 1 => t.step.advance n

/-- Draw one byte: the top 8 bits of the next state. -/
def Tape.byte (t : Tape) : UInt64 × Tape :=
  let s := lcg t.state
  (s >>> 56, ⟨s⟩)

/-- Draw a Nat below `bound` (`bound > 0`): the high bits of the next
    state, mod `bound`. Modulo bias is accepted for a test kit — noted
    here, not hidden. -/
def Tape.below (t : Tape) (bound : UInt64) : Nat × Tape :=
  let s := lcg t.state
  (((s >>> 16) % bound).toNat, ⟨s⟩)

end TestKit

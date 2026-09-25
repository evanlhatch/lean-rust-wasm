/-
# TestingKit.Lcg — the deterministic seeded generator (fresh, core-only)

Owned by: the TestingKit agent (the mandate tree, `testingkit/`).
Driving decision: notes/v3/15-patterns.md #14 (the LCG discipline) —
generated data is seeded + deterministic; a failing case replays
byte-identically from its seed; "works on my seed" is never a bug report.

Mined from: legacy/lean/TestingKit/TestingKit.lean — the exact Knuth-64
recurrence (`s * 6364136223846793005 + 1442695040888963407`) and the
same-seed-replay discipline. Fresh here: the Plausible/`Gen` plumbing is
dropped (TestingKit must not depend on Plausible/LSpec) and replaced by the
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
- gate row: TestingKit's row in Gates.Packages' gated set (the
  per-library axiom sweep covers it); TestingKitTests self-tests the
  tape discipline.
-/

module

@[expose] public section

namespace TestingKit

/-- The shared deterministic LCG (Knuth 64): the stream's one recurrence.
    Mined verbatim from legacy TestingKit — every consumer used to hand-copy
    these constants; TestingKit owns the single copy. -/
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

/-! ## The shared drawers (the domain cores' sweep faces draw through
    THESE — one copy, the seeded-sweep discipline) -/

/-- One char from a small alphabet (the drawer's leaf). Mined verbatim
    from SchemaCore.Derive's sweep face — the HOME is here (C0 testingkit;
    the domain cores import, never hand-copy; the next schemacore wave's
    adoption is a delete-and-import). -/
def drawChar (t : Tape) : Char × Tape :=
  let p := t.below 4
  ((['a', 'b', 'c', 'd'])[p.1]!, p.2)

/-- The structural repeat: draw `n` values. -/
def drawMany : Nat → (Tape → α × Tape) → Tape → List α × Tape
  | 0, _, t => ([], t)
  | n + 1, draw, t =>
      let (x, t) := draw t
      let (xs, t) := drawMany n draw t
      (x :: xs, t)

/-- The structural repeat over an OPTIONAL drawer (`none` propagates —
    the loud gap, never a silent shorter list). -/
def drawManyO : Nat → (Tape → Option (α × Tape)) → Tape →
    Option (List α × Tape)
  | 0, _, t => some ([], t)
  | n + 1, draw, t =>
      (draw t).bind fun p =>
        (drawManyO n draw p.2).map fun q => (p.1 :: q.1, q.2)

/-- A short string (length < 4) over the small alphabet. -/
def drawString (t : Tape) : String × Tape :=
  let p := t.below 4
  let (cs, t) := drawMany p.1 drawChar p.2
  (String.ofList cs, t)

end TestingKit

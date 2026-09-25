/-
# GuestTests.StdFixture — the std functions the compiled lane reads

The GuestStdTests twin of `GuestTests.Fixture`: plain `def`s — the
STD functions, marked `@[guest_std]` (the elaboration-time gate checks
the ban closure; the mark registry records the compile roots) — whose
impure-phase LCNF the driver reads IN-PROCESS (the Lcnf re-run
discipline: the impure phase is not persisted in oleans).

- `demoSum` — the end-to-end target: `GuestStd.sumU64` over a list
  literal (the cons-chain construction + the self-recursive fold —
  the list discipline's real face). The literal lifts to the
  `_closed` family (the listMain pattern); the driver reads root +
  family from ONE pipeline run.
- `demoLen` — the second compiled target: `GuestStd.listLenU64` (the
  heads ride UNOPENED — the honest boundary, no string op compiles).

The five questions (notes/v3/01-core.md): the fixture is the test
lane's Universe face — the answers live at the consumers
(GuestStdTests.Main's driver). Gate row: `GuestStdTestsLib`'s row.
-/

import LintKit.GuestGate
import Guest.Std

/-- The 3-element agreement target (the FORMER known-divergence pin,
    flipped): the std fold over the 3-element literal (the `_closed`
    family face — the listMain pattern). The native answer is 18; the
    COMPILED lane now agrees — the bump allocator's non-overlap law
    (Lower.lean's allocSeq: the object's address is the bump pointer,
    the bump advances past the object) fixed the cons-tail clobber
    (GuestStdTests suite 5 pins the agreement forever). The 2-element
    sibling `demoSum2` carries the sibling agreement pin. -/
@[guest_std]
def GuestTests.StdFixture.demoSum : UInt64 := GuestStd.sumU64 [7, 8, 3]

/-- THE TWO-ELEMENT agreement target: the proven compiled shape (the
    listSum discipline's width). The native answer is 15; the
    compiled module must agree — GuestStdTests's agreement pin. -/
@[guest_std]
def GuestTests.StdFixture.demoSum2 : UInt64 := GuestStd.sumU64 [7, 8]

/-- THE native-only target: the std count over the literal chain (the
    native answer is 4). NOT a compiled target: the literal's heads
    are STRING objects — the closed-lifted producers are exactly the
    string-box lane this slice does not compile (the honest boundary,
    pinned as the fixture's documented stance). -/
@[guest_std]
def GuestTests.StdFixture.demoLen : UInt64 :=
  GuestStd.listLenU64 ["a", "b", "c", "d"]

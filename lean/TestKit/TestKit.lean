/- TestKit — the shared test harness (harness, golden, PropSpec, DetSpec,
   DiffSpec, GateKit) + the shared deterministic LCG. -/
module

public import Lean
public import Plausible
public import TestKit.Harness
public import TestKit.Golden
public import TestKit.PropSpec
public import TestKit.DetSpec
public import TestKit.DiffSpec
public import TestKit.GateKit

@[expose] public section

namespace TestKit

/-- The shared deterministic LCG (Knuth 64): one copy for every seeded sweep.
    Before this module, each consumer hand-copied the constants
    (6364136223846793005 / 1442695040888963407); now TestKit owns the single copy. -/
def lcg : UInt64 → UInt64 := fun s => s * 6364136223846793005 + 1442695040888963407

/-- Run a Plausible generator deterministically, purely (fixed seed AND
    size — no IO, no global stdGenRef): the seeded sweeps' shared
    runner. -/
def runGenPure {α : Type} (g : Plausible.Gen α) (seed : Nat) (size : Nat) :
    Except Plausible.GenError α :=
  (ReaderT.run (StateT.run g (ULift.up (mkStdGen seed))) ⟨size⟩).map (·.1)

end TestKit

-- Re-export the LSpec names the repo's Tests actually use so Tests files
-- can import TestKit only (testImportDiscipline: Tests/ must not
-- `import LSpec` — TestKit is the blessed surface).
export LSpec (TestSeq test checkPlausibleIO)

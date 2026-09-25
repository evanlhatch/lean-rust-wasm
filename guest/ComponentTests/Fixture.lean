/-
# ComponentTests.Fixture — the guest function the component wraps

The test fixture: a plain `def` compiled normally (the package builds
this module), whose impure-phase LCNF the driver reads IN-PROCESS
(the `Guest.Lcnf` re-run discipline — the impure phase is not
persisted in oleans). The component lane's honest seed wraps ONE
function; the fixture stays minimal on purpose:

- `add64` — the pin: a UInt64 add, exported through the world as the
  component's `add64` func (the canonical-ABI scalar fragment:
  u64 × u64 → u64 — identity flattening, no adapters).

Everything beyond the scalar fragment is the named exclusion set
(`Guest.Component`'s header) — the refusals pin it. The ROOT-LEVEL
name is deliberate: the lowered module exports the decl's own name,
so the world's export func name and the core export agree (`add64`).
-/

import Wit
import Wit.World

/-- THE component pin's guest function. -/
def add64 (a b : UInt64) : UInt64 := a + b

/-- THE demo world: the guest's `add64` exported as data (the
    `Wit.World` carrier). The SSOT the emission is checked against —
    shared by the writer exe (`componentgen`) and the tests. -/
def componentWorld : Wit.World :=
  { name := "guest"
  , imports := []
  , exports :=
      [.func { name := "add64"
             , params := [{ name := "a", ty := .atom .u64 }
                        , { name := "b", ty := .atom .u64 }]
             , result := some (.atom .u64) }] }

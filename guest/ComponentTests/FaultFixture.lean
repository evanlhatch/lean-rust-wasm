/-
# ComponentTests.FaultFixture — the fault-typed result channel's fixture

The component lane's FOURTH fixture (the D6 port): the world whose
export answers the guest's TYPED REFUSAL — `probe : func() ->
result<_, u64>` (`Ty.resultErr`, the one-summand result face the D2
rows landed) — plus the core module that backs it through the
canonical-ABI HEAP-RETURN face.

Why hand-built (the string fixture's precedent, one lane over): the
guest's typed refusal is the boundary's OWN shape — a `result` whose
flattening `[i32 disc, i64 payload]` exceeds `MAX_FLAT_RESULTS` (1)
collapses to the single `i32` return-area POINTER (the ABI's heap
rule, `Guest.Component.flatten`). The committed `probe` writes the
return area DIRECTLY: the `Err` discriminant (`1`) at offset 0, the
fault payload (`42` — the seeded E-code face, `FAULT_GOLDEN` in the
host) at offset 8 (the u64's aligned slot), and returns the pointer
the realloc stub handed it. The guest's internal fault-typing (the
RC/boxed lane) does not enter this fixture — the boundary's honest
minimal, the string fixture's discipline.

The consumers:
- the component emission (the writer `componentgen` + the gate
  `gen-check` — the byte-tie pins the committed artifacts);
- the Rust host (`crates/mandate-host`'s fault lane — the typed
  channel: the guest's `Err(42)` crosses as the host's TYPED error,
  never a trap; the trap face is the distinct negative control there,
  built from WAT by the test, the established pattern).

The five questions (notes/v3/01-core.md): the fixture is data (the
test lane's Universe face) — the answers live at the consumers
(`Guest.Component.check`/`encodeComponent`, the host's fault lane).
-/

import Guest.Component
import Wit
import Wit.World
import WasmCore.Instr
import WasmCore.Module
import WasmCore.Types

open WasmCore

namespace ComponentTests.FaultFixture

/-- THE fault world: `probe : func() -> result<_, u64>` — the guest's
    typed-refusal channel (the one-summand `resultErr` face; the ok
    side is unit). -/
def faultWorld : Wit.World :=
  { name := "guest"
  , imports := []
  , exports :=
      [.func { name := "probe"
             , params := []
             , result := some (.resultErr (.atom .u64)) }] }

/-- THE fault fixture's core module: the adapter face (the exported
    one-page memory + the ABI realloc stub) + the `probe` core func —
    `() -> (i32)`, the heap-return pointer (the flattening's collapse
    past `MAX_FLAT_RESULTS`). The body writes the return area: the
    `Err` disc at +0, the fault payload at +8 (the u64's aligned
    slot), and answers the pointer. -/
def faultModule : WasmCore.Module :=
  { types := [⟨[.i32, .i32, .i32, .i32], [.i32]⟩   -- the ABI realloc
            , ⟨[], [.i32]⟩]                        -- probe (heap return)
  , funcs := [ { tyIdx := 0, locals := [], body := [.i32const 1024] }
             , { tyIdx := 1, locals := [.i32]
               , body := [.i32const 0, .i32const 0       -- the realloc call's args
                         , .i32const 0, .i32const 0
                         , .call 0                       -- ptr = realloc(0,0,0,0)
                         , .localtee 0                   -- keep ptr, leave it as store addr
                         , .i32const 1                   -- the Err discriminant
                         , .mem .i32store 0 (some 2)     -- [ptr] = 1
                         , .localget 0
                         , .i64const 42                  -- the fault payload (FAULT_GOLDEN)
                         , .mem .i64store 8 (some 3)     -- [ptr+8] = 42 (the aligned slot)
                         , .localget 0] } ]             -- answer the pointer
  , exports := [ { name := "canonical_abi_realloc", desc := .func 0 }
               , { name := "probe", desc := .func 1 }
               , { name := "memory", desc := .memory 0 } ]
  , memMin := 1 }

/-- THE FAULT SPEC: the hand-built heap-return module + the world it
    must match (the emission's skew check runs at generation —
    `Guest.Component.regen`; `check` demands the adapter face here:
    the heap result needs the memory + realloc exports). -/
def faultSpec : Guest.Component.Spec :=
  { core := faultModule, world := faultWorld }

end ComponentTests.FaultFixture

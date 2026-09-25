/-
# Faults.Regen — the faults lane's ONE regen (the writer's and the gate's copy)

The env replay + the allocation, composed once: the writer exe
(`lake exe faultsgen`) and the gate (`gates gen-check`) share THIS copy —
never a second encoding (the gen-check discipline; the `wasmgen` precedent).

The replay: `Faults.Spec`'s olean carries the `@[fault]` appends;
`importModules` with extensions replays them into the ONE compile-time
event log (`Kit.Lane.laneLogExt`, wave-30 A2); the reader routes the
log's fold to the fault lane and re-materializes the rows' values. The allocation
then reads the PERSISTED registry (Faults.Alloc's ONE IO face) and looks up
each fault's row — an unallocated fault is the FT0001 refusal, an empty
registry the FT0003 refusal (the legacy `derive_fault_variant`'s shape).

UNSAFE (the interpreter's env replay — the gates' pattern).
Five questions (notes/v3/01-core.md): none of its own — the IO shell over
Alloc (the answers live there). Gate row: gen-check's faults row.
-/

import Lean
import Kit.Lane
import Faults.Registry
import Faults.Alloc
import Faults.Emit

namespace Faults

/-- The ONE regen: the replayed fault registry + the persisted allocation →
    the emitter's spec (or the curated refusal). -/
unsafe def regen : IO (Except String (List (FaultItem × Nat))) := do
  match ← loadRegistry with
  | .error e => return .error e
  | .ok r =>
    try
      Lean.initSearchPath (← Lean.findSysroot)
      let sp ← Lean.searchPathRef.get
      Lean.searchPathRef.set (".lake/build/lib/lean" :: sp)
      Lean.enableInitializersExecution
      let env ← Lean.importModules #[{ module := `Faults.Spec }] {}
        (trustLevel := 1024) (loadExts := true)
      match ← Kit.Lane.runCoreIO env (getFaults env) with
      | .error e => return .error e
      | .ok faults =>
        if faults.isEmpty then
          return .error <| Kit.Diag.toString (Kit.Lane.usageDiag eFT0003
            "no `@[fault]` rows registered — the fold has nothing to \
              allocate; declare faults in Faults.Spec (or the lane's \
              consumers) first")
        return allocAllCheck r faults
    catch e =>
      return .error s!"faults replay: {toString e}"

end Faults

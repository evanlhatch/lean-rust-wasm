/-
# FaultGenMain — the `faultsgen` exe: the byte-tie's writer side

    lake exe faultsgen

Runs `Faults.regen` — the ONE regen shared with `gates gen-check` (never a
second encoding) — and writes the generated Rust face through the Kit.Emit
spine:

- `crates/mandate-faults/src/lib.rs` — the typed-error enum in fast-observe's
  `error!` macro syntax (the macro generates code()/category()/advice() +
  the Coded impl + the registry ENTRIES + the Fault conversions; the
  retryable() policy fn rides the emitter), its 2-line GENERATED header
  inline, its ledger row recorded. NIGHTLY: the generated `Error::provide`
  needs `error_generic_member_access` — crates/rust-toolchain.toml.

ALLOCATION AT GENERATION: the regen reads the persisted registry FIRST — a
fault without its row refuses (FT0001), nothing is written (the validator-at-
generation discipline, the `wasmgen` precedent).

The returned ledger rows have NO file consumer yet (the leftover rule — the
ledger file lands when its reader does; the wasmgen precedent).
Five questions (notes/v3/01-core.md): none of its own — the IO shell over
Faults.Regen. Gate row: none — this exe is gen-check's faults-lane WRITER
side, not a gate.
-/
import Faults

open Faults

unsafe def main : IO UInt32 := do
  match ← regen with
  | .error e =>
    IO.eprintln s!"faultsgen: REGEN FAILED — {e}"
    return 1
  | .ok modes => do
    let _rows ← Kit.Emit.runEmitters "faultsgen"
      [(faultsEmitter, modes)]
      (fun _ f => pure { items := modes.length, contentHash := f.contents.hash })
    IO.println s!"faultsgen: {modes.length} fault(s) rendered — \
      crates/mandate-faults/src/lib.rs written"
    return 0

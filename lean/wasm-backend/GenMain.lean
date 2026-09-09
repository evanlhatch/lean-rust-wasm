import Lean
import Lean.Compiler.LCNF
import WasmBackend

/-!
# WasmBackend.GenMain — the LCNF → WAT artifact writer (spike)

The `leanir` pattern: import the target module's oleans, re-run the LCNF
pipeline (the impure-phase LCNF — Perceus RC included — is NOT persisted
in oleans), read the final `Decl`s from `impureExt`, emit code.

Spike goal: validate the re-run recipe. Dump the final impure LCNF of
the demo functions via `LCNF.ppDecl'`.
-/

open Lean

/-- The functions to compile — the schema's func bodies (demo stage). -/
def targetDecls : Array Name := #[`double, `isBig, `adder, `area]

/-- Run the LCNF pipeline + dump the final impure decls, in CoreM. -/
def dumpLCNF : CoreM Unit := do
  Lean.Compiler.LCNF.main targetDecls {}
  let names ← Lean.Compiler.LCNF.getLocalImpureDecls
  IO.println s!"impure decls in env: {names}"
  for n in names do
    if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
      let fmt ← Lean.Compiler.LCNF.ppDecl' d .impure
      IO.println s!"\n=== {n} ===\n{fmt}"

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Demo, `DemoFn] (opts := {}) (loadExts := true)
  -- Run the dump in CoreM over the imported environment.
  let ctx : Core.Context := { fileName := "<wasm-gen>", fileMap := default }
  let state : Core.State := { env := env }
  let (_ , _) ← dumpLCNF.toIO ctx state
  pure ()

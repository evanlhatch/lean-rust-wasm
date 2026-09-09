import Lean
import Lean.Compiler.LCNF
import WasmBackend

/-!
# WasmBackend.GenMain — the LCNF → WAT artifact writer

The `leanir` pattern: import the target module's oleans, re-run the LCNF
pipeline (the impure-phase LCNF — Perceus RC included — is NOT persisted
in oleans), read the final `Decl`s from `impureExt`, emit WAT.

Pipeline: this exe writes `target/demo.wat`; the justfile drives
`wasm-tools parse -g` → binary, `validate`, and the wasmtime smoke run.
-/

open Lean WasmBackend

/-- The functions to compile — DemoFn (the compiler-line demo stage). -/
def targetDecls : Array Name := #[`double, `isBig, `adder, `area]

/-- Run the LCNF pipeline + emit the module, in CoreM. -/
def emitModuleWasm : CoreM String := do
  Lean.Compiler.LCNF.main targetDecls {}
  let mut decls : List (Lean.Compiler.LCNF.Decl .impure) := []
  for n in targetDecls do
    if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
      decls := d :: decls
  decls := decls.reverse
  let exports := targetDecls.toList.map fun n =>
    s!"  (export \"{n.toString}\" (func ${n.toString}))"
  let res : Except String (String × WasmBackend.S) :=
    StateT.run (WasmBackend.emitModule decls exports) {}
  match res with
  | .ok (wat, _) => pure wat
  | .error e => throwError e

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Demo, `DemoFn] (opts := {}) (loadExts := true)
  let ctx : Core.Context := { fileName := "<wasm-gen>", fileMap := default }
  let state : Core.State := { env := env }
  let (wat, _) ← emitModuleWasm.toIO ctx state
  IO.FS.createDirAll "target"
  IO.FS.writeFile "target/demo.wat" wat
  IO.println "wrote target/demo.wat"

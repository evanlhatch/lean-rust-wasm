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

open Lean Compiler.LCNF WasmBackend

/-- The functions to compile — DemoFn (the compiler-line demo stage). -/
def targetDecls : Array Name := #[`double, `isBig, `adder, `area, `doubleArea, `pick, `applyAll, `runPaps]

-- Collect `.const` names referenced by a code block (one level:
-- finds `_closed` closure constants).
mutual

partial def constRefsOfAlt (alt : Alt .impure) (acc : Array Name) : Array Name :=
  match alt with
  | .ctorAlt _ code => constRefsOf code acc
  | .default code => constRefsOf code acc
  | .alt _ _ _ h => absurd h (by simp)

partial def constRefsOf (code : Code .impure) (acc : Array Name) : Array Name :=
  match code with
  | .let decl k =>
      let acc := match decl.value with
        | .const fn _ args _ => if args.isEmpty then acc.push fn else acc
        | .fap fn args _ => if args.isEmpty then acc.push fn else acc
        | _ => acc
      constRefsOf k acc
  | .cases c => c.alts.foldr constRefsOfAlt acc
  | .sset _ _ _ _ _ k => constRefsOf k acc
  | .inc _ _ _ _ k => constRefsOf k acc
  | .dec _ _ _ _ _ k => constRefsOf k acc
  | .del _ k => constRefsOf k acc
  | .jp _ k => constRefsOf k acc
  | _ => acc

end

/-- Run the LCNF pipeline + emit the module, in CoreM. -/
def emitModuleWasm : CoreM String := do
  Lean.Compiler.LCNF.main targetDecls {}
  -- Closure constants + lambdas: `_closed`/`_lam` decls (holding the
  -- paps) are generated IN-PROCESS by the re-run — never in the imported
  -- env. Include every impure decl UNDER a target's namespace.
  let mut names := targetDecls
  let all ← Lean.Compiler.LCNF.getLocalImpureDecls
  let internal := all.filter fun n =>
    let s := n.toString
    s.contains "." && targetDecls.any fun t => s.startsWith (t.toString ++ ".")
  names := names ++ internal
  let mut decls : List (Lean.Compiler.LCNF.Decl .impure) := []
  for n in names do
    if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
      decls := d :: decls
  decls := decls.reverse
  IO.eprintln s!"NAMES: {names}"
  -- Debug dump: the final LCNF per decl (the compiler line's x-ray).
  for d in decls do
    let fmt ← Lean.Compiler.LCNF.ppDecl' d .impure
    IO.eprintln s!"--- {d.name}\n{fmt}"
  let exports := targetDecls.toList.map fun n =>
    s!"  (export \"{n.toString}\" (func ${n.toString}))"
  let res : Except String (String × WasmBackend.S) :=
    StateT.run (WasmBackend.emitModule decls exports) {}
  match res with
  | .ok (wat, _) =>
    -- splice the hand-written runtime (pooled allocator + Perceus RC)
    -- into the module body: single module, no imports.
    let rt ← IO.FS.readFile "runtime.wat"
    -- strip the runtime's module wrapper comments are fine — the runtime
    -- file is FUNCS+GLOBALS ONLY (no (module) wrapper), splice as-is.
    let opened := wat.replace "(module\n" ("(module\n" ++ rt ++ "\n")
    pure opened
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

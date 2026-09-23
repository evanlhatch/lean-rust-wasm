/-
# EdgePython.EdgeGenMain — the py-artifact writer

The wasm-gen pattern, minus the LCNF re-run: this frontend's source is
the Lean DSL (the `Py` inductives), so there is nothing to re-run —
compile the fixtures and RENDER (`Wat.Module.render`, the doctrine:
never string-interpolated structure). The justfile drives
`wasm-tools parse` → binary → the Rust duel tests.
-/

import EdgePython

open EdgePython

def main : IO Unit := do
  match compiledModule? with
  | none => throw (IO.userError "edgepython: the fixtures FAILED to compile")
  | some _ =>
    IO.FS.createDirAll "artifact"
    let wat := fixturesModule.render
    IO.FS.writeFile "artifact/py.wat" wat
    IO.println s!"edgepython: wrote artifact/py.wat ({wat.length} bytes, \
      {fixtures.length} fns, {compiledFns.foldl (fun n f => n + f.body.length) 0} instrs)"

/-
# Faults.GenMain — the artifact writer (one-writer-per-artifact)

The buf driver: iterates `Faults.Emit.jobs`, runs each emitter's pure
`run` over its spec, prepends the GENERATED header (from the emitter's
`style` + `specSource` — the `CodegenCore.Emit.Core` contract: emitters
never prepend headers, the driver does), and writes. Byte-tie CI:
`forge gen --check` re-runs this in memory and diffs — never edit the
artifact, regenerate.
-/
import Faults.Emit.Registry

open Faults.Emit (jobs)
open CodegenCore.Emit (header)

unsafe def main : IO Unit := do
  for h in jobs do
    let (e, spec) := h
    for f in e.run spec do
      let p := (CodegenCore.Emit.GeneratedFile.path f : String)
      let dir := String.intercalate "/" (p.splitOn "/").dropLast
      IO.FS.createDirAll dir
      IO.FS.writeFile p (header e.style "faults" e.specSource ++ CodegenCore.Emit.GeneratedFile.contents f)
      IO.println s!"wrote {p}"

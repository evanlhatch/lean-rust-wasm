/-
# Faults.FaultsGenMain — the artifact writer (one-writer-per-artifact)

The buf driver: iterates `Faults.Emit.jobs`, runs each emitter's pure
`run` over its spec, prepends the GENERATED header (from the emitter's
`style` + `specSource` — the `CodegenCore.Emit.Core` contract: emitters
never prepend headers, the driver does), and writes. Byte-tie CI:
`forge gen --check` re-runs this in memory and diffs — never edit the
artifact, regenerate.
-/
import Faults.Emit.Registry

open Faults.Emit (jobs)
open CodegenCore.Emit (header runEmitters)

def main : IO Unit :=
  runEmitters "faults" jobs (λ _ f => CodegenCore.Emit.genMeta 1 f.contents.hash)

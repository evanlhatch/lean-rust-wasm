/-
# SchemaLang.GenMain — the artifact writer (the buf driver)

Iterates the emitter registry: for each emitter, run the fold over the
universe, prepend the styled header, write each declared file. The
one-writer discipline: every path is claimed by exactly one emitter
(audited in Tests), and this driver is the only code that writes.
-/
import CodegenCore
import SchemaLang.Emit.Registry
import SchemaLang.Spec.Demo

open SchemaLang.Emit (emitters)
open CodegenCore.Emit (header)

def main : IO Unit := do
  for e in emitters do
    for f in e.run SchemaLang.Spec.demo do
      let p := CodegenCore.Emit.GeneratedFile.path f
      let dir := String.intercalate "/" (((p : String).splitOn "/").dropLast)
      IO.FS.createDirAll dir
      IO.FS.writeFile p (header e.style "schema-lang" e.specSource ++ CodegenCore.Emit.GeneratedFile.contents f)
      IO.println s!"wrote {p}"

/-
# SchemaLang.GenMain — the artifact writer (the buf driver)

Imports the demo module (running `@[schema]` reflection), reads the
registry from the elaborated environment, and runs every emitter over
the reified universe. The one-writer discipline: every path is claimed
by exactly one emitter (audited in Tests), and this driver is the only
code that writes.

The runtime-registry preamble (search path + extension replay) and the
write path (parent dirs + writeFile) are CodegenCore's
(`loadRegisteredItems` / `writeFileCreatingDirs`) — one copy, every
driver.
-/
import Lean
import SchemaLang.Emit.Registry
import Demo

open Lean SchemaLang.Meta

open SchemaLang.Emit (emitters)
open CodegenCore.Emit (header)

unsafe def main : IO Unit := do
  -- Replay the demo module's `@[schema]` registrations from the oleans
  -- (loadExts; `lake exe` supplies LEAN_PATH).
  let items := (← CodegenCore.loadRegisteredItems schemaItemExt #[`Demo]).map (·.2)
  for e in emitters do
    for f in e.run items do
      CodegenCore.Emit.writeFileCreatingDirs f.path
        (header e.style "schema-lang" e.specSource ++ f.contents)
      IO.println s!"wrote {f.path}"

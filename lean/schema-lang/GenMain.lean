/-
# SchemaLang.GenMain — the artifact writer (the buf driver)

Imports the demo module (running `@[schema]` reflection), reads the
registry from the elaborated environment, and runs every emitter over
the reified universe. The one-writer discipline: every path is claimed
by exactly one emitter (audited in Tests), and this driver is the only
code that writes.
-/
import Lean
import SchemaLang.Emit.Registry
import Demo

open Lean SchemaLang.Meta

open SchemaLang.Emit (emitters)
open CodegenCore.Emit (header)

unsafe def main : IO Unit := do
  -- importModules resolves oleans at RUNTIME — initialize the search path
  -- (sysroot + LEAN_PATH, which `lake exe` sets) before importing.
  Lean.initSearchPath (← Lean.findSysroot)
  -- loadExts: replay the imported modules' persistent env extensions —
  -- without it `schemaItemExt` comes back EMPTY (registered: []).
  -- (enableInitializersExecution is unsafe: executes imported inits.)
  Lean.enableInitializersExecution
  -- Import the demo module: this replays its `@[schema]` registrations
  -- from the environment (persistent extensions).
  let env ← Lean.importModules #[`Demo] (opts := {}) (loadExts := true)
  let items := (registeredItems env).map (·.2)

  for e in emitters do
    for f in e.run items do
      let p := CodegenCore.Emit.GeneratedFile.path f
      let dir := String.intercalate "/" (((p : String).splitOn "/").dropLast)
      IO.FS.createDirAll dir
      IO.FS.writeFile p (CodegenCore.Emit.header e.style "schema-lang" e.specSource ++ CodegenCore.Emit.GeneratedFile.contents f)
      IO.println s!"wrote {p}"

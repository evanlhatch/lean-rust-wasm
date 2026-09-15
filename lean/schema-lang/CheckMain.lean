/-
# SchemaLang.CheckMain — `just check-schema` (the buf lint analog)

Fast type-check of the demo universe, no emission: replay the registry
from the oleans (GenMain's preamble), run the diagnostic authority
(`universeCheck`); any diagnostic fails loudly with the rendered
did-you-mean/valid-space text, exit 1. Clean = exit 0.
-/
import Lean
import SchemaLang
import Demo

open Lean SchemaLang SchemaLang.Meta

unsafe def runCheck (_args : List String) : IO UInt32 := do
  let items := (← CodegenCore.loadRegisteredItems schemaItemExt #[`Demo]).map (·.2)
  let diags := universeCheck items
  if diags.isEmpty then
    IO.println s!"check-schema: {items.length} items, diagnostics clean"
    return 0
  else
    IO.eprintln s!"check-schema: FAIL — {diags.length} diagnostic(s):"
    for d in diags do
      IO.eprintln s!"  {SchemaDiag.render d}"
    return 1
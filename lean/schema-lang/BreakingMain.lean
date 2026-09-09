/-
# SchemaLang.BreakingMain — `just breaking` (the buf breaking analog)

Diffs the CURRENT demo registry against the committed baseline
`goldens/universe.snapshot` (`SchemaLang.Snapshot` is the codec).
Breaking findings (`Change.removed` / `Change.changed`, the latter with
field-level evidence) print to stderr and exit 1; additions are safe
and print as info. `--update` rewrites the baseline (the
deliberate-change path — it REFUSES to write names the line format
can't round-trip).

Runs from the package root (the justfile recipe `cd`s there), like the
golden checks in Tests.
-/
import Lean
import SchemaLang
import Demo

open Lean SchemaLang SchemaLang.Meta

unsafe def main (args : List String) : IO UInt32 := do
  let items := (← CodegenCore.loadRegisteredItems schemaItemExt #[`Demo]).map (·.2)
  let path : System.FilePath := "goldens/universe.snapshot"
  if args.contains "--update" then
    if Snapshot.namesEncodable items then
      CodegenCore.Emit.createParentDirs path
      IO.FS.writeFile path (Snapshot.render items)
      IO.println s!"wrote {path} ({items.length} items)"
      return 0
    else
      IO.eprintln "breaking --update: FAIL — a name the snapshot format cannot round-trip:"
      for n in Snapshot.allNames items do
        if !Snapshot.nameOk n then IO.eprintln s!"  `{n}`"
      return 1
  if !(← path.pathExists) then
    IO.eprintln s!"breaking: FAIL — no baseline at {path}; commit one via `lake exe schema-breaking --update`"
    return 1
  match Snapshot.parse (← IO.FS.readFile path) with
  | .error e =>
      IO.eprintln s!"breaking: FAIL — baseline {path} is corrupt: {e}"
      return 1
  | .ok baseline =>
      let changes := diff baseline items
      let breaking := changes.filter fun
        | .added _ => false
        | _ => true
      for c in changes do
        IO.println s!"  {c}"
      if breaking.isEmpty then
        IO.println s!"breaking: clean ({changes.length} safe change(s), {items.length} items)"
        return 0
      else
        IO.eprintln s!"breaking: FAIL — {breaking.length} breaking change(s) vs {path}:"
        for c in breaking do
          IO.eprintln s!"  {c}"
        return 1

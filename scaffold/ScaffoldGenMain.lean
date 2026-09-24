/-
# ScaffoldGenMain — the scaffolder's writer side (the `scaffoldgen` exe)

The byte-tie's writer face (the `schema`/`wasmgen` precedent): the
generator is pure (`Scaffold.generate`), the DRIVER owns IO — this exe
writes the adopted skeletons' files from the spec registry
(`Scaffold.Specs.adoptedSpecs`), never a copy of the spec values.

- `lake exe scaffoldgen <Name>` — write `<Name>`'s generated files.
- `lake exe scaffoldgen all` — every adopted skeleton (the regen
  discipline: rerun after a template change, commit; a drift without
  the regen fails the byte-tie in ScaffoldTests).

The ONE-WRITER rule at the driver: the GENERATED-header files (Reg /
App / Tests) are written every run — the generator is their only
writer. The `<Name>/Flow.lean` seed is written ONLY WHEN ABSENT: it is
the consumer's hand-owned module (no GENERATED header, no byte-tie) —
the driver seeds it once and never clobbers the consumer's content.

Safe main (no env replay — the generator is pure string machinery; the
interpreter stays off).

Five questions (notes/v3/01-core.md):
- root: Crossing — the artifact stage's write face (spec → files).
- carrier grade: the emitter discipline inherited (the content-hash
  header the generator already built).
- spine reading: Registry (the Specs values) → Interpretation
  (Scaffold.generate) → artifact (THIS write loop).
- ladder rung: rung 1 (the discipline lives in the shapes: the
  driver writes only what the generator produced).
- gate row: the byte-tie rows in ScaffoldTests (this exe is the
  writer, the tests are the detection face — the schema/wasmgen
  split).
-/

import Scaffold

open Scaffold

/-- The usage line (the exe's one argument). -/
def usage : String :=
  "usage: lake exe scaffoldgen <Name>|all  — write the adopted \
skeleton's generated files (Flow seeds only when absent)"

/-- Write one spec's files. Returns the exit code fragment (0 = clean). -/
def writeSpec (spec : Scaffold.AppSpec) : IO UInt32 := do
  match Scaffold.generate spec with
  | .error d =>
      IO.eprintln s!"scaffoldgen: REFUSED {spec.name} — {d.code.code}: {d.message}"
      return 1
  | .ok files =>
      for f in files do
        let p : System.FilePath := f.path
        let generated := f.contents.startsWith "-- GENERATED"
        if generated || !(← p.pathExists) then
          Kit.Emit.writeFileCreatingDirs p f.contents
          IO.println s!"wrote {f.path}"
        else
          IO.println s!"kept {f.path} (hand-owned — the driver never overwrites it)"
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
      if name == "all" then
        let mut code := 0
        for spec in adoptedSpecs do
          code := max code (← writeSpec spec)
        return code
      else
        match adoptedSpecs.find? (fun s => s.name == name) with
        | some spec => writeSpec spec
        | none =>
            let names := String.intercalate ", " (adoptedSpecs.map (·.name))
            IO.eprintln s!"scaffoldgen: no adopted spec named `{name}` — adopted: {names}"
            return 1
  | _ =>
      IO.eprintln usage
      return 1

/-
# TestKit.GateKit — the byte-tie gate exe, once

Every byte-tie gate (13 artifacts today, growing — doctrine §5) does the
same three things: read the committed artifact, run a regeneration,
byte-compare (or write under `--update`). GateKit is that loop, once, with
a uniform argv parser so all gate exes accept `--check` / `--update` /
`--help` identically. Core only — deliberately NOT the Cli package, so
core-only packages (lakefile comment) can require TestKit.
-/

import TestKit.Harness

namespace TestKit.GateKit

/-- Uniform gate-exe argv parser. Returns `some update`:
    `["--check"]` (or empty) → `some false`; `["--update"]` → `some true`;
    `["--help"]` prints usage and returns `some false` after the caller
    pattern... no: `--help` and anything malformed return `none` (caller
    prints usage / exits nonzero). -/
def parseGateArgs : List String → Option Bool
  | [] => some false
  | ["--check"] => some false
  | ["--update"] => some true
  | ["--help"] => none
  | _ => none

/-- Usage line for gate exes (print when `parseGateArgs` returns `none`). -/
def gateUsage (exeName : String) : String :=
  s!"usage: {exeName} [--check | --update]\n  --check   byte-compare the committed artifact against regeneration (default)\n  --update  overwrite the committed artifact (deliberate changes only)"

/-- One byte-tie: read the committed artifact at `path`, run `regenerate`,
    byte-compare. Under `update`, write instead. A mismatch prints a
    diff-shaped failure naming the artifact; a missing artifact is an error
    pointing at `--update`. Exit-code semantics: 0 pass/wrote, 1 fail. -/
def byteTie (name : String) (path : System.FilePath) (regenerate : IO String) (update : Bool)
    : IO UInt32 := do
  let emitted ← regenerate
  if update then
    IO.FS.writeFile path emitted
    IO.println s!"✓ {name}: wrote {path} ({emitted.length} bytes)"
    return 0
  else
    try
      let committed ← IO.FS.readFile path
      if committed == emitted then
        IO.println s!"✓ {name}: {path} byte-tied ({emitted.length} bytes)"
        return 0
      else
        IO.eprintln s!"× {name}: committed artifact differs from regeneration ({path})\n--- regenerated ---\n{emitted}\n--- committed ---\n{committed}\n(run with --update to regenerate)"
        return 1
    catch _ =>
      IO.eprintln s!"× {name}: committed artifact missing: {path}; run with --update to generate"
      return 1

end TestKit.GateKit

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

/-- One self-audit rule over EMITTED text: a named substring pattern that
must be absent (banned — the default) or present (required), with the WHY
for the audit report. -/
structure AuditRule where
  name : String
  pattern : String
  required : Bool := false
  why : String := ""

/-- Pure audit: the violation descriptions for `emitted` (empty = clean).
The recipe (guide 6.5.3): emitters audit their OWN generated text —
GuestGate bans constructs in guest SOURCE; this audits the EMITTED
artifact, so a generator regression that starts emitting a banned
construct fails CI even though the generator itself compiles. Purity lets
check-style test suites assert on `auditFindings … |>.isEmpty` while the
IO wrapper below drives gate-exe exit codes. -/
def auditFindings (rules : List AuditRule) (emitted : String) : List String :=
  rules.filterMap fun r =>
    if r.required then
      if emitted.contains r.pattern then none
      else some s!"required \"{r.pattern}\" absent — {r.why}"
    else
      if emitted.contains r.pattern then
        some s!"banned \"{r.pattern}\" present — {r.why}"
      else none

/-- IO audit gate: print findings for `emitted`; exit 0 clean, 1 violated.
Chain after `byteTie` in a gate exe (auditing the REGENERATED text — the
byte-tie already proved committed == regenerated). -/
def audit (what : String) (rules : List AuditRule) (emitted : String) : IO UInt32 := do
  match auditFindings rules emitted with
  | [] =>
    IO.println s!"✓ {what}: self-audit clean ({rules.length} rules)"
    return 0
  | vs =>
    for v in vs do
      IO.eprintln s!"× {what}: self-audit violation: {v}"
    return 1

end TestKit.GateKit

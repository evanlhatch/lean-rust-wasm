/-
# TestKit.GateKit — the gate-exe helpers, once

A uniform argv parser so gate exes can accept `--check` / `--update` /
`--help` identically, plus the emitted-text self-audit (AuditRule /
auditFindings / audit). The generic `byteTie` loop was deleted (2026-12
quality pass): zero consumers outside TestKit's own tests — every real
gate exe compares inlined against its own artifact shape. Core only —
deliberately NOT the Cli package, so core-only packages (lakefile
comment) can require TestKit.
-/

module

public import TestKit.Harness

@[expose] public section

namespace TestKit.GateKit

/-- Uniform gate-exe argv parser. Returns `some update`:
    `[]`/`["--check"]` → `some false` (check is the default);
    `["--update"]` → `some true`; `--help` and anything malformed →
    `none` (caller prints usage / exits nonzero). -/
def parseGateArgs : List String → Option Bool
  | [] => some false
  | ["--check"] => some false
  | ["--update"] => some true
  | ["--help"] => none
  | _ => none

/-- Usage line for gate exes (print when `parseGateArgs` returns `none`). -/
def gateUsage (exeName : String) : String :=
  s!"usage: {exeName} [--check | --update]\n  --check   byte-compare the committed artifact against regeneration (default)\n  --update  overwrite the committed artifact (deliberate changes only)"

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
Chain after the byte-tie check in a gate exe (auditing the REGENERATED
text — the gate's byte-tie already proved committed == regenerated). -/
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

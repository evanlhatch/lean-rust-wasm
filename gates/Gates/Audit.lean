/-
Gates.Audit — the artifact self-audit (`gates audit`; mined from
legacy/lean/gates/Gates/Audit.lean's audit slot + legacy
TestingKit.GateKit's AuditRule, ported fresh — the fresh tree's TestingKit
carries no GateKit).

09-gates-ops.md §5: every emitted artifact scans against the AuditRule
list — no TODO/FIXME/unwrap/dbg!/unsafe in generated output. The scan
surface is the EMITTERS' declared outputs (read from `SchemaCore.regen`
— the same one-regen-semantics surface gen-check byte-ties; never a
hand-copied artifact list), checked over the COMMITTED bytes: a
generator regression that starts emitting a banned construct fails the
gate even though the generator itself compiles.

The observability-inheritance row (§5's second half: generated host
code without span coverage fails) is NOTED, not built — this tree has
no host-code generator yet (the Rust emitter emits codecs, not host
spans); the row lands with its first consumer (the leftover rule).

Failures: a banned pattern present, an artifact absent (a path the
emitter declares whose committed file vanished), or a load failure.
No baseline file — the audit is a COMPUTED gate (the expected findings
set is empty; there is nothing to re-baseline).

The five questions (notes/v3/01-core.md):
- root: none — the audit over the artifact surface.
- carrier grade: none — substring rules over committed bytes.
- spine reading: the artifact stage's audit face (the committed bytes
  of the ONE regen's declared outputs).
- ladder rung: n/a.
- gate row: the audit row itself (`gates audit`).
-/
import Lean
import Gates.Packages
import Gates.Common
import SchemaCore

open Lean

namespace Gates.Audit

/-- One self-audit rule over EMITTED text (the TestingKit.GateKit shape,
    ported fresh): a named substring pattern that must be absent
    (banned — the default) or present (required), with the WHY for the
    audit report. -/
structure AuditRule where
  name : String
  pattern : String
  required : Bool := false
  why : String := ""

/-- The rule list (09 §5). `unwrap(` / `dbg!` / `unsafe` are Rust-facing
    bans; TODO/FIXME are the universal ladder; all BANNED. The
    generated Rust's `unwrap_or`/`unwrap_or_else` do not match
    `unwrap(` (the paren is the bare-unwrap discriminator). -/
def auditRules : List AuditRule :=
  [ { name := "todo", pattern := "TODO"
      why := "generated output is committed spec-of-record — a TODO in it \
        is an unresolved decision smuggled past review" }
  , { name := "fixme", pattern := "FIXME"
      why := "generated output is committed spec-of-record — a FIXME in it \
        is an unresolved decision smuggled past review" }
  , { name := "unwrap", pattern := "unwrap("
      why := "generated Rust never bare-unwraps — refusals are typed \
        (notes/v3/12-construction.md §8)" }
  , { name := "dbg", pattern := "dbg!"
      why := "generated Rust carries no debug-print debris" }
  , { name := "unsafe", pattern := "unsafe"
      why := "generated Rust stays in the safe subset" }
  ]

/-- Pure audit: the violation descriptions for `emitted` (empty =
    clean). Required rules demand the pattern PRESENT; banned rules
    demand it ABSENT. -/
def auditFindings (rules : List AuditRule) (emitted : String) : List String :=
  rules.filterMap fun r =>
    if r.required then
      if emitted.contains r.pattern then none
      else some s!"required \"{r.pattern}\" absent — {r.why}"
    else if emitted.contains r.pattern then
      some s!"banned \"{r.pattern}\" present — {r.why}"
    else none

/-- `gates audit` — scan every committed generated artifact (the
    emitters' declared outputs) against the rule list. Exit 1 on any
    violation or absent artifact. -/
unsafe def run : IO UInt32 := do
  let pkg : PkgSpec := { dir := "SchemaCore", srcDir := "schemacore", roots := #[`SchemaCore.Slice] }
  Gates.withPkgEnv "audit" pkg fun env => do
    match SchemaCore.regen env with
    | .error e =>
      IO.eprintln s!"audit: REGEN FAILED — {e}"
      return 1
    | .ok r => do
      let mut failed := false
      let mut scanned := 0
      for f in r.files do
        let path : System.FilePath := f.path
        unless ← path.pathExists do
          IO.eprintln s!"audit: {f.path} ABSENT — a declared artifact has no committed file"
          failed := true
          continue
        scanned := scanned + 1
        let committed ← IO.FS.readFile path
        for v in auditFindings auditRules committed do
          IO.eprintln s!"audit: {f.path}: {v}"
          failed := true
      -- the observability-inheritance row: NOTED, not built — no
      -- host-code generator exists yet (the row lands with its first
      -- consumer; 09 §5 + the leftover rule).
      if failed then
        IO.eprintln "audit: VIOLATIONS — fix the generator (never hand-edit \
          the artifact), `just gen`, commit"
        return 1
      IO.println s!"audit: clean — {scanned} artifact(s) scanned, \
        {auditRules.length} rule(s), no violations"
      IO.println "audit: observability-inheritance row — NOTED, not built \
        (no host-code generator exists yet; the span-coverage row lands \
        with its first consumer)"
      return 0

end Gates.Audit

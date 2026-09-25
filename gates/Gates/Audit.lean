/-
Gates.Audit — the artifact self-audit (`gates audit`; mined from
legacy/lean/gates/Gates/Audit.lean's audit slot + legacy
TestingKit.GateKit's AuditRule, ported fresh — the fresh tree's TestingKit
carries no GateKit).

09-gates-ops.md §5: every emitted artifact scans against the AuditRule
list — no TODO/FIXME/unwrap/dbg!/unsafe in generated output. The scan
surface is the EMITTERS' declared outputs (read from `SchemaCore.regen`
— the same one-regen-semantics surface gen-check byte-ties; never a
hand-copied artifact list; PLUS the faults lane's regen — the fault
surface rides the same discipline), checked over the COMMITTED bytes: a
generator regression that starts emitting a banned construct fails the
gate even though the generator itself compiles.

The observability-inheritance row (§5's second half, wave-30 C1 LANDED:
generated host code without span coverage fails) is the targeted
REQUIRED-rule table `coverageRules` below — per generated host artifact,
the span/fault coverage marker must be PRESENT in the committed bytes
(the global banned list stays universal; these pin the
observability-inheritance rule per artifact).

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
import SchemaCore.Emit.Witness
import Faults

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

/-- The observability-inheritance rows (09 §5, wave-30 C1): generated
    host code's coverage, REQUIRED per artifact — a (path, rule) table
    applied only to the named artifact's committed bytes. The
    span-coverage row: the generated codecs open their dotted-static
    `scope!`s (the observability TargetFace — one per schema operation);
    the fault-coverage row: the generated fault surface is fast-observe's
    `error!` face (the registry's projection — no hand-rolled error
    surface outside it). -/
def coverageRules : List (String × AuditRule) :=
  [ ("crates/schema-generated/src/lib.rs",
     { name := "span-coverage"
       pattern := "fast_observe::scope!"
       required := true
       why := "generated host code without span coverage fails the audit " ++
         "(09 §5; the observability TargetFace — one dotted-static " ++
         "scope! per schema operation)" })
  , ("crates/mandate-faults/src/lib.rs",
     { name := "fault-coverage"
       pattern := "fast_observe::error!"
       required := true
       why := "generated error paths ride the registry's projection — " ++
         "the error! face, never a hand-rolled error surface (09 §5)" }) ]

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
    match ← Kit.Lane.runCoreIO env (SchemaCore.regen env) with
    | .error e =>
      IO.eprintln s!"audit: REGEN FAILED — {e}"
      return 1
    | .ok r => do
      -- the shared artifact walk (Gates.forDeclared): the regen lane +
      -- the WITNESS LANE's artifacts (SchemaCore.Emit.Witness.regen —
      -- the same ONE copy gen-check byte-ties; the registry table + the
      -- duel manifest, text) — the same banned-pattern discipline.
      let scan : List Kit.Emit.GeneratedFile → IO (Nat × Bool) :=
        fun files => do
          let (_, present, failed) ← Gates.forDeclared "audit"
            "a declared artifact has no committed file" files fun f committed => do
            -- the universal banned list + the targeted coverage rules
            -- (the observability-inheritance rows: only the named
            -- artifact's bytes answer its required marker)
            let vs := auditFindings auditRules committed
              ++ (coverageRules.flatMap fun (path, rule) =>
                    if f.path == path then auditFindings [rule] committed else [])
            for v in vs do
              IO.eprintln s!"audit: {f.path}: {v}"
            return vs.isEmpty
          return (present, failed)
      let (s1, f1) ← scan r.files
      let (s2, f2) ← scan SchemaCore.Emit.Witness.regen.1
      -- THE FAULTS LANE's artifacts (the same ONE regen the faultsgen
      -- writer + gen-check run): the fault surface rides the audit too
      -- (the fault-coverage row's scan surface).
      let (s3, f3) ←
        match ← Faults.regen with
        | .error e => do
          IO.eprintln s!"audit: FAULTS REGEN FAILED — {e}"
          pure (0, true)
        | .ok modes => scan (Faults.faultsEmitter.run modes)
      let scanned := s1 + s2 + s3
      let failed := f1 || f2 || f3
      if failed then
        IO.eprintln "audit: VIOLATIONS — fix the generator (never hand-edit \
          the artifact), `just gen`, commit"
        return 1
      IO.println s!"audit: clean — {scanned} artifact(s) scanned, \
        {auditRules.length} banned rule(s) + {coverageRules.length} \
        coverage rule(s), no violations"
      IO.println s!"audit: observability-inheritance rows LANDED (wave-30 \
        C1): {coverageRules.map (fun p => p.2.name)} — generated host code \
        without span coverage fails"
      return 0

end Gates.Audit

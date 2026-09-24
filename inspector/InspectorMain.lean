/-
InspectorMain — the `inspector` exe: the evidence-chain inspector

    lake exe inspector why <label>     — one obligation's evidence chain
    lake exe inspector report          — the full obligation sweep
    lake exe inspector ledger          — the provenance ledger's queries
    lake exe inspector ledger backward <artifact-path>
    lake exe inspector ledger forward <spec-name>
    lake exe inspector cites <theorem> — who cites this theorem
    lake exe inspector uncited         — the zero-citation report
    lake exe inspector trust           — the tree's trust surface
    lake exe inspector whatif          — the what-if report over the
                                         fixture journal (08 #20)
    lake exe inspector                 — the sweep (the report mode)

Exit codes: `why` exits 1 only on an unknown label (the loud miss);
`ledger backward` exits 1 on an untracked path; `ledger` exits 1 on
orphan flags or a parse refusal (the review failure's ledger-side face)
but 0 in the honest ABSENT state (dormant, not green); `cites` exits 1
only on an unknown constant; `uncited`/`trust` are report-only (exit 0)
— the census's gate promotion is lintkit's question, the teeth are the
gates' rows. `whatif` is report-only (exit 0): the divergence is the
ANSWER, not a failure — a what-if over the committed fixture always
succeeds, and a net-zero what-if renders its honest `none` line. `report` is the gates' future sweep — the teeth are 09 §3's
(a registered obligation with no discharge, or evidence resolving to
nothing, fails the run), so gaps/defects exit 1.

Handlers are `unsafe` (the replay imports module environments at
runtime — the gates' pattern).

The five questions (notes/v3/01-core.md): none — the argv dispatch
shell over Inspector's surfaces. Gate row: none — the exe is how the
rows render, not a row.
-/

import Inspector
import Lean

open Inspector
open Lean

/-- Run one CoreM computation over a loaded env (the gates' toIO
    pattern — Gates.Axioms's, mirrored at the call site). -/
unsafe def runCore (env : Lean.Environment) (act : Lean.CoreM α) : IO α := do
  let ctx : Lean.Core.Context := { fileName := "<inspector>", fileMap := default }
  let (res, _) ← act.toIO ctx { env := env }
  return res

/-- The ledger row: load the committed file, render the state report.
    ABSENT = the honest dormant state (exit 0); a refusal or orphan
    flags fail the run (exit 1). -/
unsafe def runLedger : IO UInt32 := do
  let onDisk ← Inspector.LedgerView.scanGenerated
  let st ← Inspector.LedgerView.readLedger
  let (text, failed) := Inspector.LedgerView.report onDisk st
  IO.println text
  return if failed then 1 else 0

/-- One backward query: the artifact's demand surface; an untracked
    path is the loud miss (exit 1). -/
unsafe def runLedgerBackward (path : String) : IO UInt32 := do
  let st ← Inspector.LedgerView.readLedger
  match st with
  | .absent =>
      IO.println "inspector: the ledger is ABSENT — no row can answer a \
        backward query yet (it lands with the first driver wiring)"
      return 1
  | .refused e =>
      IO.eprintln s!"inspector: the ledger REFUSED to parse — {e}"
      return 1
  | .loaded rows =>
      let (text, known) := Inspector.LedgerView.backwardAnswer rows path
      IO.println text
      return if known then 0 else 1

/-- One forward query: what moves if this spec name changes. Always
    answers (an empty affected set is a legitimate answer; the query is
    conservative by Kit.Ledger's proved face). -/
unsafe def runLedgerForward (name : String) : IO UInt32 := do
  let st ← Inspector.LedgerView.readLedger
  match st with
  | .absent =>
      IO.println "inspector: the ledger is ABSENT — no row can answer a \
        forward query yet (it lands with the first driver wiring)"
      return 1
  | .refused e =>
      IO.eprintln s!"inspector: the ledger REFUSED to parse — {e}"
      return 1
  | .loaded rows =>
      IO.println (Inspector.LedgerView.forwardAnswer rows name)
      return 0

/-- The proof-coverage row over the replayed envs: who cites the
    theorem. An unknown constant is the loud miss (exit 1). -/
unsafe def runCites (envs : List (Inspector.PkgSpec × Lean.Environment))
    (thm : Name) : IO UInt32 := do
  for (_, env) in envs do
    let data ← runCore env (Inspector.Cites.assemble env)
    let (text, known) := Inspector.Cites.citesAnswer data thm
    IO.println text
    if known then return 0
  IO.eprintln s!"inspector: NO constant `{thm}` in any replayed environment"
  return 1

/-- The zero-citation report over the replayed envs (the census's
    project-roots discipline; report-only — exit 0). -/
unsafe def runUncited (envs : List (Inspector.PkgSpec × Lean.Environment)) :
    IO UInt32 := do
  for (pkg, env) in envs do
    let data ← runCore env (Inspector.Cites.assemble env)
    let cands ← runCore env (Inspector.Cites.theoremCandsFiltered env)
    let unc := Inspector.Cites.zeroCites data cands.toList
    IO.println s!"— {pkg.dir} —"
    IO.println (Inspector.Cites.uncitedReportFull unc cands.size)
  return 0

/-- The trust report over the replayed envs: the axiom cones (the
    replayed roots' decls, LintKit's machinery consumed) + the tiers'
    distribution + the duel status. Report-only (exit 0). -/
unsafe def runTrust (envs : List (Inspector.PkgSpec × Lean.Environment)) :
    IO UInt32 := do
  match ← collectReplayed with
  | .error e =>
      IO.eprintln s!"inspector: LOAD FAILED — {e}"
      return 1
  | .ok rows =>
      for (pkg, env) in envs do
        let axs ← runCore env (Inspector.Trust.axiomCones env pkg.roots)
        let total := env.header.moduleNames.size
        let proj := (env.header.moduleNames.toList.filter (fun m =>
          !(LintKit.coreModuleRoots.any (·.isPrefixOf m)))).length
        IO.println (Inspector.Trust.trustReport pkg.dir proj total axs rows)
      return 0

/-- The what-if report over the committed fixture journal (08 #20):
    the divergence is the answer, not a failure — report-only, exit 0. -/
def runWhatIf : IO UInt32 := do
  IO.println (Inspector.WhatIf.Report.render Inspector.WhatIf.fixtureWhatIf)
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["ledger"] => runLedger
  | ["ledger", "backward", path] => runLedgerBackward path
  | ["ledger", "forward", name] => runLedgerForward name
  | ["cites", thm] =>
      match ← replayEnvs with
      | .error e =>
          IO.eprintln s!"inspector: LOAD FAILED — {e}"
          return 1
      | .ok envs => runCites envs thm.toName
  | ["uncited"] =>
      match ← replayEnvs with
      | .error e =>
          IO.eprintln s!"inspector: LOAD FAILED — {e}"
          return 1
      | .ok envs => runUncited envs
  | ["trust"] =>
      match ← replayEnvs with
      | .error e =>
          IO.eprintln s!"inspector: LOAD FAILED — {e}"
          return 1
      | .ok envs => runTrust envs
  | ["whatif"] => runWhatIf
  | ["why", label] =>
      match ← collectReplayed with
      | .error e =>
          IO.eprintln s!"inspector: LOAD FAILED — {e}"
          return 1
      | .ok rows =>
          IO.println (Inspector.why rows label)
          return if Inspector.whyKnown rows label then 0 else 1
  | ["report"] | [] =>
      match ← collectReplayed with
      | .error e =>
          IO.eprintln s!"inspector: LOAD FAILED — {e}"
          return 1
      | .ok rows =>
          IO.println (Inspector.report replayPkgsRender rows)
          -- The sweep's teeth (09 §3): gaps + defects fail the run.
          return if rows.any (fun r => !r.isClean) then 1 else 0
  | _ =>
      IO.eprintln "usage: lake exe inspector [why <label> | report | ledger \
        [backward <path> | forward <name>] | cites <theorem> | uncited | \
        trust | whatif]"
      return 1

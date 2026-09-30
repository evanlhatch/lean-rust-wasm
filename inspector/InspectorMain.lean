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
    lake exe inspector explain         — the explanations lane (02 §11:
                                         why present / why absent /
                                         which change repairs)
    lake exe inspector duel [<name>]   — the committed duel vectors' REPLAY
                                         (the regression discipline) + the
                                         divergences' EXPLAIN (the witness +
                                         the ledger rows). No name = every
                                         registered duel; a name/directory is
                                         the closed world (did-you-mean).
    lake exe inspector                 — the sweep (the report mode)

Exit codes: `why` exits 1 only on an unknown label (the loud miss);
`ledger backward` exits 1 on an untracked path; `ledger` exits 1 on
orphan flags or a parse refusal (the review failure's ledger-side face)
but 0 in the honest ABSENT state (dormant, not green); `cites` exits 1
only on an unknown constant; `uncited`/`trust` are report-only (exit 0)
— the census's gate promotion is lintkit's question, the teeth are the
gates' rows. `whatif` is report-only (exit 0): the divergence is the
ANSWER, not a failure — a what-if over the committed fixture always
succeeds, and a net-zero what-if renders its honest `none` line.
`duel` is the REPLAY — a regression surface, so it has teeth: a
divergence, a malformed manifest, or an unknown duel name exits 1
(the legacy oracle-runner's probe contract); a clean replay exits 0
and renders the ledger's zero line. `report` is the gates' future sweep — the teeth are 09 §3's
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

/-- The replayed-envs dispatch (the exe's LOAD-FAILED face, ONE copy —
the six hand-rolled dispatches collapsed): on replay failure the loud
line + exit 1; on success the envs. -/
unsafe def withReplayed (k : List (Inspector.PkgSpec × Lean.Environment) → IO UInt32) :
    IO UInt32 := do
  match ← replayEnvs with
  | .error e =>
      IO.eprintln s!"inspector: LOAD FAILED — {e}"
      return 1
  | .ok envs => k envs

/-- The same face over the obligation rows (`collectReplayed`) — the
row-level handlers' dispatch. -/
unsafe def withReplayRows (k : List Inspector.InspRow → IO UInt32) : IO UInt32 := do
  match ← collectReplayed with
  | .error e =>
      IO.eprintln s!"inspector: LOAD FAILED — {e}"
      return 1
  | .ok rows => k rows

/-- The loaded-ledger dispatch (the two query directions' shared
preamble): ABSENT renders the direction's honest dormant line (exit 1
— the loud miss), a parse refusal is the review failure (exit 1);
loaded rows hand to `k`. -/
unsafe def withLedgerRows (absentWhy : String)
    (k : List Kit.Ledger.LedgerRow → IO UInt32) : IO UInt32 := do
  match ← Inspector.LedgerView.readLedger with
  | .absent =>
      IO.println absentWhy
      return 1
  | .refused e =>
      IO.eprintln s!"inspector: the ledger REFUSED to parse — {e}"
      return 1
  | .loaded rows => k rows

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
  let onDisk ← Inspector.ArtifactScan.scanGenerated
  let st ← Inspector.LedgerView.readLedger
  let (text, failed) := Inspector.LedgerView.report onDisk st
  IO.println text
  return if failed then 1 else 0

/-- One backward query: the artifact's demand surface; an untracked
    path is the loud miss (exit 1). -/
unsafe def runLedgerBackward (path : String) : IO UInt32 :=
  withLedgerRows
    "inspector: the ledger is ABSENT — no row can answer a backward \
      query yet (it lands with the first driver wiring)"
    fun rows => do
      let (text, known) := Inspector.LedgerView.backwardAnswer rows path
      IO.println text
      return if known then 0 else 1

/-- One forward query: what moves if this spec name changes. Always
    answers (an empty affected set is a legitimate answer; the query is
    conservative by Kit.Ledger's proved face). -/
unsafe def runLedgerForward (name : String) : IO UInt32 :=
  withLedgerRows
    "inspector: the ledger is ABSENT — no row can answer a forward \
      query yet (it lands with the first driver wiring)"
    fun rows => do
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
    IO UInt32 :=
  withReplayRows fun rows => do
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

/-- The explain report (02 §11: the explanations lane — why present /
    why absent / which change repairs; the explanations ARE the
    answer) — report-only, exit 0 (the `whatif` precedent). -/
def runExplain : IO UInt32 := do
  IO.println Inspector.Explain.explainReport
  return 0

/-- The duel REPLAY (the regression discipline): replay one duel or
    every registered duel, render each report (the Diag discipline —
    divergences render their envelope + the ready-to-paste ledger
    row). TEETH: a divergence, a manifest refusal, or an unknown duel
    name exits 1 (the legacy oracle-runner's probe contract — a
    replay is a regression, never a report-only surface). -/
def runDuel (name : Option String) : IO UInt32 := do
  let entries? : Option (List Inspector.DuelReplay.DuelEntry) := match name with
    | none => some Inspector.DuelReplay.duelEntries
    | some n =>
        match Inspector.DuelReplay.duelEntries.find? fun e => e.name == n || e.dir == n with
        | some e => some [e]
        | none => none
  match entries? with
  | none =>
      let got := name.getD ""
      IO.eprintln (Kit.Diag.toString (Inspector.DuelReplay.unknownDuelDiag got))
      return 1
  | some entries =>
      let mut failed := false
      for e in entries do
        match ← Inspector.DuelReplay.replayDuel e with
        | .error msg =>
            IO.eprintln (Kit.Diag.toString (Inspector.DuelReplay.manifestRefusalDiag e.dir msg))
            failed := true
        | .ok rows =>
            IO.println (Inspector.DuelReplay.report e.name rows)
            if !(rows.all (fun r => Inspector.DuelReplay.isAgree r.2)) then failed := true
      return if failed then 1 else 0

/-- The sweep (the `report` row AND the no-arg default — the old
`["report"] | []` dispatch, byte-identical). -/
unsafe def runReport : IO UInt32 :=
  withReplayRows fun rows => do
    IO.println (Inspector.report replayPkgsRender rows)
    -- The sweep's teeth (09 §3): gaps + defects fail the run.
    return if rows.any (fun r => !r.isClean) then 1 else 0

/-- A row's extra-token refusal: the row's own spelling is the closed
world (an unexpected argument is the curated miss, not a shrug). -/
def extraArgs (row : String) (args : List String) : IO UInt32 := do
  IO.eprintln (Kit.Diag.toString (Kit.Diag.closedWorld Kit.Cli.eCX0001
    "unexpected argument for this subcommand" .error (args.headD "") [row]))
  return Kit.Cli.Verdict.finding.exit

/-- The no-arg report rows: the row's body, else the curated extra-token
refusal (the old exact-match dispatch's exit-1 face, curated). -/
unsafe def rowNoArgs (row : String) (body : IO UInt32) : List String → IO UInt32
  | [] => body
  | args => extraArgs row args

/-- The `ledger backward` row. -/
unsafe def runLedgerBackwardRow : List String → IO UInt32
  | [path] => runLedgerBackward path
  | args => extraArgs "ledger backward" args

/-- The `ledger forward` row. -/
unsafe def runLedgerForwardRow : List String → IO UInt32
  | [name] => runLedgerForward name
  | args => extraArgs "ledger forward" args

/-- The `duel` row: no name = every registered duel. -/
unsafe def runDuelRow : List String → IO UInt32
  | [] => runDuel none
  | [name] => runDuel (some name)
  | args => extraArgs "duel [<name>]" args

/-- The `uncited` row. -/
unsafe def runUncitedRow : List String → IO UInt32 :=
  rowNoArgs "uncited" (withReplayed runUncited)

/-- The `trust` row. -/
unsafe def runTrustRow : List String → IO UInt32 :=
  rowNoArgs "trust" (withReplayed runTrust)

/-- The `whatif` row. -/
unsafe def runWhatIfRow : List String → IO UInt32 :=
  rowNoArgs "whatif" runWhatIf

/-- The `explain` row. -/
unsafe def runExplainRow : List String → IO UInt32 :=
  rowNoArgs "explain" runExplain

/-- The `report` row. -/
unsafe def runReportRow : List String → IO UInt32 :=
  rowNoArgs "report" runReport

/-- The `ledger` row: no args = the state report; an unknown query word
is the curated miss (the two directions are the closed world). -/
unsafe def runLedgerRow : List String → IO UInt32
  | [] => runLedger
  | args => do
      IO.eprintln (Kit.Diag.toString (Kit.Diag.closedWorld Kit.Cli.eCX0001
        "unknown ledger query" .error (args.headD "")
        ["backward <artifact-path>", "forward <spec-name>"]))
      return Kit.Cli.Verdict.finding.exit

/-- The `cites` row: one theorem name. -/
unsafe def runCitesRow : List String → IO UInt32
  | [thm] => withReplayed fun envs => runCites envs thm.toName
  | args => extraArgs "cites <theorem>" args

/-- The `why` row: one obligation label (an unknown label exits 1). -/
unsafe def runWhyRow : List String → IO UInt32
  | [label] => withReplayRows fun rows => do
      IO.println (Inspector.why rows label)
      return if Inspector.whyKnown rows label then 0 else 1
  | args => extraArgs "why <label>" args

/-! ## THE TABLE (Kit.Cli's one driver; the help is generated from it) -/

/-- The inspector's about line (the sweep is the no-arg default). -/
def inspectorAbout : String :=
  "The evidence-chain inspector — the obligation/ledger/cites/trust/duel \
    surfaces over the replayed environments; the no-arg default is the \
    sweep (`report`)."

unsafe def inspectorSubs : List Kit.Cli.Sub :=
  [ { name := "ledger backward"
      summary := "one artifact's demand surface: `ledger backward <artifact-path>`; \
an untracked path exits 1 (the loud miss)."
      run := runLedgerBackwardRow }
  , { name := "ledger forward"
      summary := "what moves if this spec name changes: `ledger forward <spec-name>` — \
always answers (an empty affected set is a legitimate answer)."
      run := runLedgerForwardRow }
  , { name := "ledger"
      summary := "the provenance ledger's state report (`ledger [backward <path> | \
forward <name>]`); ABSENT is the honest dormant face, orphan flags exit 1."
      run := runLedgerRow }
  , { name := "cites"
      summary := "who cites this theorem: `cites <theorem>` — an unknown constant \
exits 1 (the loud miss)."
      run := runCitesRow }
  , { name := "why"
      summary := "one obligation's evidence chain: `why <label>` — an unknown label \
exits 1 (the loud miss)."
      run := runWhyRow }
  , { name := "duel"
      summary := "the committed duel vectors' REPLAY (the regression discipline): \
`duel [<name>]` — no name = every registered duel; a divergence, a manifest \
refusal, or an unknown duel name exits 1."
      run := runDuelRow }
  , { name := "uncited"
      summary := "the zero-citation report over the replayed envs (report-only)."
      run := runUncitedRow }
  , { name := "trust"
      summary := "the tree's trust surface: the axiom cones + the tiers' distribution \
+ the duel status (report-only)."
      run := runTrustRow }
  , { name := "whatif"
      summary := "the what-if report over the committed fixture journal (08 #20) — \
report-only, exit 0 (the divergence is the answer)."
      run := runWhatIfRow }
  , { name := "explain"
      summary := "the explanations lane (02 §11): why present / why absent / which \
change repairs — report-only, exit 0."
      run := runExplainRow }
  , { name := "report"
      summary := "the full obligation sweep — the gates' future sweep, so it has teeth: \
gaps/defects exit 1 (09 §3)."
      run := runReportRow } ]

unsafe def main (args : List String) : IO UInt32 :=
  Kit.Cli.run "inspector" inspectorAbout inspectorSubs (some runReport) args

/-
# InspectorTests.Axioms — the axiom self-check

#print axioms over the inspector's pure rendering faces, pinned by
#guard_msgs — the expected output is the CORE TRIPLE ONLY (or the
zero-axiom line where the fold is pure definitional). If a `sorry` or a
NEW axiom ever sneaks into the rendering, the printed set changes and
this file FAILS THE BUILD — the drift is loud, not silent.

The replay face (Inspector.Replay) is host-side `unsafe` IO — its trust
story is the gates' loadPkgEnv discipline it mirrors; the axioms here
cover the DATA + RENDERING surfaces.
Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import Inspector.Obligations
import Inspector.Why
import Inspector.LedgerView
import Inspector.Cites
import Inspector.Trust
import Inspector.WhatIf
import Inspector.Explain
import Inspector.DuelReplay
import Inspector.Tables

/-- info: 'Inspector.Tables.selectRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.Tables.selectRows

/-- info: 'Inspector.Tables.projectRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.Tables.projectRows

/-- info: 'Inspector.InspRow.defects' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.InspRow.defects

/-- info: 'Inspector.InspRow.renderWhy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.InspRow.renderWhy

/-- info: 'Inspector.why' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.why

/-- info: 'Inspector.report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.report

/-- info: 'Inspector.trustStrength' does not depend on any axioms -/
#guard_msgs in
#print axioms Inspector.trustStrength

/-- info: 'Inspector.evidenceKindLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.evidenceKindLine

/-! ## the new rows' pure faces (the ledger reading + the proof coverage +
the trust report) — all inside the core triple -/

/-- info: 'Inspector.LedgerView.report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.LedgerView.report

/-- info: 'Inspector.LedgerView.backwardAnswer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.LedgerView.backwardAnswer

/-- info: 'Inspector.LedgerView.forwardAnswer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.LedgerView.forwardAnswer

/-- info: 'Inspector.LedgerView.orphans' does not depend on any axioms -/
#guard_msgs in
#print axioms Inspector.LedgerView.orphans

/-- info: 'Inspector.Cites.citesAnswer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.Cites.citesAnswer

/-- info: 'Inspector.Cites.zeroCites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.Cites.zeroCites

/-- info: 'Inspector.Trust.axiomSummary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.Trust.axiomSummary

/-- info: 'Inspector.Trust.tierDistribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.Trust.tierDistribution

/-- info: 'Inspector.Trust.trustReport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.Trust.trustReport

/-- info: 'Inspector.Trust.classifyAxiom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.Trust.classifyAxiom

/-! ## the what-if inspector's pure faces (08 #20) — all inside the
   core triple (the walk's faithfulness theorems included: zero
   `sorry`, zero new axiom) -/

/-- info: 'Inspector.WhatIf.renderTable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.WhatIf.renderTable

/-- info: 'Inspector.WhatIf.renderDelta' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.WhatIf.renderDelta

/-- info: 'Inspector.WhatIf.rewindEvents' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.WhatIf.rewindEvents

/-- info: 'Inspector.WhatIf.whatIfJournal' does not depend on any axioms -/
#guard_msgs in
#print axioms Inspector.WhatIf.whatIfJournal

/-- info: 'Inspector.WhatIf.firstDivergenceAux' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.WhatIf.firstDivergenceAux

/-- info: 'Inspector.WhatIf.firstDivergence?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.WhatIf.firstDivergence?

/-- info: 'Inspector.WhatIf.whatIfReport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.WhatIf.whatIfReport

/-- info: 'Inspector.WhatIf.Report.render' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.WhatIf.Report.render

/-- info: 'Inspector.WhatIf.firstDivergenceAux_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.WhatIf.firstDivergenceAux_none

/-- info: 'Inspector.WhatIf.firstDivergenceAux_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.WhatIf.firstDivergenceAux_some

/-- info: 'Inspector.WhatIf.whatIfJournal_seqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.WhatIf.whatIfJournal_seqs

/-! ## the explain command's pure faces (02 §11) — all inside the
   core triple -/

/-- info: 'Inspector.Explain.explainReport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.Explain.explainReport

/-- info: 'Inspector.Explain.renderRepair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.Explain.renderRepair

/-- info: 'Inspector.Explain.renderRepairDelta' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.Explain.renderRepairDelta

/-- info: 'Inspector.Explain.xPresent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.Explain.xPresent

/-! ## the duel replay's pure faces (the replay + the explain
   discipline) — all inside the core triple; the engines' axiom
   surfaces are the LANES' (WasmCore.Duel's computed expectations, the
   codec's GADT walks, the checker's verdicts), re-run as data -/

/-- info: 'Inspector.DuelReplay.rowVerdict' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.rowVerdict

/-- info: 'Inspector.DuelReplay.parseExpect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.parseExpect

/-- info: 'Inspector.DuelReplay.parseManifest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.parseManifest

/-- info: 'Inspector.DuelReplay.report' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.report

/-- info: 'Inspector.DuelReplay.ledgerRow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.ledgerRow

/-- info: 'Inspector.DuelReplay.divergenceDiag' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.divergenceDiag

/-- info: 'Inspector.DuelReplay.wasmEngine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.wasmEngine

/-- info: 'Inspector.DuelReplay.codecEngine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.codecEngine

/-- info: 'Inspector.DuelReplay.journalEngine' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.journalEngine

/-- info: 'Inspector.DuelReplay.commitEngine' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Inspector.DuelReplay.commitEngine

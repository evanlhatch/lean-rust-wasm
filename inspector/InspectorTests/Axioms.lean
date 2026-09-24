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

/-- info: 'Inspector.Trust.tierDistribution' depends on axioms: [propext] -/
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

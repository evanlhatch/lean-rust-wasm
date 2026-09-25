/-
# GatesTests.Axioms — the axiom self-check

#print axioms over the impact core's pure faces, pinned by #guard_msgs —
the expected output is the CORE TRIPLE ONLY (or the zero-axiom line
where the fold is pure definitional). If a `sorry` or a NEW axiom ever
sneaks into the impact analysis, the printed set changes and this file
FAILS THE BUILD — the drift is loud, not silent.

The IO driver (Gates.Impact.run and the scan faces) is host-side IO —
its trust story is the change set's own honesty (the VCS diff, the
manual argument); the axioms here cover the ANALYSIS surfaces.
Evidence, not architecture — the five-question block lives in the
module under test.
-/

import Gates.Impact

/-- info: 'Gates.Impact.analyze' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Gates.Impact.analyze

/-- info: 'Gates.Impact.closureIdxs_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gates.Impact.closureIdxs_covers

/-- info: 'Gates.Impact.closureIdxs_importer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gates.Impact.closureIdxs_importer

/-- info: 'Gates.Impact.affectedArtifacts_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gates.Impact.affectedArtifacts_covers

/-- info: 'Gates.Impact.affectedArtifacts_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gates.Impact.affectedArtifacts_growth

/-- info: 'Gates.Impact.revGraphOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gates.Impact.revGraphOf

/-- info: 'Gates.Impact.Verdict.render' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Gates.Impact.Verdict.render

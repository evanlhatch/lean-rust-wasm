/-
# AnalysisTests.Axioms — the axiom self-check

#print axioms over the analysis laws, pinned by #guard_msgs — the
expected outputs name the CORE TRIPLE AT MOST (propext,
Classical.choice, Quot.sound). If a `sorry` or a NEW axiom ever sneaks
into a law, the printed set changes and this file FAILS THE BUILD —
the drift is loud, not silent.
-/

import Analysis

open Analysis

/-- info: 'Analysis.abstract_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Analysis.abstract_sound

/-- info: 'Analysis.addT_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Analysis.addT_sound

/-- info: 'Analysis.negT_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Analysis.negT_sound

/-- info: 'Analysis.join_cover_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Analysis.join_cover_left

/-- info: 'Analysis.width_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Analysis.width_lt

/-- info: 'Analysis.caged_result_certified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Analysis.caged_result_certified

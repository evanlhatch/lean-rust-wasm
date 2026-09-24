/-
# ZSetTests.Axioms — the axiom self-check

#print axioms over the ZSet substrate's law theorems, pinned by
#guard_msgs — the expected output is the CORE TRIPLE ONLY (here:
[propext, Quot.sound] — funext costs Quot.sound, propext rides simp's
rewriting; both are founding axioms of Lean's logic, inside the
allowlist, never a trust extension). If a `sorry` or a NEW axiom ever
sneaks into a law, the printed set changes and this file FAILS THE
BUILD — the drift is loud, not silent.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import ZSet

/-- info: 'ZSet.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.ext

/-- info: 'ZSet.add_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.add_comm

/-- info: 'ZSet.add_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.add_assoc

/-- info: 'ZSet.add_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.add_neg

/-- info: 'ZSet.neg_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.neg_add

/-- info: 'ZSet.add_self_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.add_self_eq_zero

/-- info: 'ZSet.eq_of_beq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.eq_of_beq

/-- info: 'ZSet.weightOfW_relabel_canonW' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZSet.weightOfW_relabel_canonW

/-- info: 'ZSet.projectW_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.projectW_add

/-- info: 'ZSet.joinW_add_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.joinW_add_left

/-- info: 'ZSet.Event.occId_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms ZSet.Event.occId_ne

/-! ## 5-7: the abstract layer (ZSet.Relation) — the new surface -/

/- The generic layer's laws: the core-triple surface only. If a `sorry`
    or a NEW axiom ever sneaks into THE ONE THEOREM or the operator
    laws, the printed set changes and this file FAILS THE BUILD. -/

/-- info: 'ZSet.extW' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZSet.extW

/-- info: 'ZSet.addW_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.addW_ok

/-- info: 'ZSet.joinW_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.joinW_ok

/-- info: 'ZSet.projectW_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.projectW_ok

/-- info: 'ZSet.filterW_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.filterW_ok

/-- info: 'ZSet.distinctW_add_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.distinctW_add_ok

/-- info: 'ZSet.thresholdW_add_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.thresholdW_add_ok

/-- info: 'ZSet.evaluate_wmap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.evaluate_wmap

/-- info: 'ZSet.evaluate_supportCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.evaluate_supportCollapse

/-- info: 'ZSet.weightW_ofZSet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.weightW_ofZSet

/-! ## 8: the graph-reading layer (ZSet.Graph) — the new surface -/

/-- info: 'ZSet.Edge.succs_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.Edge.succs_mem

/-- info: 'ZSet.succs_of_Edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.succs_of_Edge

/-- info: 'ZSet.Reach.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms ZSet.Reach.trans

/-- info: 'ZSet.Reach.cycle_of_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZSet.Reach.cycle_of_closed

/-- info: 'ZSet.cycle?_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.cycle?_sound

/-- info: 'ZSet.reachFrom_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZSet.reachFrom_sound

/-- info: 'ZSet.Stratified.acyclic' does not depend on any axioms -/
#guard_msgs in
#print axioms ZSet.Stratified.acyclic

/- The graduation (16-surface §5.1): the rep ≅ weight-function iso. -/
/-- info: 'ZSet.weightFnIso' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms ZSet.weightFnIso

/-
# QueryTests.Axioms — the axiom self-check

#print axioms over the query lane's theorems, pinned by #guard_msgs —
the expected outputs name the CORE TRIPLE AT MOST (propext,
Classical.choice, Quot.sound — the Classical.choice rides the Keys
lane's `uniqueOn_determines` plumbing). If a `sorry` or a NEW axiom
ever sneaks into a theorem, the printed set changes and this file
FAILS THE BUILD — the drift is loud, not silent.
-/

import Query

open Query

/-- info: 'Query.Row.bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.Row.bytes_eq

/-- info: 'Query.evalQ_wmap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.evalQ_wmap

/-- info: 'Query.QSat.weight_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.QSat.weight_true

/-- info: 'Query.evalQ_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.evalQ_true_iff

/-- info: 'Query.keyJoinRows_atMostOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.keyJoinRows_atMostOne

/-! ## the explanations lane's faces (02 §11) — all inside the core triple -/

/-- info: 'Query.Derivation.qsat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Query.Derivation.qsat

/-- info: 'Query.QSat.derivation_nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Query.QSat.derivation_nonempty

/-- info: 'Query.blocker_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.blocker_absent

/-- info: 'Query.WhyAbsent.verdict_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.WhyAbsent.verdict_sound

/-- info: 'Query.KeyJoinMiss.not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Query.KeyJoinMiss.not_mem

/-- info: 'Query.repairVerdict_clean_iff_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.repairVerdict_clean_iff_valid

/-- info: 'Query.applyRepair_credit_targeted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.applyRepair_credit_targeted

/-- info: 'Query.applyRepair_danglingSrc_targeted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.applyRepair_danglingSrc_targeted

/-! ## the TypedBridge's faces — all inside the core triple -/

/-- info: 'Query.toTypedRow_round' does not depend on any axioms -/
#guard_msgs in
#print axioms Query.toTypedRow_round

/-- info: 'Query.typedRowToVals_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Query.typedRowToVals_exact

/-- info: 'Query.predToExpr_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Query.predToExpr_ok

/-- info: 'Query.qEval_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Query.qEval_sound

/-- info: 'Query.qEval_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Query.qEval_complete

/-- info: 'Query.qEval_agree_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Query.qEval_agree_iff

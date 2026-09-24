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

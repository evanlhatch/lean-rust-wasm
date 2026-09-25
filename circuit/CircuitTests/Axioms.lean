/-
# CircuitTests.Axioms — the axiom self-check

#print axioms over the circuit lane's theorems, pinned by #guard_msgs —
the expected outputs name the CORE TRIPLE AT MOST (propext,
Quot.sound, Classical.choice — the axiom gate's accepted set; the
Classical.choice legs are inherited from the landed ZSet substrate's
law theorems, e.g. `ZSet.distinctW_add_ok`, not introduced here). If a
`sorry` or a NEW axiom ever sneaks into a theorem, the printed set
changes and this file FAILS THE BUILD — the drift is loud, not silent.

Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import Circuit

/-- info: 'Circuit.Ckt.incrementalize_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.Ckt.incrementalize_ok

/-- info: 'Circuit.compile_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.compile_ok

/-- info: 'Circuit.Ckt.recursive_opt_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.Ckt.recursive_opt_ok

/-- info: 'Circuit.optOnce_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.optOnce_ok

/-- info: 'Circuit.opStep_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.opStep_law

/-- info: 'Circuit.distinctStep_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.distinctStep_ok

/-- info: 'Circuit.thresholdStep_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.thresholdStep_ok

/-- info: 'Circuit.opStep_linear_oldFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Circuit.opStep_linear_oldFree

/-
# DatalogTests.Axioms — the axiom self-check

#print axioms over the datalog laws, pinned by #guard_msgs — the
expected outputs name the CORE TRIPLE AT MOST (propext,
Classical.choice, Quot.sound). If a `sorry` or a NEW axiom ever sneaks
into a law, the printed set changes and this file FAILS THE BUILD —
the drift is loud, not silent.
-/

import Datalog

open Datalog

/-- info: 'Datalog.step_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Datalog.step_mono

/-- info: 'Datalog.Conseq.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms Datalog.Conseq.mono

/-- info: 'Datalog.step_iff_conseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Datalog.step_iff_conseq

/-- info: 'Datalog.exists_fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Datalog.exists_fix

/-- info: 'Datalog.eval_fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Datalog.eval_fix

/-- info: 'Datalog.lfp_least' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Datalog.lfp_least

/-- info: 'Datalog.deriv_iff_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Datalog.deriv_iff_eval

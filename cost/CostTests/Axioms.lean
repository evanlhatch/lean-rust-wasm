/-
# CostTests.Axioms — the axiom self-check

#print axioms over the cost laws, pinned by #guard_msgs — the expected
outputs name the CORE TRIPLE AT MOST (propext, Quot.sound;
Classical.choice never appears). If a `sorry` or a NEW axiom ever
sneaks into a law, the printed set changes and this file FAILS THE
BUILD — the drift is loud, not silent.

Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import Cost

/-- info: 'Cost.Grading.agrees' does not depend on any axioms -/
#guard_msgs in
#print axioms Cost.Grading.agrees

/-- info: 'Cost.Grading.cost_honest' does not depend on any axioms -/
#guard_msgs in
#print axioms Cost.Grading.cost_honest

/-- info: 'Cost.Graded.pure_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms Cost.Graded.pure_bind

/-- info: 'Cost.Graded.bind_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms Cost.Graded.bind_pure

/-- info: 'Cost.Graded.bind_assoc' does not depend on any axioms -/
#guard_msgs in
#print axioms Cost.Graded.bind_assoc

/-- info: 'Cost.spend_covered' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cost.spend_covered

/-- info: 'Cost.spend_exhausted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cost.spend_exhausted

/-- info: 'Cost.spend_seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cost.spend_seq

/-- info: 'Cost.covered_remaining_monus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cost.covered_remaining_monus

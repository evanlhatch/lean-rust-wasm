/-
# ContractsTests.Axioms — the axiom self-check

#print axioms over the wp engine's theorems + the contract surface's
laws + the loop discipline, pinned by #guard_msgs — the expected
outputs name the CORE TRIPLE AT MOST (propext, Quot.sound;
Classical.choice never appears — the fragment's soundness is one
structural induction, the while's is one fuel induction, the surface's
laws route through them + cited cites). If a `sorry` or a NEW axiom
ever sneaks into a law, the printed set changes and this file FAILS
THE BUILD — the drift is loud, not silent.

Evidence, not architecture — the five-question blocks live in the
modules under test.
-/

import Contracts

open Contracts

/-- info: 'Contracts.wp_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.wp_sound

/-- info: 'Contracts.wp_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Contracts.wp_iff

/-- info: 'Contracts.wp_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.wp_mono

/-- info: 'Contracts.wp_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.wp_cons

/-- info: 'Contracts.wp_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.wp_bind

/-- info: 'Contracts.wp_seq' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.wp_seq

/-- info: 'Contracts.wp_cond' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.wp_cond

/-- info: 'Contracts.Prog.exec_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.Prog.exec_bind

/-- info: 'Contracts.While.run_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Contracts.While.run_true

/-- info: 'Contracts.While.run_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Contracts.While.run_false

/-- info: 'Contracts.while_sound_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.while_sound_fuel

/-- info: 'Contracts.while_sat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.while_sat

/-- info: 'Contracts.Contract.sat_of_vc' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.Contract.sat_of_vc

/-- info: 'Contracts.Contract.sat_of_inconsistent' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.Contract.sat_of_inconsistent

/-- info: 'Contracts.Contract.pointDischarge_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Contracts.Contract.pointDischarge_sound

/-- info: 'Contracts.Feasibility.checked' does not depend on any axioms -/
#guard_msgs in
#print axioms Contracts.Feasibility.checked

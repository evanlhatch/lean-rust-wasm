/-
# ReprTests.Axioms — the axiom self-check

#print axioms over the Repr lane's law theorems, pinned by #guard_msgs —
the expected output is the CORE-TRIPLE-ONLY surface ([propext,
Quot.sound] — funext costs Quot.sound, propext rides simp's rewriting;
both are founding axioms of Lean's logic, inside the allowlist, never a
trust extension). If a `sorry` or a NEW axiom ever sneaks into a law,
the printed set changes and this file FAILS THE BUILD — the drift is
loud, not silent.
Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import Repr

/-! ## The discipline's laws (Repr.Basic) -/

/-- info: 'Repr.run_pres' does not depend on any axioms -/
#guard_msgs in
#print axioms Repr.run_pres

/-- info: 'Repr.client_obs' does not depend on any axioms -/
#guard_msgs in
#print axioms Repr.client_obs

/-- info: 'Repr.client_obs_from' does not depend on any axioms -/
#guard_msgs in
#print axioms Repr.client_obs_from

/-- info: 'Repr.crossRep_obs' does not depend on any axioms -/
#guard_msgs in
#print axioms Repr.crossRep_obs

/-- info: 'Repr.no_ignore_step' does not depend on any axioms -/
#guard_msgs in
#print axioms Repr.no_ignore_step

/-! ## The worked example's laws (Repr.FinMap) -/

/-- info: 'Repr.lookupS_insort' does not depend on any axioms -/
#guard_msgs in
#print axioms Repr.lookupS_insort

/-- info: 'Repr.lookupS_deleteS' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Repr.lookupS_deleteS

/-- info: 'Repr.lookupR_insertR' does not depend on any axioms -/
#guard_msgs in
#print axioms Repr.lookupR_insertR

/-- info: 'Repr.lookupR_deleteR' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Repr.lookupR_deleteR

/-- info: 'Repr.canonicity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Repr.canonicity

/-- info: 'Repr.toAbsS_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Repr.toAbsS_inj

/-- info: 'Repr.raw_not_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Repr.raw_not_injective

/-- info: 'Repr.client_cross' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Repr.client_cross

/-- info: 'Repr.insert_effect_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Repr.insert_effect_ne

/-- info: 'Repr.sorted_ignore_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Repr.sorted_ignore_step

/-- info: 'Repr.raw_ignore_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Repr.raw_ignore_step

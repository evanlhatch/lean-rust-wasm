/-
# VortexTests.Axioms — the axiom self-check

#print axioms over the selection's laws + the emitter row's discharge,
pinned by #guard_msgs — the expected outputs name the CORE TRIPLE AT
MOST (propext, Classical.choice, Quot.sound). If a `sorry` or a NEW
axiom ever sneaks into a law, the printed set changes and this file
FAILS THE BUILD — the drift is loud, not silent.
-/

import Vortex

open Vortex

/-- info: 'Vortex.select_applicable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.select_applicable

/-- info: 'Vortex.layoutOf_applicable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.layoutOf_applicable

/-- info: 'Vortex.keyFacts_dict' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.keyFacts_dict

/-- info: 'Vortex.forRead_forEncode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.forRead_forEncode

/-- info: 'Vortex.constRead_constEncode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.constRead_constEncode

/-- info: 'Vortex.layoutLaw_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.layoutLaw_discharged

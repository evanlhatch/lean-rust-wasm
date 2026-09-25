/-
# FaultsTests.Axioms — the axiom self-check

#print axioms over the lane's checked facts, pinned by #guard_msgs — the
expected output is the CORE TRIPLE at most (`propext`, `Classical.choice`,
`Quot.sound` — the allowlist the axiom gate enforces; the cones here come
from the Kit/TextKit machinery the allocation routes through, never from
proof debt). If a `sorry` or a NEW axiom ever sneaks into the lane, the
printed set changes and this file FAILS THE BUILD — the drift is loud, not
silent.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import Faults

/-- info: 'Faults.allocOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faults.allocOne

/-- info: 'Faults.allocAllCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faults.allocAllCheck

/-- info: 'Faults.ecodeSpelling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faults.ecodeSpelling

/-- info: 'Faults.renderLib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faults.renderLib

/-- info: 'Faults.regen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Faults.regen

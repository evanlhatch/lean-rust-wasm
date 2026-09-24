/-
# WasmCoreTests.Axioms — the axiom self-check

#print axioms over the seed's laws, pinned by #guard_msgs — the
expected output is the CORE TRIPLE ONLY (propext, Classical.choice,
Quot.sound — every set below is a subset; no `sorry`, no new axiom).
If a `sorry` or a NEW axiom ever sneaks into a law, the printed set
changes and this file FAILS THE BUILD — the drift is loud, not silent.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import WasmCore.Encode
import WasmCore.Validate
import WasmCore.Wat
import WasmCore.Exec

-- The varint law pins (`WasmCore.ulebCodec`/`WasmCore.ulebDec_append`)
-- moved to `KitTests.Axioms` with the laws themselves: the varint atom
-- now lives in `Kit.Varint` (the C0 shared home).

/-- info: 'WasmCore.checkBody_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.checkBody_sound

/-- info: 'WasmCore.checkBody_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.checkBody_complete

/-- info: 'WasmCore.checkFunc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.checkFunc_sound

/-- info: 'WasmCore.funcChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.funcChecked

/-- info: 'WasmCore.checkModule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.checkModule

/-- info: 'WasmCore.encodeModule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WasmCore.encodeModule

-- The WAT lane's pins: the renderer + the emitter row stay inside
-- the core triple (the total fold is a plain data computation).
/-- info: 'WasmCore.renderModule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.renderModule

/-- info: 'WasmCore.watEmitter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.watEmitter

-- The executor's laws: the machine + the theorems stay inside the core
-- triple (the executor is a plain def; the theorems are hand proofs
-- over it + the validator's bridge).
/-- info: 'WasmCore.step_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.step_preserves

/- The frame machine's preservation (the body-level induction) + the
    module-level driver face: the deliverable theorems stay inside the
    core triple — no `sorry`, no new axiom. -/

/-- info: 'WasmCore.exec_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.exec_typed

/-- info: 'WasmCore.runFunc_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.runFunc_safe

/-- info: 'WasmCore.checkFuncs_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.checkFuncs_some

/-- info: 'WasmCore.step_store_inBounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.step_store_inBounds

/-- info: 'WasmCore.step_store_oob_traps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WasmCore.step_store_oob_traps

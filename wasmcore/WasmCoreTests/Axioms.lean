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

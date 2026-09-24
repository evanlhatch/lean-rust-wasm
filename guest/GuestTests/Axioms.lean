/-
# GuestTests.Axioms — the axiom self-check over the pure faces

#print axioms over the lowering's pure faces, pinned by #guard_msgs —
the expected output is the CORE TRIPLE ONLY (propext,
Classical.choice, Quot.sound). If a `sorry` or a NEW axiom ever
sneaks into a face, the printed set changes and this file FAILS THE
BUILD — the drift is loud, not silent.

The host IO faces (`Guest.Lcnf.readDecl?`, the test driver) are the
driver's IO discipline, not pure code — they are NOT pinned here
(the same boundary every package's Axioms.lean draws).
-/

import Guest
import WasmCore

-- The lowering's pure face: the decl → module crossing (single + multi).
/-- info: 'Guest.lowerFunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.lowerFunc

/-- info: 'Guest.lowerFuncs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.lowerFuncs

-- The refusal envelope's rendering.
/-- info: 'Guest.LowerError.toDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.LowerError.toDiag

-- The scalar type map.
/-- info: 'Guest.wasmTyOf?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.wasmTyOf?

-- The op surface.
/-- info: 'Guest.binop?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.binop?

-- The bounded-Nat cap constant.
/-- info: 'Guest.natCap' does not depend on any axioms -/
#guard_msgs in
#print axioms Guest.natCap

-- The size measures (the well-founded substrate).
/-- info: 'Guest.codeSize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.codeSize

-- The join-point discipline's detector.
/-- info: 'Guest.jumpsTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.jumpsTo

-- The tag prescan.
/-- info: 'Guest.collectScalarEnums' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.collectScalarEnums

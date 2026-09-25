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
-- THE SPLIT'S DIVIDEND: the IR's String keys shaved the Lean-name
-- hashing's Classical.choice off the lowering's axiom set.
/-- info: 'Guest.lowerFunc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.lowerFunc

/-- info: 'Guest.lowerFuncs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.lowerFuncs

-- The frontend's pure face: the LCNF → IR reading (the composed
-- pipeline rides it). The Lean-name hashing carries the Classical
-- choice here (the frontend's face, not the lowering's).
/-- info: 'Guest.toIR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.toIR

/-- info: 'Guest.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.compile

-- The refusal envelope's rendering.
/-- info: 'Guest.LowerError.toDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.LowerError.toDiag

-- The scalar type map (the frontend's row resolution).
/-- info: 'Guest.irTyOf?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.irTyOf?

-- The op surface (the frontend's name dispatch).
/-- info: 'Guest.binopOf?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.binopOf?

-- The bounded-Nat cap constant.
/-- info: 'Guest.natCap' does not depend on any axioms -/
#guard_msgs in
#print axioms Guest.natCap

-- The size measures (the well-founded substrate over the LCNF tree
-- — the frontend's; the IR's spine is structural).
/-- info: 'Guest.codeSize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.codeSize

-- The join-point discipline's detector (over the IR's spine —
-- structural, so no axioms at all).
/-- info: 'Guest.jumpsTo' does not depend on any axioms -/
#guard_msgs in
#print axioms Guest.jumpsTo

-- The tag prescan.
/-- info: 'Guest.collectScalarEnums' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.collectScalarEnums

-- The effects lane's integration (Guest.Effects): the derivation +
-- the boundary check + the obligation rows.
/-- info: 'Guest.Effects.rowOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.Effects.rowOf

/-- info: 'Guest.Effects.fpOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.Effects.fpOf

/-- info: 'Guest.Effects.verdictOf' does not depend on any axioms -/
#guard_msgs in
#print axioms Guest.Effects.verdictOf

/-- info: 'Guest.Effects.enforce' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.Effects.enforce

/-- info: 'Guest.Effects.obligationRows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.Effects.obligationRows

/-- info: 'Guest.Effects.rowDiff_nil_iff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.Effects.rowDiff_nil_iff_le

/-- info: 'Guest.Effects.verdict_over_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.Effects.verdict_over_refuses

/-- info: 'Guest.Effects.verdict_not_le_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.Effects.verdict_not_le_refuses

/-- info: 'Guest.Effects.verdict_le_of_not_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.Effects.verdict_le_of_not_refused

/-- info: 'Guest.Effects.EffectError.toDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.Effects.EffectError.toDiag

-- The SECOND FRONTEND's pure faces (the edgepython lane — the parse
-- face rides TextKit's own gates; these are the fold + the pipeline).
/-- info: 'Guest.EdgePython.Fe.lowerProgram' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Guest.EdgePython.Fe.lowerProgram

/-- info: 'Guest.EdgePython.Fe.compileModule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.EdgePython.Fe.compileModule

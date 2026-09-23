/-
# SchemaTests.Axioms — the axiom self-check

#print axioms over the slice's checked facts, pinned by #guard_msgs —
the expected output is the CORE TRIPLE at most (`propext`,
`Classical.choice`, `Quot.sound` — Lean's founding logical axioms, the
same allowlist LintKit enforces; the `Classical.choice` cones here come
from the string/registry machinery the Kit theorems route through, not
from any proof debt). If a `sorry` or a NEW axiom ever sneaks into the
slice, the printed set changes and this file FAILS THE BUILD — the
drift is loud, not silent.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import SchemaCore
import SchemaCore.Pred
import SchemaCore.Check

open SchemaCore

/-- info: 'SchemaCore.registryOfItems' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.registryOfItems

/-- info: 'SchemaCore.dischargeFieldNodup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.dischargeFieldNodup

/-- info: 'SchemaCore.fieldNodupObligation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.fieldNodupObligation

/-- info: 'SchemaCore.tyOfExpr?' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.tyOfExpr?

/-- info: 'SchemaCore.reflectStruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.reflectStruct

/-- info: 'SchemaCore.regen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.regen

/-- info: 'SchemaCore.renderWit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.renderWit

/-- info: 'SchemaCore.kebabName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.kebabName

/-- info: 'SchemaCore.Value.eval' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.Value.eval

/-- info: 'SchemaCore.Value.beq_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.Value.beq_refl

/-- info: 'SchemaCore.RowVals.project?' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.RowVals.project?

/-- info: 'SchemaCore.fieldIndexIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.fieldIndexIso

/-- info: 'SchemaCore.Ty.toType' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.Ty.toType

/-- info: 'SchemaCore.renderKeyTy_toTy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.renderKeyTy_toTy

/-- info: 'SchemaCore.KeyTy.toType_toTy' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.KeyTy.toType_toTy

/-- info: 'SchemaCore.tyOfDescr' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.tyOfDescr

/-- info: 'SchemaCore.tyOfDescr_denotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.tyOfDescr_denotes

/-- info: 'SchemaCore.deriveRender' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.deriveRender

/-- info: 'SchemaCore.deriveRender_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.deriveRender_coherent

/-- info: 'SchemaCore.itemOfDescr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.itemOfDescr

/-- info: 'SchemaCore.describe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.describe

/-- info: 'SchemaCore.reflectItemViaDescr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.reflectItemViaDescr

/-- info: 'SchemaCore.Ty.witLossless' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.Ty.witLossless

/-- info: 'SchemaCore.renderTy_set_list_collision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.renderTy_set_list_collision

/-- info: 'SchemaCore.renderTy_bounded_u64_collision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.renderTy_bounded_u64_collision

/-- info: 'SchemaCore.witSurfaceDistinct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.witSurfaceDistinct

/-- info: 'SchemaCore.keyOfExpr?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.keyOfExpr?

/-- info: 'SchemaCore.natLitOf?' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.natLitOf?

/-- info: 'SchemaCore.Pred.check_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.Pred.check_iff

/-- info: 'SchemaCore.Pred.checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.Pred.checked

/-- info: 'SchemaCore.CheckItem.checkRows_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.CheckItem.checkRows_iff

/-- info: 'SchemaCore.CheckItem.scopedDiags_eq_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.CheckItem.scopedDiags_eq_nil_iff

/-- info: 'SchemaCore.CheckItem.dischargeOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.CheckItem.dischargeOn

/-- info: 'SchemaCore.CheckItem.checkOn_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.CheckItem.checkOn_self

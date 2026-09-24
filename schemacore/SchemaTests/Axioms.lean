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
import SchemaCore.Keys

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

/-! ## The derivation layer (SchemaCore.Derive + DeriveMeta — the order's
     axiom pins: the GENERIC theorems must be axiom-free or core-triple
     only — a new axiom in the derivation layer fails the build here) -/

/-- info: 'SchemaCore.deriveCodec_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.deriveCodec_correct

/-- info: 'SchemaCore.deriveDec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.deriveDec_eq

/-- info: 'SchemaCore.deriveCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.deriveCodec

/-- info: 'SchemaCore.rowBridgeIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.rowBridgeIso

/-- info: 'SchemaCore.eval_mkValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.eval_mkValue

/-- info: 'SchemaCore.mkValue_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.mkValue_eval

/-- info: 'SchemaCore.ofRowF_toRowF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.ofRowF_toRowF

/-- info: 'SchemaCore.toRowF_ofRowF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.toRowF_ofRowF

/-- info: 'SchemaCore.decNat?_encNat_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.decNat?_encNat_append

/-- info: 'SchemaCore.WireCodec' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.WireCodec

/-- info: 'SchemaCore.row_bridge' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.row_bridge

/-! ## The keys lane (SchemaCore.Keys — the determinacy theorems' cone:
     core-triple at most; the structural beq's lawfulness is the
     unconditional replacement for the legacy CodecClosed conditioning) -/

/-- info: 'SchemaCore.FieldVal.beq' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.FieldVal.beq

/-- info: 'SchemaCore.Value.beq_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.Value.beq_eq

/-- info: 'SchemaCore.FieldVal.beq_eq_true_iff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.FieldVal.beq_eq_true_iff_eq

/-- info: 'SchemaCore.KeyDecl.uniqueOn_determines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.KeyDecl.uniqueOn_determines

/-- info: 'SchemaCore.KeyDecl.lookup?_atMostOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.KeyDecl.lookup?_atMostOne

/-- info: 'SchemaCore.KeyDecl.check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.KeyDecl.check

/-- info: 'SchemaCore.keyDeclsCheck_eq_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.keyDeclsCheck_eq_nil_iff

/-- info: 'SchemaCore.keysChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.keysChecked

/-- info: 'SchemaCore.KeyDecl.dischargeUniqueOn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.KeyDecl.dischargeUniqueOn

/-- info: 'SchemaCore.KeyDecl.defaultObligations' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.KeyDecl.defaultObligations

/-! ## The event-sourcing lane (SchemaCore.Delta + Event — the rungs,
     the fusion, the codec, the gate: core-triple at most) -/

/-- info: 'SchemaCore.witnessedReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.witnessedReversible

/-- info: 'SchemaCore.journal_notReversible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.journal_notReversible

/-- info: 'SchemaCore.apply_eq_patchW' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.apply_eq_patchW

/-- info: 'SchemaCore.witnessOf_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.witnessOf_valid

/-- info: 'SchemaCore.replay_of_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.replay_of_run

/-- info: 'SchemaCore.journal_differentiates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.journal_differentiates

/-- info: 'SchemaCore.decJournal?_encJournal_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.decJournal?_encJournal_append

/-- info: 'SchemaCore.replayMigrated?_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.replayMigrated?_ok

/-! ## The semantic-profiles lane (SchemaCore.Profile — the phantom's
     erasure cone: core-triple at most; the codec-legality citations
     ride the value codec's own cone) -/

/-- info: 'SchemaCore.Profiled.iso' does not depend on any axioms -/
#guard_msgs in
#print axioms SchemaCore.Profiled.iso

/-- info: 'SchemaCore.Fixed.add?_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.Fixed.add?_some

/-- info: 'SchemaCore.Fixed.mul?_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SchemaCore.Fixed.mul?_some

/-- info: 'SchemaCore.Fixed.val_codecLegal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SchemaCore.Fixed.val_codecLegal

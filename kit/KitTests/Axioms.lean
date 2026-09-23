/-
# KitTests.Axioms — the axiom self-check

#print axioms over the kit's law theorems, pinned by #guard_msgs — the
expected output is the CORE TRIPLE ONLY (here: `[propext]`, or the
zero-axiom line where the proof is pure definitional + decide routing —
`propext` is one of the three founding axioms of Lean's logic, never a
trust extension). If a `sorry` or a NEW axiom ever sneaks into a law,
the printed set changes and this file FAILS THE BUILD — the drift is
loud, not silent.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import Kit.Obligation
import Kit.CheckedProp
import Kit.Registry
import Kit.FreshName
import Kit.Change
import Kit.Observer
import Kit.CodeRegistry
import Kit.Varint

/-- info: 'Kit.Obligation.decideEvidence_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.Obligation.decideEvidence_sound

/-- info: 'Kit.Obligation.decideEvidence_of_claim' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Obligation.decideEvidence_of_claim

/-- info: 'Kit.Obligation.decideDischarge_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.Obligation.decideDischarge_sound

/-- info: 'Kit.Obligation.decideDischarge_of_claim' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Obligation.decideDischarge_of_claim

/-- info: 'Kit.CheckedProp.check_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.CheckedProp.check_iff

/-- info: 'Kit.DataRegistry.nameOf_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.DataRegistry.nameOf_injective

/-- info: 'Kit.CodedRegistry.idxOf_getElem_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.CodedRegistry.idxOf_getElem_inj

/-- info: 'Kit.freshNameVerdict_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.freshNameVerdict_none_iff

/-- info: 'Kit.CodeRegistry.sortedCodes_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.CodeRegistry.sortedCodes_iff

/-- info: 'Kit.codeRegistryWf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.codeRegistryWf

/-- info: 'Kit.CodeRegistry.maxCode_ge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.CodeRegistry.maxCode_ge

/-- info: 'Kit.CodeRegistry.nextCode_gt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.CodeRegistry.nextCode_gt

/-- info: 'Kit.Additive.invRoundTrip' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Additive.invRoundTrip

/-- info: 'Kit.Additive.bindComm' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Additive.bindComm

/-- info: 'Kit.Reversible.apply_invNop' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Reversible.apply_invNop

/-- info: 'Kit.monus_notReversible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.monus_notReversible

/-- info: 'Kit.fieldSet_notComposable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.fieldSet_notComposable

/-- info: 'Kit.fieldSet_notReversible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.fieldSet_notReversible

/-- info: 'Kit.Observer.equiv_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Observer.equiv_trans

/-- info: 'Kit.Observer.Below.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Observer.Below.trans

/-- info: 'Kit.Observer.refines_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Observer.refines_trans

/-- info: 'Kit.Varint.varintCodec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Varint.varintCodec

/-- info: 'Kit.Varint.decVarNat?_encVarNat_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Varint.decVarNat?_encVarNat_append

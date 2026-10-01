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

-- the wave's grind migrations (Codecs: readBytes?/unpackStream_packStream)
-- import Classical.choice through the consumed byte laws — the honest
-- drift (06 §12's choice-axiom note); the integrator re-baselines.
/-- info: 'Vortex.decBitPacked?_encBitPacked_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decBitPacked?_encBitPacked_append

/-- info: 'Vortex.decFoR?_encFoR_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decFoR?_encFoR_append

/-- info: 'Vortex.decDict?_encDict_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decDict?_encDict_append

/-- info: 'Vortex.dictDecode_dictEncode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.dictDecode_dictEncode

/-- info: 'Vortex.dictRetention' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.dictRetention

/-- info: 'Vortex.decConst?_encConst_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decConst?_encConst_append

/-- info: 'Vortex.decSeq?_encSeq_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decSeq?_encSeq_append

/-- info: 'Vortex.decIdentity?_encIdentity_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decIdentity?_encIdentity_append

/-- info: 'Vortex.decodeColumn_encodeColumn_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decodeColumn_encodeColumn_append

/-- info: 'Vortex.select_ne_sparse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.select_ne_sparse

/-- info: 'Vortex.sparseJoin_mask_patches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.sparseJoin_mask_patches

/-- info: 'Vortex.sparseMask_dom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.sparseMask_dom

/-- info: 'Vortex.inDomain_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.inDomain_nil

/-- info: 'Vortex.readColumnData_emitColumnData_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.readColumnData_emitColumnData_append

/-- info: 'Vortex.decDTypeBody?_encDTypeBody_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decDTypeBody?_encDTypeBody_append

/-- info: 'Vortex.decDType?_encDType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.decDType?_encDType

/- E3's laws — the affine kernel's retention discipline, the hazard
   law note's refusals, and the dtype policy rows — the core triple
   at most, like every law above. -/

/-- info: 'Vortex.evalArith_law' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.evalArith_law

/-- info: 'Vortex.hazard_refused_not_rounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.hazard_refused_not_rounded

/-- info: 'Vortex.hazard_no_f53_cliff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Vortex.hazard_no_f53_cliff

/-- info: 'Vortex.hazard_above_f53_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.hazard_above_f53_exact

/-- info: 'Vortex.for_add_win' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.for_add_win

/-- info: 'Vortex.dict_arith_win' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.dict_arith_win

/-- info: 'Vortex.const_arith_win' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.const_arith_win

/-- info: 'Vortex.AOp.eval_eq_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.AOp.eval_eq_exact

/-- info: 'Vortex.policyRow_signed_viaFoR' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.policyRow_signed_viaFoR

/-- info: 'Vortex.policyRow_float_alp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.policyRow_float_alp

/-- info: 'Vortex.tyToDType_no_float' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Vortex.tyToDType_no_float

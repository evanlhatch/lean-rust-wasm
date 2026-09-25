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

import Kit.Relation
import Kit.Hyper
import Kit.Obligation
import Kit.CheckedProp
import Kit.Registry
import Kit.Change
import Kit.Observer
import Kit.CodeRegistry
import Kit.Varint
import Kit.Text
import Kit.Duel
import Kit.Mangle

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

/-- info: 'Kit.CodeRegistry.sortedCodes_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.CodeRegistry.sortedCodes_iff

/-- info: 'Kit.codeRegistryWf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.codeRegistryWf

-- The ledger's grammar migration: the file format's law is the generic
-- theorems' instance — the footprints stay in the core triple (the
-- derived parse/print + the certificate's decide, no new trust).
/-- info: 'Kit.Ledger.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Ledger.parse_print

/-- info: 'Kit.Ledger.print_parse_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Ledger.print_parse_raw

/-- info: 'Kit.Ledger.toRow_rowEncode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Ledger.toRow_rowEncode

/-- info: 'Kit.Ledger.ledgerCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Ledger.ledgerCert

/-- info: 'Kit.Ledger.parse_print_selfStable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Ledger.parse_print_selfStable

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

-- The Galois connection (A3): the tie to the Abstraction grade + the
-- coarsening-preserves-claims corollaries — the core triple only.
/-- info: 'Kit.Observer.Below.toAbstraction' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Observer.Below.toAbstraction

/-- info: 'Kit.Observer.Below.conc_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Observer.Below.conc_iff

/-- info: 'Kit.Observer.refines_below' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Observer.refines_below

/-- info: 'Kit.Observer.equiv_below' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Observer.equiv_below

/-- info: 'Kit.Observer.refines_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Observer.refines_trans

/-- info: 'Kit.Varint.varintCodec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Varint.varintCodec

/-- info: 'Kit.Varint.decVarNat?_encVarNat_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Varint.decVarNat?_encVarNat_append

/-- info: 'Kit.render_app' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.render_app

/-- info: 'Kit.render_cat_strs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.render_cat_strs

/-- info: 'Kit.render_sepBy_strs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.render_sepBy_strs

-- The binary lane's pins: the tie compare + the byte hash (the byte
-- hash's propext is core's Char/UInt64 machinery, not an assumption).
/-- info: 'Kit.Emit.tieBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Emit.tieBytes

/-- info: 'Kit.Emit.bytesHash' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.Emit.bytesHash

-- The duel harness's pins: the verdict fold + the seeded generator
-- + the manifest (pure data folds — propext only, core machinery).
/-- info: 'Kit.Duel.Verdict.foldRows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.Duel.Verdict.foldRows

/-- info: 'Kit.Duel.genBytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.Duel.genBytes

/-- info: 'Kit.Duel.manifestBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.Duel.manifestBody

-- The mangle restoration: the collision bridge + the dup-scan idiom
-- (Classical.choice rides the countP/decide routing, not an assumption
-- smuggled in — the core triple only).
/-- info: 'Kit.collDiags_eq_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.collDiags_eq_nil_iff

/-- info: 'Kit.dupNames_eq_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.dupNames_eq_nil_iff

/-- info: 'Kit.nodup_iff_countP_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.nodup_iff_countP_le_one

/-- info: 'Kit.mangleWf' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.mangleWf

-- The DataRegistry insert restoration + the determinism law + the
-- indexed-name space.
/-- info: 'Kit.DataRegistry.lookup?_ok_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.DataRegistry.lookup?_ok_unique

/-- info: 'Kit.DataRegistry.lookup?_insert_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.DataRegistry.lookup?_insert_self

/-- info: 'Kit.DataRegistry.all_insert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.DataRegistry.all_insert

/-- info: 'Kit.nodupNamesIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kit.nodupNamesIso

-- The relational engine's substrate: THE generic theorem + the §1
-- relation-family laws (pure structural induction + pure logic — zero
-- axioms; a sorry in any of them fails the build).
/-- info: 'Kit.Expr.preserves' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Expr.preserves

/-- info: 'Kit.Expr.pipeline' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Expr.pipeline

/-- info: 'Kit.Expr.chain' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Expr.chain

/-- info: 'Kit.Interpretation.ofPreserves_agrees' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Interpretation.ofPreserves_agrees

/-- info: 'Kit.Rel.comp_assoc' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Rel.comp_assoc

/-- info: 'Kit.Rel.trans_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Rel.trans_iff

/-- info: 'Kit.Rel.det_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Rel.det_iff

-- The carrier-as-graph bridge (16 §4.1): the tower-merge theorems per
-- grade + the unit rows (the Codec trans reads `Option.bind_eq_some_iff`
-- — its propext/Quot.sound are the core machinery, not an assumption).
/-- info: 'Kit.Iso.toRel_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Iso.toRel_trans

/-- info: 'Kit.Iso.toRel_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Iso.toRel_refl

/-- info: 'Kit.Retraction.toRel_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Retraction.toRel_trans

/-- info: 'Kit.Retraction.toRel_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Retraction.toRel_refl

/-- info: 'Kit.Codec.toRel_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kit.Codec.toRel_trans

/-- info: 'Kit.Codec.toRel_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Codec.toRel_refl

-- The bridge's remaining grades (16 §4.1): the per-grade rows are
-- axiom-free — the Simulation/Abstraction merges are definitional
-- (`Iff.rfl`), the Normalization collapse spends its own idempotence
-- law and nothing else.
/-- info: 'Kit.Normalization.toRel_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Normalization.toRel_sound

/-- info: 'Kit.Normalization.toRel_comp_self' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Normalization.toRel_comp_self

/-- info: 'Kit.Normalization.toRel_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Normalization.toRel_refl

/-- info: 'Kit.Simulation.toRel_step' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Simulation.toRel_step

/-- info: 'Kit.Simulation.toRel_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Simulation.toRel_trans

/-- info: 'Kit.Simulation.toRel_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Simulation.toRel_refl

/-- info: 'Kit.Abstraction.toRel_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Abstraction.toRel_sound

/-- info: 'Kit.Abstraction.toRel_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Abstraction.toRel_trans

/-- info: 'Kit.Abstraction.toRel_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Abstraction.toRel_refl

/-- info: 'Kit.Iso.toRel_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Iso.toRel_det

/-- info: 'Kit.Retraction.toRel_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Retraction.toRel_det

/-- info: 'Kit.Codec.toRel_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Codec.toRel_det

/-- info: 'Kit.Normalization.toRel_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Normalization.toRel_det

-- The hyperproperty substrate (16 §4.3): the power jump + the flagship
-- hyperproperty + the worked instances (the simp-refutation nets ride
-- propext, the core machinery).
/-- info: 'Kit.Rel.lift2_comp' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Rel.lift2_comp

/-- info: 'Kit.Noninterfering.toPreserves2' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Noninterfering.toPreserves2

/-- info: 'Kit.Noninterfering.ofPreserves2' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Noninterfering.ofPreserves2

/-- info: 'Kit.noninterfering_of_factor' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.noninterfering_of_factor

/-- info: 'Kit.Noninterfering.below' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.Noninterfering.below

/-- info: 'Kit.noninterfering_securityOf' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.noninterfering_securityOf

/-- info: 'Kit.dropSecret_noninterfering' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.dropSecret_noninterfering

/-- info: 'Kit.leakSecret_notNoninterfering' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.leakSecret_notNoninterfering

/-- info: 'Kit.resultOnly_audit_noninterfering' does not depend on any axioms -/
#guard_msgs in
#print axioms Kit.resultOnly_audit_noninterfering

/-- info: 'Kit.leakExec_notNoninterfering' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Kit.leakExec_notNoninterfering

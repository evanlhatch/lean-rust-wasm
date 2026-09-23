/- Axiom gate (lean-gates CI): headline theorems must print only the core
   triple (propext / Classical.choice / Quot.sound). sorryAx or anything
   else fails the build — a stub is a lie, not a shortcut. -/
import CodegenCore
#print axioms CodegenCore.allocateCodes_length
#print axioms CodegenCore.DataRegistry.nodup_map_unique
#print axioms CodegenCore.DataRegistry.nameOf_injective
#print axioms CodegenCore.DataRegistry.lookup?_ok_mem
#print axioms CodegenCore.DataRegistry.lookup?_ok_unique
#print axioms CodegenCore.DataRegistry.lookup?_miss
#print axioms CodegenCore.DataRegistry.lookup?_insert_self
#print axioms CodegenCore.CheckedProp.check_iff
#print axioms CodegenCore.Validation.foldlM_ok
#print axioms CodegenCore.Validation.foldlM_errs
#print axioms CodegenCore.Validation.foldlM_errs_length
#print axioms CodegenCore.Validation.traverse_ok
-- W-iso batch: the Iso graduations ride the same gate
#print axioms CodegenCore.PartialIso.toImageIso
#print axioms CodegenCore.nodupNamesIso
#print axioms CodegenCore.CodedRegistry.idxOf_getElem_inj
#print axioms CodegenCore.CodedRegistry.membersIso
#print axioms CodegenCore.CodedRegistry.finIso
-- The ladder-audit bridge: denseness by construction at the writer
-- (the code at position i IS the position-derived string).
#print axioms CodegenCore.CodedRegistry.allocateCodes_code_eq
-- The decidableNow backend (the obligation machinery's ONE
-- implementation): soundness + completeness ride the core triple —
-- the per-lane `*_sound`/`*_of_claim` theorems route through these.
#print axioms CodegenCore.Obligation.decideEvidence_sound
#print axioms CodegenCore.Obligation.decideEvidence_of_claim
#print axioms CodegenCore.Obligation.decideDischarge_sound
#print axioms CodegenCore.Obligation.decideDischarge_of_claim

-- the shared delta/lens law shape (DisjointCommute): a law field +
-- projections — the two granularities' instances cite THEIR existing
-- theorems, so the cone stays the core triple
#print axioms CodegenCore.DisjointCommute.disjoint_commutes

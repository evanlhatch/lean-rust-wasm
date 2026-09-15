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
#print axioms CodegenCore.iterateBounded_sound
#print axioms CodegenCore.CheckedProp.check_iff
#print axioms CodegenCore.Validation.foldlM_ok
#print axioms CodegenCore.Validation.foldlM_errs
#print axioms CodegenCore.Validation.foldlM_errs_length
#print axioms CodegenCore.Validation.traverse_ok

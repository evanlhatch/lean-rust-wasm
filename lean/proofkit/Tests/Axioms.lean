/- Axiom gate (lean-gates CI): headline theorems must print only the core
   triple (propext / Classical.choice / Quot.sound). sorryAx or anything
   else fails the build — a stub is a lie, not a shortcut. -/
import Proofkit

#print axioms Proofkit.u64add_sub
#print axioms Proofkit.u64add_assoc
#print axioms Proofkit.sumToFast_spec

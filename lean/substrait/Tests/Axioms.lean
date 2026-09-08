/- Axiom gate — the headline theorems must print only the core triple. -/
import Substrait
-- HasCol is a class (no axioms); check the decode round-trip instead
#print axioms Substrait.Decode.Text.parsePlan

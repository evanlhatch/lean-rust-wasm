/- Axiom gate — the dogfood service's headline theorems. The gate runs
   `lean Tests/Axioms.lean` in every lean_pkgs entry; every row must
   print only the core triple (propext/Classical.choice/Quot.sound +
   disclosed native_decide) — a missing row is silent coverage, a stub
   row is a lie. -/
import FeatureFlagsFn

-- THE PROVED-ERASED INVARIANT: the sentinel contract (the host's
-- defensive none-check is erased — its content is this theorem).
#print axioms FeatureFlagsImpl.flag_get_zero_none

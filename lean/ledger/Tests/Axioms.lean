/- Axiom gate — the skeleton. This file exists so `just lean-axioms`
   covers the package uniformly (the gate runs `lean Tests/Axioms.lean`
   in every lean_pkgs entry). The scaffold ships no theorems; the
   headline defs must print only the core triple
   (propext/Classical.choice/Quot.sound + disclosed native_decide).
   Add a `#print axioms` row per headline theorem as they land — a
   missing row is silent coverage, a stub row is a lie. -/
import LedgerFn
import LedgerES

#print axioms LedgerImpl.ledger_get

-- W5.1: the event-sourced dogfood (conservation at the proved tier,
-- the RewindableMachine instance's laws, the decide'd fixture pin)
#print axioms LedgerES.balanceOf_snoc
#print axioms LedgerES.total_snoc_closed
#print axioms LedgerES.total_post_conserves
#print axioms LedgerES.transfer_replay
#print axioms LedgerES.transfer_rewind
#print axioms LedgerES.transfer_rewind_suffix
#print axioms LedgerES.conservation_discharges
#print axioms LedgerES.discharge_tier_agrees

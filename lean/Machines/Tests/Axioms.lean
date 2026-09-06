/- Axioms gate (drift CI 7.3.3). -/
import Machines
#print axioms Machines.Machine.run_preserves
#print axioms Machines.RewindableMachine.rewind_suffix
#print axioms Machines.Machine.Refines.run_sim
#print axioms Machines.Machine.compose_commute
#print axioms Machines.ConvergentMachine.terminates
#print axioms Machines.Convergent.run_length_le
#print axioms Machines.Convergent.run_length_bound
#print axioms Machines.Convergent.terminates

-- Machines.Sync (the asyncbound primitive contracts)
#print axioms Machines.Sync.latch_countDown_enabled
#print axioms Machines.Sync.latch_wait_stable
#print axioms Machines.Sync.latch_countDown_closed
#print axioms Machines.Sync.mpsc_send_full_rejected
#print axioms Machines.Sync.mpsc_closed_rejected
#print axioms Machines.Sync.oneshot_send_once
#print axioms Machines.Sync.oneshot_recv_needs_sent
#print axioms Machines.Sync.barrier_arrive_full_rejected
#print axioms Machines.Sync.sem_acquire_empty_rejected
#print axioms Machines.Sync.sem_release_full_rejected

-- the liveness readings (blocked-becomes-enabled)
#print axioms Machines.Sync.mpsc_blocked_send_unblocks
#print axioms Machines.Sync.sem_blocked_acquire_unblocks
#print axioms Machines.Sync.latch_blocked_wait_unblocks

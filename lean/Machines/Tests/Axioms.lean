/- Axioms gate (drift CI 7.3.3). -/
import Machines
#print axioms Machines.Machine.run_preserves
#print axioms Machines.RewindableMachine.rewind_suffix
#print axioms Machines.Machine.Refines.run_sim
#print axioms Machines.Machine.compose_commute
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

-- Machines.Sim (the DST core)
#print axioms Machines.Sim.stepSim_det
#print axioms Machines.Sim.simTrace_congr
#print axioms Machines.Sim.runSim_congr
#print axioms Machines.Sim.simTrace_length
#print axioms Machines.Sim.stepSim_conserves
#print axioms Machines.Sim.no_loss
#print axioms Machines.Sim.stepSim_inflight_sublist
#print axioms Machines.Sim.schedulable_fires
#print axioms Machines.Sim.Fires_clock
#print axioms Machines.Sim.deliver_swap
#print axioms Machines.Sim.deliver_order_irrelevant
#print axioms Machines.Sim.zset_sim_two_replica
#print axioms Machines.Sim.zset_deliver_order_irrelevant

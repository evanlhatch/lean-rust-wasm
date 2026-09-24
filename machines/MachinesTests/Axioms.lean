/-
# MachinesTests.Axioms — the axiom self-check

#print axioms over the machines' laws, pinned by #guard_msgs — the
expected outputs name the CORE TRIPLE AT MOST (propext,
Classical.choice, Quot.sound — every set below is a subset; no `sorry`,
no new axiom). If a `sorry` or a NEW axiom ever sneaks into a law, the
printed set changes and this file FAILS THE BUILD — the drift is loud,
not silent. Evidence, not architecture — the five-question block lives
in the modules under test.
-/

import Machines

/-- info: 'Machines.Machine.step_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.Machine.step_iff

/-- info: 'Machines.Machine.reachable_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Machine.reachable_run

/-- info: 'Machines.Machine.run_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Machine.run_reachable

/-- info: 'Machines.Exec.exec_run' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.Exec.exec_run

/-- info: 'Machines.Exec.run_exec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Exec.run_exec

/-- info: 'Machines.check_proved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.check_proved

/-- info: 'Machines.check_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.check_refuted

/- The EventSpec/guard layer: preservation + the inversions. -/
/-- info: 'Machines.MachineWithInv.step?_preserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.MachineWithInv.step?_preserves

/-- info: 'Machines.MachineWithInv.run_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.MachineWithInv.run_preserves

/-- info: 'Machines.MachineWithInv.reachable_preserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.MachineWithInv.reachable_preserves

/-- info: 'Machines.MachineWithInv.step?_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.MachineWithInv.step?_eq_some

/-- info: 'Machines.Machine.run_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Machine.run_preserves

/- The parameterized frontier fold (Explore.lean's `foldFrontier` — the
   ONE fold behind the verdict search AND the battery's reachable
   fragment; the consolidation of the review's finding #4). -/
/-- info: 'Machines.foldFrontier_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.foldFrontier_run

/-- info: 'Machines.foldFrontier_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.foldFrontier_coverage

/-- info: 'Machines.closure_covers' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.closure_covers

/-- info: 'Machines.seen_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.seen_refuted

/- The battery: the reachable-fold soundness/completeness + the bridges. -/
/-- info: 'Machines.Testing.reachableAux_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Testing.reachableAux_run

/-- info: 'Machines.Testing.reachableAux_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Testing.reachableAux_complete

/-- info: 'Machines.Testing.deadlockFree_proved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Testing.deadlockFree_proved

/-- info: 'Machines.Testing.guardCoverage_proved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Testing.guardCoverage_proved

/-- info: 'Machines.Testing.guardCoverage_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Testing.guardCoverage_refuted

/- The fusion layer: the dI iso, the journal/replay bridges, the
   bisimulation as stream equality. -/
/-- info: 'Machines.I_D' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Machines.I_D

/-- info: 'Machines.D_I' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Machines.D_I

/-- info: 'Machines.Fusion.journal_eq_D_run' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Machines.Fusion.journal_eq_D_run

/-- info: 'Machines.Fusion.replay_eq_run' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Machines.Fusion.replay_eq_run

/-- info: 'Machines.Fusion.bisim_iff_respStreams' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Machines.Fusion.bisim_iff_respStreams

/-- info: 'Machines.Fusion.respTrace_tick_agree' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.Fusion.respTrace_tick_agree

/-- info: 'Machines.Fusion.respStream_equiv' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Machines.Fusion.respStream_equiv

/-- info: 'Machines.Machine.tick_of_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Machine.tick_of_step

/-- info: 'Machines.compose_inv_cancel' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.compose_inv_cancel

/-- info: 'Machines.Fusion.respTrace_exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Fusion.respTrace_exec

/-- info: 'Machines.Fusion.traceStates_exec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Fusion.traceStates_exec

/- The graduation (16-surface §5.1): the Exec ≅ runnable-tapes iso. -/
/-- info: 'Machines.Exec.execIso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Exec.execIso

/-- info: 'Machines.Exec.execRetraction' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Exec.execRetraction

/- THE CLOSURE BRIDGE (Machines.Closure): the frontier fold = the
   Datalog closure. The encoding bridge is core-triple-only; the
   agreement + payoff cite `Datalog.deriv_iff_eval`, whose
   Classical.choice they inherit (named, not grown here). -/
/-- info: 'Machines.Closure.deriv_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Closure.deriv_reachable

/-- info: 'Machines.Closure.deriv_iff_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Closure.deriv_iff_reachable

/-- info: 'Machines.Closure.bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Closure.bridge

/-- info: 'Machines.Closure.inv_of_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Closure.inv_of_eval

/-
# EffectsTests.Axioms — the axiom self-check

#print axioms over the effects lane's laws, pinned by #guard_msgs — the
expected outputs name the CORE TRIPLE AT MOST (propext, Quot.sound;
Classical.choice never appears — the laws are membership-level
inductions and cited cites). If a `sorry` or a NEW axiom ever sneaks
into a law, the printed set changes and this file FAILS THE BUILD —
the drift is loud, not silent.

Evidence, not architecture — the five-question blocks live in the
modules under test.
-/

import Effects

open Effects Effects.Resource

/-- info: 'Effects.mem_unionMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.mem_unionMem

/-- info: 'Effects.Row.sub_iff_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effects.Row.sub_iff_le

/-- info: 'Effects.Row.join_idem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.Row.join_idem

/-- info: 'Effects.Row.join_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.Row.join_comm

/-- info: 'Effects.Row.join_assoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.Row.join_assoc

/-- info: 'Effects.Row.join_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.Row.join_le

/-- info: 'Effects.row_blind_to_double_spend' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.row_blind_to_double_spend

/-- info: 'Effects.Resource.Ctx.kept_survive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.Resource.Ctx.kept_survive

/-- info: 'Effects.Resource.Ctx.spent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.Resource.Ctx.spent

/-- info: 'Effects.Resource.Handle.split_disallows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.Resource.Handle.split_disallows

/-- info: 'Effects.Resource.spendCount_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effects.Resource.spendCount_compose

/-- info: 'Effects.Resource.monus_cannot_refuse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effects.Resource.monus_cannot_refuse

/-- info: 'Effects.Cmd.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms Effects.Cmd.frame

/-- info: 'Effects.wr_frame_of_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effects.wr_frame_of_join

/-- info: 'Effects.Cmd.seq_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effects.Cmd.seq_reads

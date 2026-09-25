/-
# GuestTests.StdAxioms — the axiom self-check

#print axioms over the std's laws, pinned by #guard_msgs — the
expected output is the CORE TRIPLE ONLY (propext, Classical.choice,
Quot.sound — every set below is a subset; no `sorry`, no new axiom).
If a `sorry` or a NEW axiom ever sneaks into a law, the printed set
changes and this file FAILS THE BUILD — the drift is loud, not silent.
Evidence, not architecture — the five-question block lives in the
modules under test.
-/

import Guest.Std

/-- info: 'GuestStd.strlen_eq_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GuestStd.strlen_eq_length

/-- info: 'GuestStd.strcat_eq_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GuestStd.strcat_eq_append

/-- info: 'GuestStd.streq_eq_beq' does not depend on any axioms -/
#guard_msgs in
#print axioms GuestStd.streq_eq_beq

/-- info: 'GuestStd.strof_eq_ofList' does not depend on any axioms -/
#guard_msgs in
#print axioms GuestStd.strof_eq_ofList

/-- info: 'GuestStd.strlen_strcat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GuestStd.strlen_strcat

/-- info: 'GuestStd.listLenU64_eq_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GuestStd.listLenU64_eq_length

/-- info: 'GuestStd.sumU64_eq_foldr' does not depend on any axioms -/
#guard_msgs in
#print axioms GuestStd.sumU64_eq_foldr

/-- info: 'GuestStd.natToUInt64_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GuestStd.natToUInt64_succ

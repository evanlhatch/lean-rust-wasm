/-
# ScaffoldTests.Axioms — the axiom self-check

#print axioms over the scaffold's pure faces, pinned by #guard_msgs —
the expected set is the CORE TRIPLE ONLY (the axiom gate's allowlist;
`validate`/`generate` fold List/String + the closed-world Diag
constructor, whose suggest engine rides core's levenshtein DP). If a
`sorry` or a NEW axiom ever sneaks into the generator, the printed set
changes and this file FAILS THE BUILD — the drift is loud, not silent.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import Scaffold

open Scaffold

/-- info: 'Scaffold.validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scaffold.validate

/-- info: 'Scaffold.generate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scaffold.generate

/-- info: 'Scaffold.capsOf' does not depend on any axioms -/
#guard_msgs in
#print axioms Scaffold.capsOf

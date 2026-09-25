/-
# ComponentTests.Axioms — the axiom self-check over the component lane's pure faces

`#print axioms` over the component emission's pure faces, pinned by
#guard_msgs — the expected output is the core triple at most (propext,
Classical.choice, Quot.sound). If a `sorry` or a NEW axiom ever sneaks
into a face, the printed set changes and this file FAILS THE BUILD —
the drift is loud, not silent (the GuestTests.Axioms pattern).

The driver IO faces (`importFixture`, `readDecl?`, the file reads)
are the driver's IO discipline, not pure code — NOT pinned here.
-/

import Guest
import Guest.Component
import Wit

-- The component emission's pure faces: the type encoding, the
-- flattening, the skew check, the binary fold, the regen.
/-- info: 'Guest.Component.ScalarPrim' does not depend on any axioms -/
#guard_msgs in
#print axioms Guest.Component.ScalarPrim

/-- info: 'Guest.Component.flatOf' does not depend on any axioms -/
#guard_msgs in
#print axioms Guest.Component.flatOf

/-- info: 'Guest.Component.tyEncAt' does not depend on any axioms -/
#guard_msgs in
#print axioms Guest.Component.tyEncAt

/-- info: 'Guest.Component.flatten' does not depend on any axioms -/
#guard_msgs in
#print axioms Guest.Component.flatten

/-- info: 'Guest.Component.needsAdapters' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.Component.needsAdapters

/-- info: 'Guest.Component.check' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.Component.check

/-- info: 'Guest.Component.encodeComponent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Guest.Component.encodeComponent

/-- info: 'Guest.Component.regen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.Component.regen

/-- info: 'Guest.Component.ComponentError.toDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Guest.Component.ComponentError.toDiag

-- The renderer's world face (the artifact's text lane).
/-- info: 'Wit.Render.worldFile' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Wit.Render.worldFile

-- The world carrier's accessor.
/-- info: 'Wit.Item.name' does not depend on any axioms -/
#guard_msgs in
#print axioms Wit.Item.name

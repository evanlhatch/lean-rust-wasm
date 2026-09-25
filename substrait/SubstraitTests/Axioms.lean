/-
# SubstraitTests.Axioms — the axiom self-check

#print axioms over the substrait lane's theorems, pinned by #guard_msgs —
the expected outputs name the CORE TRIPLE AT MOST. If a `sorry` or a NEW
axiom ever sneaks into a theorem, the printed set changes and this file
FAILS THE BUILD — the drift is loud, not silent.
-/

import Substrait

open Substrait

/-- info: 'Substrait.Typed.Schema.get?_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.Schema.get?_lt

/-- info: 'Substrait.Text.parseScalarGo_typeChars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Text.parseScalarGo_typeChars

/-- info: 'Substrait.Typed.Expr.toProto_ords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.Expr.toProto_ords

/-- info: 'Substrait.Typed.Args.toProto_ords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.Args.toProto_ords

/-- info: 'Substrait.Typed.Rel.toProto_width' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.Rel.toProto_width

/-- info: 'Substrait.Typed.Rel.toPlan_fns_declared' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.Rel.toPlan_fns_declared

/-- info: 'Substrait.Typed.Rel.toProto_width' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.Rel.toProto_width

/-- info: 'Substrait.Proto.JoinType.width_add' does not depend on any axioms -/
#guard_msgs in
#print axioms Substrait.Proto.JoinType.width_add

/-! ## the slice-2 theorems (the eval bridges + the name tables + the
corollary) -/

/-- info: 'Substrait.Typed.Row.get_resolves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Typed.Row.get_resolves

/-- info: 'Substrait.Typed.castVal_self' does not depend on any axioms -/
#guard_msgs in
#print axioms Substrait.Typed.castVal_self

/-- info: 'Substrait.Typed.filterRowsM_ok_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.filterRowsM_ok_sound

/-! ## the typed decode's laws (the read direction's rungs) -/

/-- info: 'Substrait.Decode.decTypedRel?_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Decode.decTypedRel?_ok

/-- info: 'Substrait.Decode.decTypedPlan?_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Decode.decTypedPlan?_ok

/-- info: 'Substrait.Decode.decTypedSchema?_colsToProto' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Decode.decTypedSchema?_colsToProto

/-- info: 'Substrait.Typed.filterRowsM_ok_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.filterRowsM_ok_complete

/-- info: 'Substrait.Typed.matchedRow_ok_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.matchedRow_ok_sound

/-- info: 'Substrait.Typed.evalJoinPairs_ok_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.evalJoinPairs_ok_sound

/-- info: 'Substrait.Typed.walkProto_ok_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.walkProto_ok_length

/-- info: 'Substrait.Typed.anyExprListToProto_ok_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.anyExprListToProto_ok_length

/-- info: 'Substrait.Typed.measureListToProto_ok_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Substrait.Typed.measureListToProto_ok_length

/-- info: 'Substrait.Text.parseType_typeText_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Text.parseType_typeText_scalar

/-- info: 'Substrait.Text.findName_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Text.findName_self

/-- info: 'Substrait.Text.sortDirOfName_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Text.sortDirOfName_self

/-- info: 'Substrait.Text.setOpOfName_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Text.setOpOfName_self

/-- info: 'Substrait.Text.joinTypeOfName_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Text.joinTypeOfName_self

/-- info: 'Substrait.Text.NameTable.ofName_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Text.NameTable.ofName_self

/-- info: 'Substrait.Text.NameTable.ofName_miss' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Text.NameTable.ofName_miss

/-- info: 'Substrait.Wire.decReadBody?_encReadBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Wire.decReadBody?_encReadBody

/-- info: 'Substrait.Wire.decNatLit?_encNatLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Wire.decNatLit?_encNatLit

/-- info: 'Substrait.Wire.decRelBody?_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Wire.decRelBody?_law

/-- info: 'Substrait.Wire.decPlanBody?_encPlanBody_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Wire.decPlanBody?_encPlanBody_append

/-- info: 'Substrait.Wire.decPlan?_encPlan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Substrait.Wire.decPlan?_encPlan

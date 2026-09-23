/-
# KitTests.LaneReg — the demo lane's registration module

The lane substrate's end-to-end fixture, part 1: the item type + the
ONE `register_lane` call. This module's generated initializers (the
extension + the attribute mount) run at import — so the consumption
(the `@[demoLaneItem]` entries, the replay/fold pins, the curated
failures) lives in the NEXT module, `KitTests.LaneDemo` (a module's
own initializers do not run during its own elaboration).

Name convention (Kit.Lane's header): base `demoLaneItem` (the item
type's last component decapitalized) → `demoLaneItemExt`, the
`@[demoLaneItem]` attribute, `getDemoLaneItems`, `demoLaneItemRegistry`,
`demoLaneItemNameOf`, `demoLaneItemAttrReg`.

Provenance: fresh (the fixture IS the substrate's first consumer; no
legacy content).
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import Kit.Lane

/-- The demo lane's item type. -/
structure DemoLaneItem where
  name : String
  weight : Nat
deriving Inhabited, Repr, BEq

register_lane DemoLaneItem where
  naming := fun it => it.name

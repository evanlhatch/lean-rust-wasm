/-
# KitTests.LaneReg2 — THE ACCEPTANCE FIXTURE (wave-30 A2): a new lane = ONE row + ONE reader

The one-log registry discipline's acceptance: a NEW lane lands with a
SINGLE `register_lane` call (the lane's row family in the ONE log) +
ONE reader (the derived accessor) — ZERO substrate change. The lane's
identity is data (`extraLaneLaneId`); the shared log routes by it;
this module's generated initializers run at import — the consumption
(the entry, the replay pins, the family pin) lives in the NEXT module,
`KitTests.LaneDemo2`.

Provenance: fresh (the A2 acceptance fixture).
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import Kit.Lane

/-- The new lane's item type (deliberately distinct from the demo
    lane's: the closed-world family holds both). -/
structure ExtraLaneItem where
  name : String
  mass : Nat
deriving Inhabited, Repr, BEq

-- THE ONE ROW: the lane's registration — nothing else lands.
register_lane ExtraLaneItem where
  naming := fun it => it.name

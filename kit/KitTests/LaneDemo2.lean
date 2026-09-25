/-
# KitTests.LaneDemo2 — THE ACCEPTANCE FIXTURE, part 2: the new lane's reader + the shared-log pins

The one-log discipline's acceptance face: the new lane's entry
registered into the ONE log; the reader (the routed replay) answers
ONLY this lane's rows; the two lanes coexist in one log with their
orders and contents independent; the closed-world family is the log's
lane-id data. A drift FAILS the build.

Provenance: fresh (the A2 acceptance fixture).
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import KitTests.LaneDemo
import KitTests.LaneReg2

@[extraLaneItem]
def extraEntry : ExtraLaneItem := { name := "extra", mass := 9 }

-- THE READER (the ONE reader the lane lands): the routed replay —
-- this lane's rows only, in registration order.
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  match ← getExtraLaneItems env with
  | .error e => Lean.throwError s!"extra lane replay refused: {e}"
  | .ok items =>
    unless items.length == 1 && items[0]!.name == "extra"
        && items[0]!.mass == 9 do
      Lean.throwError s!"extra lane replay drifted: {items.map (·.name)}"
  -- THE ROUTING TOOTH: the OTHER lane's rows do not leak into this
  -- reader (the fold filters by the lane's id, as data).
  match ← getDemoLaneItems env with
  | .error e => Lean.throwError s!"demo lane replay refused: {e}"
  | .ok demoItems =>
    unless (demoItems.map (·.name)) == ["first", "second"] do
      Lean.throwError s!"the demo lane's replay drifted: {(demoItems.map (·.name))}"

-- THE CLOSED-WORLD FAMILY: the ONE log's lane ids, first-seen order —
-- both lanes are IN the one log, each with its own rows.
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let fam := Kit.Lane.laneFamilies env
  unless fam.contains "DemoLaneItem"
      && fam.contains "ExtraLaneItem" do
    Lean.throwError s!"the lane family drifted: {fam}"
  unless (Kit.Lane.laneRows env "ExtraLaneItem").length == 1
      && (Kit.Lane.laneRows env "DemoLaneItem").length == 2 do
    Lean.throwError "the routing counts drifted"

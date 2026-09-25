/-
# KitTests.LaneDemo — the demo lane's consumption module (end-to-end + controls)

The lane substrate's end-to-end fixture, part 2: the `@[demoLaneItem]`
entries append at elaboration; the replay accessor + the fold hook read
the live environment (the `#eval` pins — a drift FAILS the build); the
curated failures are the `#guard_msgs` negative controls (a message
drift FAILS the build).

Provenance: fresh (the fixture IS the substrate's first consumer).
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import KitTests.LaneReg

@[demoLaneItem]
def firstEntry : DemoLaneItem := { name := "first", weight := 1 }

@[demoLaneItem]
def secondEntry : DemoLaneItem := { name := "second", weight := 2 }

-- The end-to-end pin: two entries registered, replayed in registration
-- order, materialized into the registry (the fold hook fires).
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  match ← demoLaneItemRegistry env with
  | .error e => Lean.throwError s!"lane fold drifted: {e}"
  | .ok reg =>
    match ← getDemoLaneItems env with
    | .error e => Lean.throwError s!"lane replay refused: {e}"
    | .ok items =>
      if reg.items.length == 2
          && reg.items[0]!.name == "first"
          && reg.items[1]!.name == "second"
          && items.length == 2 then
        pure ()
      else
        Lean.throwError "lane replay drifted: wrong item count or order"

-- THE ENTOURAGE HOOKS (16-surface §3 at the lane face): the
-- registration auto-filled the obligation view (the attests labels,
-- one per item) + the ledger demand (the lane records the collections
-- it READS — its own extension — plus the rows it folds). A drift
-- FAILS the build.
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let d := demoLaneItemLedgerDemand env
  if demoLaneItemObligationView env == ["first", "second"]
      && d.collections == [Kit.Ledger.namesOf "Kit.Lane.laneLogExt"]
      && d.rows == [Kit.Ledger.namesOf "first", Kit.Ledger.namesOf "second"]
      && d.emitterRev == "register_lane" then
    pure ()
  else
    Lean.throwError "lane entourage hooks drifted: the obligation view or \
      the ledger demand did not auto-fill"

/- THE NEGATIVE CONTROLS, as the ONE teeth shape (Kit.Lane's
    lane-teeth macro — the audit's E3): the control command is taken
    VERBATIM (the #guard_msgs shape — nothing spliced); the expected
    refusals are computed from the mount's own Diag constructors and
    checked byte-for-byte; the dup tooth ALSO pins its valid-list
    against the live registration state. -/
lane_dup_tooth "first" ["first", "second"] in
  @[demoLaneItem] def dupEntry : DemoLaneItem := { name := "first", weight := 3 }

lane_wrong_tooth DemoLaneItem in
  @[demoLaneItem] def wrongEntry : Nat := 5

/- NEGATIVE CONTROL: the `naming` clause is required — the curated
    usage message (KL0006). -/
/-- error: [KL0006] error: register_lane: the `where naming := <fn>` clause is required — naming is the item's naming function (the registry's lookup key); valid usage: `register_lane <Item> where naming := <fn>` with the optional clauses `attr := <name>` (the attribute's name) and `builder := <fn>` (a custom builder `Environment → Name → Except String Item`) -/
#guard_msgs in
register_lane Broken where
  attr := brokenLane

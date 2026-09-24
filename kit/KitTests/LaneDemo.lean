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
  match demoLaneItemRegistry env with
  | .error e => Lean.throwError s!"lane fold drifted: {e}"
  | .ok reg =>
    if reg.items.length == 2
        && reg.items[0]!.name == "first"
        && reg.items[1]!.name == "second"
        && (getDemoLaneItems env).length == 2 then
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
      && d.collections == [Kit.Ledger.namesOf "KitTests.demoLaneItemExt"]
      && d.rows == [Kit.Ledger.namesOf "first", Kit.Ledger.namesOf "second"]
      && d.emitterRev == "register_lane" then
    pure ()
  else
    Lean.throwError "lane entourage hooks drifted: the obligation view or \
      the ledger demand did not auto-fill"

/- NEGATIVE CONTROL: a duplicate entry name is the closed-world
    refusal (Kit.Diag's `closedWorld` — got + the taken names + the
    ONE engine's did-you-mean). -/
/-- error: [KL0001] error: @[demoLaneItem] dupEntry: `first` is already a registered item — names must be fresh (got: first) — valid: first, second — did you mean: first? -/
#guard_msgs in
@[demoLaneItem] def dupEntry : DemoLaneItem := { name := "first", weight := 3 }

/- NEGATIVE CONTROL: the entry must be a `def` of the lane's item
    type — the curated usage message (KL0003). -/
/-- error: [KL0003] error: @[demoLaneItem] wrongEntry: the entry's type is not the lane's item type `DemoLaneItem` — valid usage: `@[demoLaneItem] def wrongEntry : DemoLaneItem := <value>` -/
#guard_msgs in
@[demoLaneItem] def wrongEntry : Nat := 5

/- NEGATIVE CONTROL: the `naming` clause is required — the curated
    usage message (KL0006). -/
/-- error: [KL0006] error: register_lane: the `where naming := <fn>` clause is required — naming is the item's naming function (the registry's lookup key); valid usage: `register_lane <Item> where naming := <fn>` with the optional clauses `attr := <name>` (the attribute's name) and `builder := <fn>` (a custom builder `Environment → Name → Except String Item`) -/
#guard_msgs in
register_lane Broken where
  attr := brokenLane

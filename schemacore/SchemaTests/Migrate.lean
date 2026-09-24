/- # SchemaTests.Migrate — the migration lane's suite

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5). The fixture is a WIDENING chain — a `bounded 42` qty
field widened to `bounded 100` then `bounded 200` (the
`SchemaCore.widenBounded` exemplar, Diff.lean's remedy half) — with the
derived upcaster exercised end to end: the derivation (from the diff's
change set + the registered remedies), the value-level upcast, the
replay-preservation law (THE ONE INDUCTION, live), the composition law
(two hops ≡ direct), the event-lane seed (`replayMigrated?` consumes
the derived upcaster under the witness), and EVERY refusal arm's
teeth.

Suites:
1. `migrateSpec` — the derivation + the row pin + the replay law +
   the seed + the composition (both faces: the composite ≡ the two
   hops, and the per-diff remedy-registry boundary).
2. `migrateRefusalSpec` — every refusal arm fires with its NAMED
   obligation (removed / unremedied / reordered / mid-addition /
   unstable key / no-default) + the negative controls.

Evidence, not architecture — the five-question block lives in the
modules under test (SchemaCore.Migrate / SchemaCore.Diff /
SchemaCore.Event).
-/

import TestingKit.Harness
import SchemaCore
import SchemaTests.Events

open SchemaCore TestingKit

/-! ## The fixture: a bounded-cap widening chain -/

/-- v1: the quantity is capped at 42. -/
def migFs1 : List Field :=
  [{ name := "id", ty := .u64 }, { name := "qty", ty := .bounded 42 }]

/-- v2: the quantity widened to 100. -/
def migFs2 : List Field :=
  [{ name := "id", ty := .u64 }, { name := "qty", ty := .bounded 100 }]

/-- v3: the quantity widened again, to 200. -/
def migFs3 : List Field :=
  [{ name := "id", ty := .u64 }, { name := "qty", ty := .bounded 200 }]

def migItem1 : Item := { name := "Widget", fields := migFs1 }
def migItem2 : Item := { name := "Widget", fields := migFs2 }
def migItem3 : Item := { name := "Widget", fields := migFs3 }

/-- The remedy: the bounded-cap widening (Diff.lean's exemplar — the
    total map `Fin.castLE`, with `widenBounded_sound` its obligation). -/
def w122 : FieldMigration := widenBounded "qty" 42 100 (by decide)
def w232 : FieldMigration := widenBounded "qty" 100 200 (by decide)
def w132 : FieldMigration := widenBounded "qty" 42 200 (by decide)

def mig12 : Migration := { item := "Widget", fields := [w122] }
def mig23 : Migration := { item := "Widget", fields := [w232] }
def mig13 : Migration := { item := "Widget", fields := [w132] }

/-- A v1 row: id 7, qty 40 (under the 42 cap). -/
def wRowA : RowVals migFs1 :=
  .cons (.u64 7) (.cons (.bounded ⟨40, by decide⟩) .nil)

/-- A second v1 row: id 8, qty 5. -/
def wRowB : RowVals migFs1 :=
  .cons (.u64 8) (.cons (.bounded ⟨5, by decide⟩) .nil)

/-- The same row, v2-typed (the widened pin's expectation). -/
def wRowA2 : RowVals migFs2 :=
  .cons (.u64 7) (.cons (.bounded ⟨40, by decide⟩) .nil)

/-- The fixture journal: insert then update (v1 deltas). -/
def migLog : List (RowDelta migFs1) := [.insert wRowA, .update wRowB]

/-- The fixture's derived plans — the three derivations (v1→v2, v2→v3,
    and the DIRECT v1→v3 with its own remedy). `none` is the suites'
    loud failure, never a silent skip. -/
structure MigFixture where
  plan12 : FieldPlan migFs1 migFs2
  plan23 : FieldPlan migFs2 migFs3
  plan13 : FieldPlan migFs1 migFs3

def migFixture? : Option MigFixture :=
  match deriveUpcaster "id" [mig12] migItem1 migItem2,
        deriveUpcaster "id" [mig23] migItem2 migItem3,
        deriveUpcaster "id" [mig13] migItem1 migItem3 with
  | .ok p12, .ok p23, .ok p13 => some { plan12 := p12, plan23 := p23, plan13 := p13 }
  | _, _, _ => none

/-! ## Suite 1 — the derivation, the replay law, the seed, the composition -/

def migrateSpec : Spec :=
  Spec.ofList "the migration lane: derive, upcast, replay, compose"
    (fun _ => do
      match migFixture? with
      | some fx =>
          let compPlan := FieldPlan.comp fx.plan23 fx.plan12
          -- the event lane's seed: the derived upcaster under the
          -- operator's witness (the gate consumes it via replayMigrated?)
          let seed12 := MigrationSeed.ofPlan fx.plan12 "mig/widget/42-100" "w1"
          let seed12Unw : MigrationSeed migFs1 migFs2 :=
            { seed12 with witness? := none }
          -- THE DERIVATION: key-stable (stable identities, 08 §19)
          assert (fx.plan12.stableKey "id" && fx.plan23.stableKey "id"
              && fx.plan13.stableKey "id" && compPlan.stableKey "id")
            "the derived plans' key stability drifted"
          -- THE VALUE PIN: the widened row keeps the id AND the qty's
          -- number (widening, not reinterpretation — the soundness
          -- obligation's runtime face)
          assert (renderTable [fx.plan12.upcast wRowA] == renderTable [wRowA2])
            "the widened row drifted"
          assert (match RowVals.project? migFs2 (fx.plan12.upcast wRowA) "qty" with
            | some fv => fv.ty == .bounded 100 && toString fv.val == "40"
            | none => false)
            "the widened value is not the SAME number under the new cap"
          -- THE ONE INDUCTION, live: the migrated replay IS the replay
          -- of the migrated log (upcast_replay's runtime face)
          assert (renderTable
                (replay "id" (migLog.map fx.plan12.upcastDelta)
                  ([] : List (RowVals migFs2)))
              == renderTable
                ((replay "id" migLog ([] : List (RowVals migFs1)))
                  |>.map fx.plan12.upcast))
            "the replay-preservation law drifted"
          -- THE EVENT-LANE INTEGRATION: the derived seed replays
          -- through the Event lane's gate, under the witness
          assert (match replayMigrated? "id" seed12 migLog
                    ([] : List (RowVals migFs2)) with
            | .ok t => renderTable t == renderTable
                (replay "id" (migLog.map fx.plan12.upcastDelta)
                  ([] : List (RowVals migFs2)))
            | .error _ => false)
            "the seeded replay drifted"
          -- THE COMPOSITION LAW: two hops ≡ the composed plan ≡ the
          -- direct derivation (upcast_comp's runtime face + the
          -- value-level agreement of the chained widenings)
          assert (renderTable [compPlan.upcast wRowA]
              == renderTable [fx.plan23.upcast (fx.plan12.upcast wRowA)])
            "the composed upcaster is not the two-hop pipeline"
          assert (renderTable [compPlan.upcast wRowA]
              == renderTable [fx.plan13.upcast wRowA])
            "two hops ≢ the direct derivation"
          assert (renderLog (compPlan.upcastDelta (.insert wRowA))
              == renderLog (fx.plan13.upcastDelta (.insert wRowA)))
            "the composed event upcaster drifted"
          -- THE DIFF CONSUMPTION: the verdict gates the derivation's
          -- pre-check (remedied vs unremedied, Diff.lean's three-way)
          assert (verdictOf (diff [migItem1] [migItem2]) [mig12] == .remedied
              && verdictOf (diff [migItem1] [migItem2]) [] == .unremedied)
            "the verdict drifted"
          -- THE HONEST BOUNDARY: the remedy REGISTRY is per-diff — the
          -- two hops' remedies (42→100, 100→200) do not match the
          -- direct diff's finding (42→200) by type; the composition
          -- lives at the upcaster (pinned above), not in the registry
          assert (verdictOf (diff [migItem1] [migItem3]) [mig12, mig23]
              == .unremedied)
            "the registry boundary drifted"
      | none => assert false "the fixture derivations must succeed")
    [ ("the unremedied retype derives",
        fun _ =>
          assert (match deriveUpcaster "id" [] migItem1 migItem2 with
            | .ok _ => true | .error _ => false)
          "control fired: a retyped field with NO registered remedy must \
            refuse (fieldUnremedied) — never a partial migration")
    , ("the migrated replay loses an event",
        fun _ => match migFixture? with
          | some fx =>
              assert (renderTable
                    (replay "id" (migLog.map fx.plan12.upcastDelta)
                      ([] : List (RowVals migFs2)))
                != renderTable
                    ((replay "id" migLog ([] : List (RowVals migFs1)))
                      |>.map fx.plan12.upcast))
                "control fired: THE ONE INDUCTION holds — the migrated \
                  replay IS the replay of the migrated log, event for event"
          | none => assert false "the fixture derivations must succeed")
    , ("the composed plan differs from the pipeline",
        fun _ => match migFixture? with
          | some fx =>
              assert (renderTable
                  [(FieldPlan.comp fx.plan23 fx.plan12).upcast wRowA]
                != renderTable [fx.plan23.upcast (fx.plan12.upcast wRowA)])
                "control fired: the composition law holds — the composed \
                  plan's upcaster IS the two-hop pipeline"
          | none => assert false "the fixture derivations must succeed")
    , ("the unwitnessed seed replays",
        fun _ => match migFixture? with
          | some fx =>
              let seed12 := MigrationSeed.ofPlan fx.plan12 "mig/widget/42-100" "w1"
              let seed12Unw : MigrationSeed migFs1 migFs2 :=
                { seed12 with witness? := none }
              assert (match replayMigrated? "id" seed12Unw migLog
                        ([] : List (RowVals migFs2)) with
                | .ok _ => true
                | .error _ => false)
                "control fired: an unwitnessed migration REFUSES, loudly, \
                  naming its obligation — the events are not applied"
          | none => assert false "the fixture derivations must succeed")
    , ("widening reinterprets",
        fun _ => match migFixture? with
          | some fx =>
              assert (match RowVals.project? migFs2 (fx.plan12.upcast wRowA)
                        "qty" with
                | some fv => toString fv.val == "41"
                | none => false)
                "control fired: widening preserves the number — the same \
                  40 under the new cap (widenBounded_sound's content)"
          | none => assert false "the fixture derivations must succeed") ]
    4 42

/-! ## Suite 2 — the refusal teeth (every arm, NAMED) -/

/-- The removal fixture: v2 drops the qty field. -/
def migItemRemoved : Item :=
  { name := "Widget", fields := [{ name := "id", ty := .u64 }] }

/-- The reorder fixture: v2 swaps the fields (the name-keyed diff sees
    NOTHING — the walk's positional refusal is the honest face). -/
def migItemReordered : Item :=
  { name := "Widget"
    fields := [{ name := "qty", ty := .bounded 42 }, { name := "id", ty := .u64 }] }

/-- The mid-list addition fixture: v2 inserts a note field BEFORE qty
    (also refused — v1's derivation is order-aligned). -/
def migItemMidAdd : Item :=
  { name := "Widget"
    fields := [ { name := "id", ty := .u64 }
              , { name := "note", ty := .string }
              , { name := "qty", ty := .bounded 42 } ] }

/-- The bounded-KEY fixture: the key field itself widened. -/
def migItemKey1 : Item :=
  { name := "Widget"
    fields := [{ name := "cap", ty := .bounded 42 }, { name := "qty", ty := .u64 }] }

def migItemKey2 : Item :=
  { name := "Widget"
    fields := [{ name := "cap", ty := .bounded 100 }, { name := "qty", ty := .u64 }] }

/-- A remedy for the key's widening (registered — so the pre-check
    passes and the WALK's key-stability refusal is the one that fires). -/
def migKey : Migration :=
  { item := "Widget", fields := [widenBounded "cap" 42 100 (by decide)] }

/-- The no-default fixture: v2 adds a cap-0 bounded field (uninhabited
    — no default exists). The old side is a strict PREFIX of the new
    (no removal in the diff — the noDefault arm is the one that fires). -/
def migItemBare : Item :=
  { name := "Widget", fields := [{ name := "id", ty := .u64 }] }

def migItemNoDefault : Item :=
  { name := "Widget"
    fields := [ { name := "id", ty := .u64 }
              , { name := "z", ty := .bounded 0 } ] }

def migrateRefusalSpec : Spec :=
  Spec.ofList "the derivation refuses, loudly, each arm NAMED"
    (fun _ => do
      -- the UNREMEDIATED retype (no remedy registered): the pre-check's
      -- refusal, naming the diff's finding
      assert (match deriveUpcaster "id" [] migItem1 migItem2 with
        | .error (.fieldUnremedied "Widget" "qty") => true | _ => false)
        "the fieldUnremedied refusal drifted"
      -- the REMOVAL: no value-map target for gone data
      assert (match deriveUpcaster "id" [mig12] migItem1 migItemRemoved with
        | .error (.fieldRemoved "Widget" "qty") => true | _ => false)
        "the fieldRemoved refusal drifted"
      -- the REORDER: the diff is name-keyed and CLEAN here; the walk's
      -- positional refusal is the honest face (the two readings'
      -- boundary, pinned)
      assert (diff [migItem1] [migItemReordered] == []
        && (match deriveUpcaster "id" [mig12] migItem1 migItemReordered with
          | .error (.fieldReordered "Widget" "id") => true | _ => false))
        "the fieldReordered refusal drifted"
      -- the MID-LIST ADDITION: also order-aligned-only
      assert (match deriveUpcaster "id" [mig12] migItem1 migItemMidAdd with
        | .error (.fieldReordered "Widget" "qty") => true | _ => false)
        "the mid-addition refusal drifted"
      -- the UNSTABLE KEY: the key field retyped (even WITH a remedy)
      assert (match deriveUpcaster "cap" [migKey] migItemKey1 migItemKey2 with
        | .error (.keyUnstable "Widget" "cap") => true | _ => false)
        "the keyUnstable refusal drifted"
      -- the NO-DEFAULT add: a cap-0 bounded field is uninhabited
      assert (match deriveUpcaster "id" [mig12] migItemBare migItemNoDefault with
        | .error (.noDefault "Widget" "z") => true | _ => false)
        "the noDefault refusal drifted")
    [ ("the reordered schema's diff is not clean",
        fun _ =>
          assert (diff [migItem1] [migItemReordered] != [])
          "control fired: a reorder is the name-keyed diff's NO-OP — \
            the walk's positional refusal is what catches it (the two \
            readings' boundary is REAL and pinned)")
    , ("the removal is remedied",
        fun _ =>
          assert (verdictOf (diff [migItem1] [migItemRemoved]) [mig12]
            == .remedied)
          "control fired: removals are honestly UNREMEDIABLE — there is \
            no value-map target for gone data")
    , ("the unstable key derives",
        fun _ =>
          assert (match deriveUpcaster "cap" [migKey] migItemKey1 migItemKey2 with
            | .ok _ => true | .error _ => false)
          "control fired: stable identities are ENFORCED — a migrated \
            key is a different entity set (08 §19)")
    , ("the cap-0 field gets a default",
        fun _ =>
          assert (match Ty.migrateDefault (.bounded 0) with
            | some _ => true | none => false)
          "control fired: a cap-0 bounded is UNINHABITED — the honest \
            default is none, and the derivation refuses (noDefault)") ]
    4 42

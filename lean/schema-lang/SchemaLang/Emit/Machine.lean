/-
# SchemaLang.Emit.Machine — the generic machine → Rust fold

Machines models discipline; this file EMITS it. The pipeline machine
was the precedent (its `pipelineArms` now folds through this module's
`matchArms`); this module is the GENERAL fold — any Machines machine
whose states/events
have Rust renderings gets an emitted `step` fn, generated from the
PROVED trans table (the `orderTableStep?_eq_step?` discipline: the data is
pinned to the machine by a theorem before the emitter touches it).

The wildcard-collapse check (one event firing from EVERY concrete state
to the SAME target → a single wildcard arm, the `reset` edge) is
CHECKED against the table here — the generated match cannot claim a
wildcard the table does not justify.
-/

import CodegenCore
import SchemaLang.Emit.GenCtx
import Machines.Core
import SchemaLang.Pipeline
import SchemaLang.OrderMachine

namespace SchemaLang.Emit.Machine

open CodegenCore.Emit.Rust (Item renderModule)

/-- The Rust renderings of a machine's states and events. -/
structure Renderings (S E : Type) where
  state : S → String
  event : E → String

/-- The Rust event enum item: one variant per DISTINCT event in the
    table (the table, not the Label type, is the emission source — the
    theorem ties them). -/
def eventEnumItem {S E : Type} [BEq E] (r : Renderings S E) (eventEnum : String)
    (trans : List (E × S × S)) : CodegenCore.Emit.Rust.Item :=
  Item.enum eventEnum [] ((trans.map (·.1)).eraseDups.map r.event)

/-- The `match` arms, folded from a PROVED trans table: one arm per
    row, EXCEPT — when a wildcard event (e.g. `reset`) sends every
    concrete state to the same target, a single wildcard arm. The
    collapse is CHECKED here: a table that doesn't justify the
    wildcard gets per-row arms (never a wrong generated match). -/
def matchArms {S E : Type} [BEq S] [BEq E] [Inhabited S] (r : Renderings S E)
    (trans : List (E × S × S)) (wildcard : Option E)
    (concrete : List S) : List String :=
  let isWild := fun (e : E) => wildcard.any (fun w => w == e)
  let specific := trans.filter (fun (e, _, _) => !isWild e)
  let wildRows := trans.filter (fun (e, _, _) => isWild e)
  let armOf := fun (e : E) (f t : S) =>
    s!"        ({r.state f}, {r.event e}) => Some({r.state t}),"
  match wildcard with
  | none => specific.map (fun (e, f, t) => armOf e f t)
  | some w =>
    let wildOnly := wildRows.all (fun (e, _, _) => e == w)
    let targets := (wildRows.map fun (_, _, t) => t).eraseDups
    let froms := wildRows.map fun (_, f, _) => f
    let collapseOk := wildOnly &&
      (match targets with
      | [t] => concrete.all (froms.contains ·)
      | _ => false)
    specific.map (fun (e, f, t) => armOf e f t)
      ++ if collapseOk then [s!"        (_, {r.event w}) => Some({r.state (targets.head!)}),"]
         else wildRows.map fun (e, f, t) => armOf e f t

/-- The full generated module: the state/event enums + the `step` fn
    folded from the proved table + the replay assertions (the happy
    path + the terminal rejections — the Rust-side drift guards). -/
def moduleRust {S E : Type} [BEq S] [BEq E] [Inhabited S] (r : Renderings S E)
    (specSource : String)
    (stateEnum eventEnum : String)
    (trans : List (E × S × S)) (wildcard : Option E)
    (concrete : List S)
    (happy : List (E × S × S))
    (rejects : List (String × S × E)) : String :=
  let arms := matchArms r trans wildcard concrete
  let happyAsserts := happy.map fun (e, f, t) =>
    Item.raw s!"    assert_eq!(step({r.state f}, {r.event e}), Some({r.state t}));"
  let rejectAsserts := rejects.map fun (why, f, e) =>
    [ Item.raw s!"    // {why}"
    , Item.raw s!"    assert_eq!(step({r.state f}, {r.event e}), None);" ]
  renderModule
    ([ Item.comment s!"GENERATED from {specSource} — the lifecycle machine."
     , Item.comment "Agreement with the Lean machine is a THEOREM there"
     , Item.comment "(orderTableStep?_eq_step?); do not edit — regenerate."
     , Item.raw ""
     , Item.raw "#[derive(Clone, Copy, Debug, PartialEq, Eq)]"
     , Item.enum stateEnum [] (concrete.map r.state)
     , Item.raw ""
     , Item.raw "#[derive(Clone, Copy, Debug, PartialEq, Eq)]"
     , eventEnumItem r eventEnum trans
     , Item.raw ""
     , Item.raw s!"use {stateEnum}::*;"
     , Item.raw s!"use {eventEnum}::*;"
     , Item.raw ""
     , Item.raw s!"pub fn step(s: {stateEnum}, e: {eventEnum}) -> Option<{stateEnum}> \{"
     , Item.raw "    match (s, e) {"
     ]
    ++ (arms.map Item.raw)
    ++ [ Item.raw "        _ => None,"
       , Item.raw "    }"
       , Item.raw "}"
       , Item.raw ""
       , Item.raw "/// The proved trace: happy path + terminal rejections"
       , Item.raw "/// (the Lean theorems' executable counterparts)."
       , Item.raw "pub fn trace_assertions() {"
       ]
    ++ happyAsserts
    ++ rejectAsserts.flatten
    ++ [ Item.raw "}" ])

/-- The Rust renderings of the order lifecycle. -/
def orderRenderings : Renderings OrderStatus orderMachine.Label where
  state := fun s =>
    match s with
    | .cart => "Cart" | .placed => "Placed" | .shipped => "Shipped"
    | .delivered => "Delivered" | .cancelled => "Cancelled"
    | .stray => "Stray"
  event := fun e =>
    match e with
    | .place => "Place" | .ship => "Ship" | .deliver => "Deliver"
    | .cancel => "Cancel" | .reset => "Reset"

def orderMachineRust : String :=
  moduleRust orderRenderings
    "SchemaLang.OrderMachine (orderTrans + orderTableStep?_eq_step?)"
    "OrderStatus" "OrderEvent"
    orderTrans (some .reset) orderStates
    [ (.place, .cart, .placed)
    , (.ship, .placed, .shipped)
    , (.deliver, .shipped, .delivered) ]
    [ ("a delivered order is terminal (terminal_only_reset)", .delivered, .ship)
    , ("a cancelled order cannot be re-placed (terminal_only_reset)", .cancelled, .place)
    , ("out-of-order firing is rejected (reject_ship_before_place)", .cart, .ship) ]

def orderMachineEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "order-machine"
  style := .doubleSlash
  specSource := "SchemaLang.OrderMachine (orderTrans + orderTableStep?_eq_step?)"
  outputs := ["../../src/order_machine_generated.rs"]
  run _ctx :=
    [{ path := "../../src/order_machine_generated.rs"
       contents := orderMachineRust }]

end SchemaLang.Emit.Machine


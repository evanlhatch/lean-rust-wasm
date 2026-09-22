/-
# SchemaLang.Emit.Machine — the generic machine → Rust fold

Machines models discipline; this file EMITS it. The pipeline machine
was the precedent (its `pipelineArms` now folds through this module's
`matchArms`); this module is the GENERAL fold — any Machines machine
whose states/events
have Rust renderings gets an emitted `step` fn, generated from the
PROVED trans table (the `orderMachineTableStep?_eq_step?` discipline: the
data is pinned to the machine by a theorem before the emitter touches
it).

The wildcard-collapse check (one event firing from EVERY concrete state
to the SAME target → a single wildcard arm, the `reset` edge) is
CHECKED against the table here — the generated match cannot claim a
wildcard the table does not justify.
-/

module

public import CodegenCore
public import SchemaLang.Emit.GenCtx
public import Machines.Core
public import SchemaLang.Pipeline
public import SchemaLang.OrderMachine

@[expose] public section

namespace SchemaLang.Emit.Machine

open CodegenCore.Emit.Rust (Item renderModule)

/-- The Rust renderings of a machine's states and events. -/
structure Renderings (S E : Type) where
  state : S → String
  event : E → String

/-- The Rust event enum item: one variant per DISTINCT event in the
    table (the table, not the Label type, is the emission source — the
    theorem ties them). `eventDecl` is the DECLARATION rendering (the
    variant spelling); it may differ from `r.event`, the match-arm
    use-site spelling (the pipeline qualifies its arms and keeps the
    enum bare — no event glob). -/
def eventEnumItem {S E : Type} [BEq E] (eventDecl : E → String) (eventEnum : String)
    (trans : List (E × S × S)) : CodegenCore.Emit.Rust.Item :=
  Item.enum eventEnum [] ((trans.map (·.1)).eraseDups.map eventDecl)

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
      | [_t] => concrete.all (froms.contains ·)
      | _ => false)
    specific.map (fun (e, f, t) => armOf e f t)
      ++ if collapseOk then [s!"        (_, {r.event w}) => Some({r.state (targets.head!)}),"]
         else wildRows.map fun (e, f, t) => armOf e f t

/-- The full generated module: the state/event enums + the `step` fn
    folded from the proved table + the replay assertions (the happy
    path + the terminal rejections — the Rust-side drift guards).

    The DERIVED core is shared (both machines): the state enum (from
    `concrete`), the event enum (the table's distinct events, via
    `eventDecl`), the `matchArms` fold, the step signature, and the
    happy/reject assertion derivation. The per-machine SHAPE around it
    differs (the pipeline's stage machine carries the structural
    `Failed` variant, qualifies its event arms, and docs the step fn;
    the order machine globs both enums) — so every divergent chunk is
    a PARAMETER. Byte-tie: both call sites reproduce their committed
    goldens exactly (the pipeline consolidation). -/
def moduleRust {S E : Type} [BEq S] [BEq E] [Inhabited S] (r : Renderings S E)
    (eventDecl : E → String)
    (header : List CodegenCore.Emit.Rust.Item)
    (stateEnum eventEnum : String)
    (trans : List (E × S × S)) (wildcard : Option E)
    (concrete : List S)
    (preStep stepDoc inStep : List CodegenCore.Emit.Rust.Item)
    (happy : List (E × S × S))
    (rejects : List (String × S × E))
    (assertsFn : String)
    (assertsDoc extraAsserts : List CodegenCore.Emit.Rust.Item) : String :=
  let arms := matchArms r trans wildcard concrete
  let happyAsserts := happy.map fun (e, f, t) =>
    Item.raw s!"    assert_eq!(step({r.state f}, {r.event e}), Some({r.state t}));"
  let rejectAsserts := rejects.map fun (why, f, e) =>
    [ Item.raw s!"    // {why}"
    , Item.raw s!"    assert_eq!(step({r.state f}, {r.event e}), None);" ]
  renderModule
    (header
    ++ [ Item.raw ""
       , Item.raw "#[derive(Clone, Copy, Debug, PartialEq, Eq)]"
       , Item.enum stateEnum [] (concrete.map r.state)
       , Item.raw ""
       , Item.raw "#[derive(Clone, Copy, Debug, PartialEq, Eq)]"
       , eventEnumItem eventDecl eventEnum trans
       , Item.raw "" ]
    ++ preStep
    ++ stepDoc
    ++ [ Item.raw s!"pub fn step(s: {stateEnum}, e: {eventEnum}) -> Option<{stateEnum}> \{" ]
    ++ inStep
    ++ [ Item.raw "    match (s, e) {" ]
    ++ (arms.map Item.raw)
    ++ [ Item.raw "        _ => None,"
       , Item.raw "    }"
       , Item.raw "}"
       , Item.raw "" ]
    ++ assertsDoc
    ++ [ Item.raw s!"pub fn {assertsFn}() \{" ]
    ++ happyAsserts
    ++ rejectAsserts.flatten
    ++ extraAsserts
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
  moduleRust orderRenderings orderRenderings.event
    [ Item.comment "GENERATED from SchemaLang.OrderMachine (orderMachineTrans + orderMachineTableStep?_eq_step?) — the lifecycle machine."
    , Item.comment "Agreement with the Lean machine is a THEOREM there"
    , Item.comment "(orderMachineTableStep?_eq_step?); do not edit — regenerate." ]
    "OrderStatus" "OrderEvent"
    orderMachineTrans (some .reset) orderMachineStates
    [ Item.raw "use OrderStatus::*;"
    , Item.raw "use OrderEvent::*;"
    , Item.raw "" ]
    []  -- stepDoc: the order machine's step fn is undocumented (as committed)
    []  -- inStep: the use globs sit above the fn (preStep)
    [ (.place, .cart, .placed)
    , (.ship, .placed, .shipped)
    , (.deliver, .shipped, .delivered) ]
    [ ("a delivered order is terminal (terminal_only_reset)", .delivered, .ship)
    , ("a cancelled order cannot be re-placed (terminal_only_reset)", .cancelled, .place)
    , ("out-of-order firing is rejected (reject_ship_before_place)", .cart, .ship) ]
    "trace_assertions"
    [ Item.raw "/// The proved trace: happy path + terminal rejections"
    , Item.raw "/// (the Lean theorems' executable counterparts)." ]
    []  -- extraAsserts: the order trace IS the happy/rejects derivation

/-! ## The emission law (the vortex lane's `vortexLaw` shape) -/

/-- The order-machine emitter's law: the table the Rust folds IS the
    machine's `step?` over the enumerated state space — the
    `orderMachineTableStep?_eq_step?` agreement riding the emitter
    (the `circuitLaw` precedent: ctx-independent, the machine is
    module data and `run` ignores the ctx). -/
def orderMachineLaw : GenCtx → Prop := fun _ =>
  ∀ (e : orderMachine.Label) (s : OrderStatus), s ∈ orderMachineStates →
    orderMachineTableStep? e s = Machines.Machine.step? orderMachine s e

/-- The discharge: the machine!-generated agreement theorem, cited. -/
theorem orderMachineLaw_discharged (ctx : GenCtx) : orderMachineLaw ctx :=
  fun _ _ hs => orderMachineTableStep?_eq_step? _ _ hs

/-- The order-machine emitter's well-formedness note (the
    `Emitter.law` sweep): the law IS populated (`orderMachineLaw`) —
    no defensive arm to justify: the fold is total over the proved
    table, and the bytes are the byte-tie's own. -/
def orderMachineEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "order-machine"
  style := .doubleSlash
  specSource := "SchemaLang.OrderMachine (orderMachineTrans + orderMachineTableStep?_eq_step?)"
  outputs := ["../../generated/rust/order_machine_generated.rs"]
  run _ctx :=
    [{ path := "../../generated/rust/order_machine_generated.rs"
       contents := orderMachineRust }]
  law := some orderMachineLaw

end SchemaLang.Emit.Machine


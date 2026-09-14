/-
# SchemaLang.Emit.Typestate — the order lifecycle's TYPESTATE projection

The flatland row "machine! = enum state column + edge updates ⇒ Rust
typestate": from the SAME proved `orderTrans` table the enum-machine
emitter (`Emit.Machine`) folds, this module emits the typestate
projection — one newtype struct per REACHABLE state (the payload = the
row identity, v1: the u64 order id), transitions as METHODS on the
source state returning the target DIRECTLY.

Ownership: this module is the ONLY writer of
`../../src/order_typestate_generated.rs` (and its golden under
`goldens/typestate/`). It is NOT yet registered in
`SchemaLang.Emit.Registry.emitters` — the registry wiring is the
registry owner's line (`SchemaLang.Emit.Typestate.typestateEmitter`
dropped into `coreEmitters`).

Driving decisions (deliberate exclusions):
- The `reset` edge is NOT emitted. A typestate value is CONSUMED, never
  rewrapped to `Cart` — the whole point of the projection is that
  illegal transitions are UNREPRESENTABLE, and a `fn reset(self) ->
  Cart` would be a rewrap that erases the state's identity (the enum
  projection in `Emit.Machine` keeps reset; this one does not).
  Recovery in v1 = construct a fresh `Cart(id)`.
- `stray` gets NO struct: no `orderTrans` row targets it (the machine
  `Inv`'s non-vacuity — an unreachable state is unrepresentable).
- `delivered`/`cancelled` get NO methods (`terminal_only_reset`): the
  table has no non-reset rows from them, so no `impl` is emitted.
- No `Option`, no panic: every emitted method returns its target
  DIRECTLY, justified per-row by `typestate_edges_legal` (each folded
  row is a `some` step of the proved table).
-/

import CodegenCore
import SchemaLang.Item
import SchemaLang.OrderMachine

namespace SchemaLang.Emit.Typestate

open CodegenCore.Emit.Rust (renderModule)

-- `Item` below is ALWAYS `CodegenCore.Emit.Rust.Item` — inside
-- `namespace SchemaLang` the bare name would resolve to `SchemaLang.Item`
-- (the schema descriptor), so the AST is spelled out (Machine.lean pins
-- it via expected types; explicit beats implicit here).

/-! ## The pinned fold (the data is the machine's, by theorem) -/

/-- The Rust struct name for a state's typestate. -/
def stateStruct : OrderStatus → String
  | .cart => "Cart" | .placed => "Placed" | .shipped => "Shipped"
  | .delivered => "Delivered" | .cancelled => "Cancelled" | .stray => "Stray"

/-- The Rust method name for a transition label (camelCase — the
    typestate reads as verbs on the state). -/
def eventMethod : orderMachine.Label → String
  | .place => "place" | .ship => "ship" | .deliver => "deliver"
  | .cancel => "cancel" | .reset => "reset"

/-- The edges the typestate folds: every non-`reset` row of `orderTrans`
    — the SAME table the theorem `orderTableStep?_eq_step?` proves IS
    `orderMachine.step?`. No hand copy: the emitter's rows cannot drift
    from the machine's (a `reset` row is filtered, never re-typed). -/
def typestateEdges : List (orderMachine.Label × OrderStatus × OrderStatus) :=
  orderTrans.filter (fun (e, _, _) => !(e == .reset))

/-- The emitted states: `cart` (the initial state) plus every folded row
    target, table order, deduped. `stray` is a target of NO row, so it
    cannot appear — see `typestate_states_reachable`. -/
def typestateStates : List OrderStatus :=
  (.cart :: (typestateEdges.map fun (_, _, t) => t)).eraseDups

/-- LEGALITY PIN: every folded row is a `some` step of the PROVED table
    (`orderTableStep?`, pinned to the machine by
    `orderTableStep?_eq_step?`) — no emitted method can represent an
    illegal firing, which is why the generated methods return their
    target directly (no Option, no panic). -/
theorem typestate_edges_legal :
    (typestateEdges.map fun (e, f, _) => orderTableStep? e f).all
      Option.isSome = true := rfl

/-- REACHABILITY PIN: every emitted struct's state is `cart` or a row
    TARGET of the proved table — so `stray` (the state no transition
    produces, the `Inv`'s non-vacuity control) gets no struct, and the
    emitted structs are exactly the machine's reachable set. -/
theorem typestate_states_reachable :
    typestateStates.all
      (fun s => (s == .cart) || orderTrans.any (fun (_, _, t) => t == s))
      = true := rfl

/-! ## The Rust AST -/

/-- One typestate struct: `pub struct Cart(pub u64);` — the payload is
    the row identity (v1: the u64 order id). -/
def structItem (s : OrderStatus) : CodegenCore.Emit.Rust.Item :=
  .newtype (stateStruct s) "u64" ["Clone", "Copy", "Debug", "PartialEq", "Eq"]

/-- The methods on one source state: one per folded row FROM it, in
    table order — `pub fn place(self) -> Placed { Placed(self.0) }`.
    Direct return: the row is legal by construction
    (`typestate_edges_legal`). -/
def methodItems (ms : List (orderMachine.Label × OrderStatus)) :
    List CodegenCore.Emit.Rust.Item :=
  ms.flatMap fun (e, t) =>
    [ .raw s!"    pub fn {eventMethod e}(self) -> {stateStruct t} \{"
    , .raw s!"        {stateStruct t}(self.0)"
    , .raw "    }" ]

/-- The inherent impl for one source state — omitted ENTIRELY for the
    terminal states (`delivered`/`cancelled`): the proved table has no
    non-reset rows from them (`terminal_only_reset`), so the typestate
    gives them no methods — an illegal transition from a terminal state
    is unrepresentable, not `None`. -/
def implItems (s : OrderStatus) : List CodegenCore.Emit.Rust.Item :=
  let ms := typestateEdges.filter fun (_, f, _) => f == s
  match ms with
  | [] => []
  | _ =>
    [ .raw s!"impl {stateStruct s} \{" ]
    ++ methodItems (ms.map fun (e, _, t) => (e, t))
    ++ [ .raw "}" ]

/-- The `#[cfg(test)]` module: the happy-path chain CONSTRUCTS each
    reachable state and consumes it into `Delivered` — compile-time
    legality IS the test (a broken chain is a type error, not a runtime
    `None`). -/
def testModule : CodegenCore.Emit.Rust.Item :=
  .mod_ "tests"
    [ .use_ "super::*"
    , .raw "#[test]"
    , .fn "fn happy_path_reaches_delivered()"
        "assert_eq!(Cart(7u64).place().ship().deliver().0, 7u64);"
    , .raw "#[test]"
    , .fn "fn cancel_paths_are_legal()"
        "assert_eq!(Cart(7u64).cancel().0, 7u64);"
    , .raw "#[test]"
    , .fn "fn cancel_after_place_is_legal()"
        "assert_eq!(Placed(7u64).cancel().0, 7u64);" ]

/-- The full module's items: the pinning comments, one struct per
    reachable state, one impl per state WITH outgoing rows, the test
    module. Deterministic (table-order folds only — byte-tie ready). -/
def typestateItems : List CodegenCore.Emit.Rust.Item :=
  [ .comment "GENERATED from SchemaLang.OrderMachine — the lifecycle's TYPESTATE"
  , .comment "projection. Each struct = one REACHABLE state (payload = the row id,"
  , .comment "v1: u64); each method = one non-`reset` row of `orderTrans` — the SAME"
  , .comment "table the theorem `orderTableStep?_eq_step?` pins to the machine (the"
  , .comment "emitter folds the table, never a hand copy; Lean pins:"
  , .comment "`typestate_edges_legal`, `typestate_states_reachable`)."
  , .comment ""
  , .comment "Deliberate exclusions:"
  , .comment "- the `reset` edge is NOT emitted: a typestate value is consumed,"
  , .comment "  never rewrapped — recovery = a fresh Cart(id)."
  , .comment "- `stray` gets no struct: no orderTrans row targets it (Inv non-vacuity)."
  , .comment "- `delivered`/`cancelled` get no methods (`terminal_only_reset`): the"
  , .comment "  illegal transition is unrepresentable, not None — no Option, no panic."
  , .comment "Do not edit — regenerate."
  , .raw "" ]
  ++ typestateStates.map structItem
  ++ ((typestateStates.flatMap fun s => .raw "" :: implItems s).drop 1)
  ++ [ testModule ]

def typestateRust : String := renderModule typestateItems

/-! ## The emitter -/

/-- The typestate emitter: the machine's states as consuming newtypes,
    its non-reset rows as methods. Same discipline as
    `Emit.Machine.orderMachineEmitter` — pure over the proved table. -/
def typestateEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "typestate"
  style := .doubleSlash
  specSource := "SchemaLang.OrderMachine (orderTrans + orderTableStep?_eq_step?)"
  outputs := ["../../src/order_typestate_generated.rs"]
  run _ :=
    [{ path := "../../src/order_typestate_generated.rs"
       contents := typestateRust }]

end SchemaLang.Emit.Typestate

/-
# SchemaLang.Emit.Typestate — the order lifecycle's TYPESTATE projection

The flatland row "machine! = enum state column + edge updates ⇒ Rust
typestate": from the SAME proved `orderMachineTrans` table the
enum-machine emitter (`Emit.Machine`) folds, this module emits the
typestate
projection — one newtype struct per REACHABLE state (the payload = the
row identity, v1: the u64 order id), transitions as METHODS on the
source state returning the target DIRECTLY.

Ownership: this module is the ONLY writer of
`../../src/order_typestate_generated.rs` (and its golden under
`goldens/typestate/`); `typestateEmitter` is registered in
`SchemaLang.Emit.Registry.emitters`.

The fold is NOT hand-rolled: it is the generic
`SchemaLang.EntityMachine.hookItems` typestate projection instantiated
at `orderMachine` (this module supplies the naming maps + the filtered
table; the preset supplies struct/method/impl item shapes, the pinning
comments, the state fold). The per-order theorems
`typestate_edges_legal`/`typestate_states_reachable` are the
instantiation's evidence — the same statements the generic
`hookEdges_legal`/`hookStates_reachable` lemmas govern (layering audit
#3: the duplicate hand-rolled fold deleted).

Driving decisions (deliberate exclusions):
- The `reset` edge is NOT emitted. A typestate value is CONSUMED, never
  rewrapped to `Cart` — the whole point of the projection is that
  illegal transitions are UNREPRESENTABLE, and a `fn reset(self) ->
  Cart` would be a rewrap that erases the state's identity (the enum
  projection in `Emit.Machine` keeps reset; this one does not).
  Recovery in v1 = construct a fresh `Cart(id)`.
- `stray` gets NO struct: no `orderMachineTrans` row targets it (the
  machine `Inv`'s non-vacuity — an unreachable state is
  unrepresentable).
- `delivered`/`cancelled` get NO methods (`terminal_only_reset`): the
  table has no non-reset rows from them, so no `impl` is emitted.
- No `Option`, no panic: every emitted method returns its target
  DIRECTLY, justified per-row by `typestate_edges_legal` (each folded
  row is a `some` step of the proved table).
-/

module

public import CodegenCore
public import SchemaLang.EntityMachine
public import SchemaLang.Item
public import SchemaLang.Emit.GenCtx
public import SchemaLang.OrderMachine

@[expose] public section

namespace SchemaLang.Emit.Typestate

open CodegenCore.Emit.Rust (renderModule)

-- `Item` below is ALWAYS `CodegenCore.Emit.Rust.Item` — inside
-- `namespace SchemaLang` the bare name would resolve to `SchemaLang.Item`
-- (the schema descriptor), so the AST is spelled out (Machine.lean pins
-- it via expected types; explicit beats implicit here).

/-! ## The pinned fold (the data is the machine's, by theorem) —
    the GENERIC hook's instantiation -/

/-- The Rust struct name for a state's typestate. -/
def stateStruct : OrderStatus → String
  | .cart => "Cart" | .placed => "Placed" | .shipped => "Shipped"
  | .delivered => "Delivered" | .cancelled => "Cancelled" | .stray => "Stray"

/-- The Rust method name for a transition label (camelCase — the
    typestate reads as verbs on the state). -/
def eventMethod : orderMachine.Label → String
  | .place => "place" | .ship => "ship" | .deliver => "deliver"
  | .cancel => "cancel" | .reset => "reset"

/-- The edges the typestate folds: every non-`reset` row of
    `orderMachineTrans` — the SAME table the theorem
    `orderMachineTableStep?_eq_step?` proves IS `orderMachine.step?`.
    No hand copy: the emitter's rows cannot drift from the machine's
    (a `reset` row is filtered, never re-typed). -/
def typestateEdges : List (orderMachine.Label × OrderStatus × OrderStatus) :=
  EntityMachine.hookEdges orderMachineTrans (some .reset)

/-- The emitted states: `cart` (the initial state) plus every folded row
    target, table order, deduped. `stray` is a target of NO row, so it
    cannot appear — see `typestate_states_reachable`. -/
def typestateStates : List OrderStatus :=
  EntityMachine.hookStates .cart typestateEdges

/-- LEGALITY PIN: every folded row is a `some` step of the PROVED table
    (`orderMachineTableStep?`, pinned to the machine by
    `orderMachineTableStep?_eq_step?`) — no emitted method can represent
    an illegal firing, which is why the generated methods return their
    target directly (no Option, no panic). -/
theorem typestate_edges_legal :
    (typestateEdges.map fun (e, f, _) => orderMachineTableStep? e f).all
      Option.isSome = true := rfl

/-- REACHABILITY PIN: every emitted struct's state is `cart` or a row
    TARGET of the proved table — so `stray` (the state no transition
    produces, the `Inv`'s non-vacuity control) gets no struct, and the
    emitted structs are exactly the machine's reachable set. -/
theorem typestate_states_reachable :
    typestateStates.all
      (fun s => (s == .cart) || orderMachineTrans.any (fun (_, _, t) => t == s))
      = true := rfl

/-! ## The hook instance + the Rust AST -/

/-- The GENERIC hook instance: the hand-written naming maps (the Rust
    struct/method names, per state/label) + the folded table ride
    `EntityMachine.TypestateHook` — the item shapes, the comment block
    and the state fold are the preset's (`hookItems`), not re-rolled
    here (the layering audit's unification). -/
def orderHook : EntityMachine.TypestateHook orderMachine :=
  EntityMachine.TypestateHook.mk (some .reset) typestateEdges
    stateStruct eventMethod

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

/-- The full module's items: the GENERIC hook's items (the pinning
    comments, one struct per reachable state, one impl per state WITH
    outgoing rows) + the test module. Deterministic (table-order folds
    only — byte-tie ready). The comment block is the preset's text —
    a DELIBERATE byte re-pin vs the deleted hand-rolled fold's
    comments (content identical, prose generalized). -/
def typestateItems : List CodegenCore.Emit.Rust.Item :=
  EntityMachine.hookItems orderHook .cart
    "SchemaLang.OrderMachine (orderMachineTrans + orderMachineTableStep?_eq_step?)"
  ++ [ testModule ]

def typestateRust : String := renderModule typestateItems

/-! ## The emitter -/

/-! ## The emission law (the vortex lane's `vortexLaw` shape) -/

/-- The typestate emitter's law: the module's own legality + reachability
    pins, bundled as one `GenCtx → Prop` (the `vortexLaw` shape — both
    theorems ctx-independent, the machine is module data). Content: no
    emitted method can represent an illegal firing, and the emitted
    structs are exactly the reachable states. -/
def typestateLaw : GenCtx → Prop := fun _ =>
  (typestateEdges.map fun (e, f, _) => orderMachineTableStep? e f).all
      Option.isSome = true
  ∧ typestateStates.all
      (fun s => (s == .cart) || orderMachineTrans.any (fun (_, _, t) => t == s))
      = true

/-- The discharge: the module's own pins, one citation per conjunct. -/
theorem typestateLaw_discharged (ctx : GenCtx) : typestateLaw ctx :=
  ⟨typestate_edges_legal, typestate_states_reachable⟩

/-- The typestate emitter: the machine's states as consuming newtypes,
    its non-reset rows as methods. Same discipline as
    `Emit.Machine.orderMachineEmitter` — pure over the proved table.
    W7.9 `Emitter.law` sweep: `law` POPULATED (`typestateLaw`),
    discharged by `typestateLaw_discharged`. -/
def typestateEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "typestate"
  style := .doubleSlash
  specSource := "SchemaLang.OrderMachine (orderMachineTrans + orderMachineTableStep?_eq_step?)"
  outputs := ["../../src/order_typestate_generated.rs"]
  run _ctx :=
    [{ path := "../../src/order_typestate_generated.rs"
       contents := typestateRust }]
  law := some typestateLaw

end SchemaLang.Emit.Typestate

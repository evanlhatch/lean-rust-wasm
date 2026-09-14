//! The lifecycle TYPESTATE, compiled — the machine! preset's Rust
//! projection. `src/order_typestate_generated.rs` folds the SAME proved
//! table as the enum+step module (`orderTableStep?_eq_step?`): legal
//! transitions are direct returns (illegal = unrepresentable — no
//! Option, no panic); `stray`/terminals get no constructors/methods
//! (`Inv` non-vacuity / `terminal_only_reset`).

#[path = "../../../src/order_typestate_generated.rs"]
mod order_typestate;

use order_typestate::*;

#[test]
fn typestate_happy_chain_compiles_and_runs() {
    // The compile IS the check: Cart -> Placed -> Shipped -> Delivered
    // with no Option, no panic — the illegal transitions cannot even
    // be written. The generated test module replays the same chain.
    let placed = Cart(7).place();
    let shipped = placed.ship();
    let delivered = shipped.deliver();
    assert_eq!(delivered.0, 7);
}

#[test]
fn typestate_cancel_paths() {
    let cancelled_from_cart = Cart(1).cancel();
    assert_eq!(cancelled_from_cart.0, 1);
    let cancelled_from_placed = Cart(2).place().cancel();
    assert_eq!(cancelled_from_placed.0, 2);
}

#[test]
fn typestate_generated_tests_self_check() {
    order_typestate::tests::happy_path_reaches_delivered();
    order_typestate::tests::cancel_paths_are_legal();
    order_typestate::tests::cancel_after_place_is_legal();
}

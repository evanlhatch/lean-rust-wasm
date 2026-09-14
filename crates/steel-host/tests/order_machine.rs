//! The order lifecycle, REPLAYED — the host side of the machine tie.
//!
//! `src/order_machine_generated.rs` is GENERATED from
//! `SchemaLang.OrderMachine` (the proved machine: `lifecycle_rank_advances`,
//! `terminal_only_reset`, `orderTableStep?_eq_step?` — Lean theorems).
//! This test replays the lifecycle the spec proves, against the code the
//! spec generates: place → ship → deliver, the cancel path, and the
//! terminal rejections. If the generated step drifts from the proved
//! table, this fails (the trace is the theorem's executable shadow).

#[path = "../../../src/order_machine_generated.rs"]
mod order_machine;

use order_machine::{step, OrderEvent::*, OrderStatus::*};

#[test]
fn lifecycle_happy_path_replayed() {
    // Lean: lifecycle_happy_path (proved by rfl)
    assert_eq!(step(Cart, Place), Some(Placed));
    assert_eq!(step(Placed, Ship), Some(Shipped));
    assert_eq!(step(Shipped, Deliver), Some(Delivered));
}

#[test]
fn lifecycle_cancel_path_replayed() {
    // Lean: cancel_from_placed (proved by rfl)
    assert_eq!(step(Cart, Place), Some(Placed));
    assert_eq!(step(Placed, Cancel), Some(Cancelled));
    // cancel straight from the cart is legal too
    assert_eq!(step(Cart, Cancel), Some(Cancelled));
}

#[test]
fn lifecycle_out_of_order_rejected() {
    // Lean: reject_ship_before_place / reject_double_place (proved by rfl)
    assert_eq!(step(Cart, Ship), None);
    assert_eq!(step(Cart, Place), Some(Placed));
    assert_eq!(step(Placed, Place), None);
}

#[test]
fn lifecycle_terminal_closed() {
    // Lean: terminal_only_reset (proved) — delivered/cancelled reject
    // every non-reset event; only Reset reopens (to Cart).
    for e in [Place, Ship, Deliver, Cancel] {
        assert_eq!(step(Delivered, e), None, "delivered must reject {e:?}");
        assert_eq!(step(Cancelled, e), None, "cancelled must reject {e:?}");
    }
    assert_eq!(step(Delivered, Reset), Some(Cart));
    assert_eq!(step(Cancelled, Reset), Some(Cart));
}

#[test]
fn trace_assertions_self_check() {
    // The generated module's own replay battery (emitted from the same
    // proved table). If this ever fails, the GENERATOR drifted — not
    // just this test's expectations.
    order_machine::trace_assertions();
}

// GENERATED from SchemaLang.OrderMachine (orderTrans + orderTableStep?_eq_step?) — the lifecycle machine.
// Agreement with the Lean machine is a THEOREM there
// (orderTableStep?_eq_step?); do not edit — regenerate.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]

pub enum OrderStatus {
  Cart,
  Placed,
  Shipped,
  Delivered,
  Cancelled,
  Stray,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]

pub enum OrderEvent {
  Place,
  Ship,
  Deliver,
  Cancel,
  Reset,
}

use OrderStatus::*;
use OrderEvent::*;

pub fn step(s: OrderStatus, e: OrderEvent) -> Option<OrderStatus> {
    match (s, e) {
        (Cart, Place) => Some(Placed),
        (Placed, Ship) => Some(Shipped),
        (Shipped, Deliver) => Some(Delivered),
        (Cart, Cancel) => Some(Cancelled),
        (Placed, Cancel) => Some(Cancelled),
        (_, Reset) => Some(Cart),
        _ => None,
    }
}

/// The proved trace: happy path + terminal rejections
/// (the Lean theorems' executable counterparts).
pub fn trace_assertions() {
    assert_eq!(step(Cart, Place), Some(Placed));
    assert_eq!(step(Placed, Ship), Some(Shipped));
    assert_eq!(step(Shipped, Deliver), Some(Delivered));
    // a delivered order is terminal (terminal_only_reset)
    assert_eq!(step(Delivered, Ship), None);
    // a cancelled order cannot be re-placed (terminal_only_reset)
    assert_eq!(step(Cancelled, Place), None);
    // out-of-order firing is rejected (reject_ship_before_place)
    assert_eq!(step(Cart, Ship), None);
}

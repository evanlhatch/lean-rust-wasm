//! The Lean-witness replays — the host side of the four ties, ONE binary.
//!
//! Each lane replays Lean's witness values against the emitter's Rust
//! projection (the theorem's executable shadow: if the generated code
//! drifts from the proved spec, these fail). The lanes were four
//! hand-rolled suites; the replays share the shape, so they share the
//! binary. The ASSERTIONS are byte-for-byte the suites' own — only the
//! boilerplate merged. Per-lane provenance (which emitter/theorem each
//! `*_generated.rs` folds) lives in the lane modules below.
//!
//! The lanes live in per-lane inner modules because two of them bind
//! the same BARE NAMES to different kinds (`Cart`/`Placed`/... are
//! `OrderStatus` variants in the machine lane and tuple-struct
//! constructors in the typestate lane) — the modules keep every
//! assertion's text verbatim, collision-free.
//!
//! Ownership: crates/guestlang-host/tests/replay.rs (the witness-replay
//! lanes). Additive only; src/** untouched (included by path, compiled
//! as-is).

// The GENERATED modules, included by path (the suites' original anchor:
// tests/ + three ups = the repo-root src/). The per-lane inner modules
// below import from `super` — keeping the lane bodies verbatim.

#[path = "../../../src/circuit_generated.rs"]
mod circuit_generated;

#[path = "../../../src/order_machine_generated.rs"]
mod order_machine;

#[path = "../../../src/order_typestate_generated.rs"]
mod order_typestate;

#[path = "../../../src/updates_generated.rs"]
mod updates;

// The generated `updates` module's `crate::schema_generated::User` —
// resolved at THIS binary's root (the original updates.rs's bottom-of-file
// use, relocated with the merge).
use lean_rust_wasm::schema_generated;

// ── lane: the certified dbsp circuit ────────────────────────────────

mod circuit_lane {
    //! `src/circuit_generated.rs`, GENERATED from `SchemaLang.Emit.Circuit`
    //! (the fold of `orderTotalCkt`; the incrementalization's certificate is
    //! the Lean theorem `Dbsp.incrementalize_ok`, shape-pinned by
    //! `#check_cert` in the emitter module). Replays the batch circuit's
    //! running total, and the incremental circuit fed the input's DELTAS
    //! emitting the batch output's differences.

    use super::circuit_generated::*;

    /// The constant-1 stream (the integrated domain: states).
    fn ones(_i: usize) -> Val {
        Val::I(1)
    }

    /// Its deltas: 1 at tick 0, 0 after (Lean: `Dbsp.D ones`).
    fn ones_delta(i: usize) -> Val {
        Val::I(if i == 0 { 1 } else { 0 })
    }

    #[test]
    fn batch_circuit_computes_running_total() {
        // Lean witness: orderTotalCkt_denote_tick3 (native_decide) —
        // denote over the constant-1 stream at tick n is 2(n+1).
        let c = order_total_circuit();
        assert_eq!(eval(&c, &ones, 0), Val::I(2));
        assert_eq!(eval(&c, &ones, 3), Val::I(8));
        assert_eq!(eval(&c, &ones, 5), Val::I(12));
    }

    #[test]
    fn incremental_circuit_agrees_on_deltas() {
        // `Dbsp.incrementalize_ok`: denote (incrementalize c) = incremental (denote c)
        // = D . denote c . I — fed the deltas of `ones`, the incremental
        // circuit emits the batch output's differences: a constant 2.
        // Lean witness: orderTotalIncr_denote_tick3.
        let c = order_total_incremental();
        for n in 0..6 {
            assert_eq!(eval(&c, &ones_delta, n), Val::I(2));
        }
    }

    #[test]
    fn derivative_inverts_integral() {
        // D . I = id on the constant-1 stream (Lean: Dbsp.derivative_integral).
        let c = Node::Seq(Box::new(Node::Integral), Box::new(Node::Derivative));
        for n in 0..6 {
            assert_eq!(eval(&c, &ones, n), Val::I(1));
        }
    }

    #[test]
    fn delay_shifts_with_zero_at_tick_zero() {
        // Lean: Dbsp.delay — z^-1 with the group's zero at tick 0.
        let c = Node::Delay;
        assert_eq!(eval(&c, &ones, 0), Val::I(0));
        assert_eq!(eval(&c, &ones, 3), Val::I(1));
    }

    #[test]
    fn par_and_feedback_compute_the_delayed_loop() {
        // body = par(I, z^-1) over s ⊗ z^-1(alpha): the loop
        // alpha(n) = (I s n, z^-1(z^-1(alpha)) n) — the second component is
        // alpha(n-2) (the PAIR, delayed), with the pair-group zero at ticks
        // < 2: alpha(1) = (2, 0), alpha(3) = (4, alpha(1)) = (4, (2, 0)).
        // Exercises the memoized `Dbsp.fix` shadow (causality: tick n reads
        // alpha only at ticks < n).
        let c = Node::Feedback(Box::new(Node::Par(
            Box::new(Node::Integral),
            Box::new(Node::Delay),
        )));
        assert_eq!(
            eval(&c, &ones, 1),
            Val::P(Box::new(Val::I(2)), Box::new(Val::I(0)))
        );
        assert_eq!(
            eval(&c, &ones, 3),
            Val::P(
                Box::new(Val::I(4)),
                Box::new(Val::P(Box::new(Val::I(2)), Box::new(Val::I(0))))
            )
        );
    }
}

// ── lane: the order lifecycle (machine) ─────────────────────────────

mod machine_lane {
    //! `src/order_machine_generated.rs`, GENERATED from
    //! `SchemaLang.OrderMachine` (the proved machine: `lifecycle_rank_advances`,
    //! `terminal_only_reset`, `orderTableStep?_eq_step?` — Lean theorems).
    //! Replays place → ship → deliver, the cancel path, the terminal
    //! rejections.

    use super::order_machine::{step, OrderEvent::*, OrderStatus::*};
    use super::order_machine;

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
}

// ── lane: the order lifecycle (typestate) ───────────────────────────

mod typestate_lane {
    //! `src/order_typestate_generated.rs` folds the SAME proved table as
    //! the enum+step module (`orderTableStep?_eq_step?`): legal transitions
    //! are direct returns (illegal = unrepresentable — no Option, no
    //! panic); `stray`/terminals get no constructors/methods (`Inv`
    //! non-vacuity / `terminal_only_reset`).

    use super::order_typestate::*;

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
        super::order_typestate::tests::happy_path_reaches_delivered();
        super::order_typestate::tests::cancel_paths_are_legal();
        super::order_typestate::tests::cancel_after_place_is_legal();
    }
}

// ── lane: the update semantics ──────────────────────────────────────

mod updates_lane {
    //! `src/updates_generated.rs`, GENERATED from the `schema_update`
    //! registry (the proved `UpdateItem.applyRow` discipline: guard AND
    //! value read the ORIGINAL row; a refused row passes through
    //! untouched; the tick re-runs updates in registration order).

    use super::updates::*;

    fn demo_users() -> Vec<schema_generated::User> {
        vec![
            schema_generated::User { id: 150, name: "long-name".into(), email: String::new(), tags: vec![] },
            schema_generated::User { id: 50, name: "ab".into(), email: String::new(), tags: vec![] },
        ]
    }

    #[test]
    fn update_guard_reads_the_original_row() {
        // reset_id: guard `id > 100` — 150 fires, 50 is refused.
        // Lean pin: apply on ids [150, 50] → [0, 50].
        let mut rows = demo_users();
        apply_reset_id(&mut rows);
        assert_eq!(rows[0].id, 0, "the guarded row fires");
        assert_eq!(rows[1].id, 50, "the refused row passes through");
    }

    #[test]
    fn update_value_reads_the_original_row() {
        // self_bump: `id := id` — the value is the ORIGINAL id, and the
        // echo of a refused... the self-read update is IDEMPOTENT here
        // (the value expr is the identity) — the pin: run twice, same.
        let mut rows = demo_users();
        apply_self_bump(&mut rows);
        let after1: Vec<u64> = rows.iter().map(|r| r.id).collect();
        apply_self_bump(&mut rows);
        let after2: Vec<u64> = rows.iter().map(|r| r.id).collect();
        assert_eq!(after1, after2, "the self-read update sees the original row");
    }

    #[test]
    fn update_string_channel_replayed() {
        // echo_email: guard `strlen(name) > 3`, set `email := name`.
        let mut rows = demo_users();
        apply_echo_email(&mut rows);
        assert_eq!(rows[0].email, "long-name", "the long name echoes");
        assert_eq!(rows[1].email, "", "the short name is refused");
    }

    #[test]
    fn tick_replays_registration_order() {
        let mut rows = demo_users();
        tick_user(&mut rows);
        // reset_id fired (150 → 0), echo_email fired (email := name),
        // self_bump no-op'd.
        assert_eq!(rows[0].id, 0);
        assert_eq!(rows[0].email, "long-name");
        assert_eq!(rows[1].id, 50);
        assert_eq!(rows[1].email, "");
    }

    // bring the schema type into scope for the demo constructor
    use crate::schema_generated;
}

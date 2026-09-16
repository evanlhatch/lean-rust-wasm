//! The certified dbsp circuit, REPLAYED — the host side of the circuit tie.
//!
//! `src/circuit_generated.rs` is GENERATED from `SchemaLang.Emit.Circuit`
//! (the fold of `orderTotalCkt`; the incrementalization's certificate is
//! the Lean theorem `Dbsp.incrementalize_ok`, shape-pinned by
//! `#check_cert` in the emitter module). These tests replay the
//! Lean-side witnesses: the batch circuit's running total, and the
//! incremental circuit fed the input's DELTAS emitting the batch
//! output's differences (the certificate's executable shadow).

#[path = "../../../src/circuit_generated.rs"]
mod circuit_generated;

use circuit_generated::*;

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

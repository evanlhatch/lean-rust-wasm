//! splicer-mw — the FIRST REAL middleware: a tracing/counting
//! INTERPOSER between the host and the demo component.
//!
//! The splice-smoke gate proved interposition works MECHANICALLY (a
//! passthrough splicer); this component is the real thing: every
//! wrapped export (a) increments an in-wasm counter (the middleware's
//! own state — a static), (b) calls the INNER implementation (this
//! component's IMPORTS — the wac composition wires the demo
//! component's exports to them), (c) returns the inner's result
//! unchanged.
//!
//! Phase 2 — the STREAM leg: watch-counts is wrapped as a ZERO-COPY
//! HANDLE PASS-THROUGH: the inner's readable half IS our result. A
//! naive pump (write into a fresh pair before returning) deadlocks —
//! a WASI 0.3 stream write blocks until the consumer attaches, and
//! the consumer attaches only after the call returns (the demo's own
//! module avoids this with the yield-dance; wit-bindgen's async fn
//! cannot yield mid-body). Consequence: no item-level counting on
//! streams — the calls counter is the interposition evidence.
//!
//! Ownership: the splicer-middleware lane. Deliberate exclusions:
//! only the scalar subset (double, is-big) plus watch-counts is
//! wrapped — the remaining string/option/stream exports pass through
//! un-wrapped (the seam contract's spans stay the spec's data; this
//! layer is the COUNT layer between). Driving decision: zero hand-WAT
//! — wit-bindgen does the wrapping on both sides.

wit_bindgen::generate!({
    path: "splicer-mw.wit",
    world: "mw",
});

use std::sync::atomic::{AtomicU64, Ordering};

/// The middleware's own state — the count of wrapped calls so far.
/// Relaxed is sufficient: the count is observability, not
/// synchronization, and the component runs single-threaded.
static CALLS: AtomicU64 = AtomicU64::new(0);

struct Middleware;

impl Guest for Middleware {
    fn double(x: u64) -> u64 {
        CALLS.fetch_add(1, Ordering::Relaxed);
        // the INNER: the composition wires this import to
        // guestlang:demo's double
        double(x)
    }

    fn is_big(x: u64) -> bool {
        CALLS.fetch_add(1, Ordering::Relaxed);
        // the INNER: the composition wires this import to
        // guestlang:demo's is-big
        is_big(x)
    }

    /// The STREAM interposer: PASS-THROUGH HANDLE. The naive pump
    /// (write_one into a fresh pair before returning) DEADLOCKS: a
    /// WASI 0.3 stream write blocks until the consumer attaches, and
    /// the consumer attaches only after this call returns — the guest
    /// awaits the reader, the host awaits the call. The demo's own
    /// module avoids this with the yield-dance (the stash + the
    /// callback = the write site); wit-bindgen's async fn cannot yield
    /// mid-body, so the honest v1 = zero-copy handle interposition:
    /// the inner's readable half IS our result. Consequence: no
    /// item-level counting on streams (the items flow host-to-host
    /// past us) — the calls counter still counts; the item-counting =
    /// the yield-dance follow-up.
    async fn watch_counts(n: u64) -> wit_bindgen::rt::async_support::StreamReader<u64> {
        CALLS.fetch_add(1, Ordering::Relaxed);
        watch_counts(n).await
    }

    fn calls() -> u64 {
        CALLS.load(Ordering::Relaxed)
    }

}

export!(Middleware);

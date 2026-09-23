//! The FIRST REAL MIDDLEWARE (Track 2d): the composed component
//! (wac wires the demo component's exports to the middleware's
//! imports) runs double THROUGH the interposer — the middleware's
//! in-wasm counter ticks, the inner's answer comes back unchanged,
//! and the host's spans (the spec's manifest — observability_generated.rs)
//! still fire on the wrapped calls.
//!
//! The seam: the SPANS = the spec's data (fast-observe, the host side);
//! the COUNTER = the middleware's own in-wasm state (`calls`) — the
//! count layer BETWEEN (notes/seam-contract.md).

mod common;

use common::drain::DrainTask;
use common::{canonicalize_or_skip, instantiate, spliced_mw_path};


use std::sync::{Arc, Mutex};

use guestlang_host::{CapabilitySet, HostEngine};
use wasmtime::component::Val;

fn composed_path() -> std::path::PathBuf {
    spliced_mw_path()
}

#[tokio::test]
async fn the_middleware_interposes_the_inner() -> Result<(), Box<dyn std::error::Error>> {
    let Some(path) = canonicalize_or_skip(
        &composed_path(),
        &format!("skipping: run `just splicer-mw` to build {:?}", composed_path()),
    ) else {
        return Ok(());
    };
    let engine = HostEngine::new()?;
    let component = engine.load_component(&path)?;
    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    // counter starts at zero (the middleware's own state, read through
    // its `calls` export)
    let r = rt.call("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(0)),
        "counter must start at 0: {:?}",
        r[0]
    );

    // the INNER ran through the INTERPOSER: wrapped double(21) = 42
    let r = rt.call("double", &[Val::U64(21)]).await?;
    assert!(
        matches!(&r[0], Val::U64(42)),
        "wrapped double broke: {:?}",
        r[0]
    );

    // the counter ticked (the count layer between)
    let r = rt.call("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(1)),
        "counter after 1 call: {:?}",
        r[0]
    );

    // twice → 2
    rt.call("double", &[Val::U64(3)]).await?;
    let r = rt.call("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(2)),
        "counter after 2 calls: {:?}",
        r[0]
    );

    // the SECOND wrapper also counts: is-big routes through the
    // interposer too (answer unchanged — whatever the inner returns)
    let r = rt.call("is-big", &[Val::U64(5)]).await?;
    assert!(
        matches!(r[0], Val::Bool(_)),
        "wrapped is-big broke: {:?}",
        r[0]
    );
    let r = rt.call("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(3)),
        "is-big must count too: {:?}",
        r[0]
    );
    Ok(())
}

/// THE TRACING TIE: the host's spans stay the SPEC's manifest even on
/// the middleware-wrapped path — `double` is a registered export, the
/// call records a span with the spec's delivery tag; `calls` is NOT in
/// the spec's table (the middleware's own export — the host cannot
/// invent a span for it; the counter IS that export's observability).
#[tokio::test]
async fn the_spec_spans_govern_the_wrapped_calls() -> Result<(), Box<dyn std::error::Error>> {
    let Some(path) = canonicalize_or_skip(
        &composed_path(),
        &format!("skipping: run `just splicer-mw` to build {:?}", composed_path()),
    ) else {
        return Ok(());
    };
    let engine = HostEngine::new()?;
    let component = engine.load_component(&path)?;
    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    // the spec's manifest covers the wrapped surface
    for name in ["double", "is-big"] {
        assert!(
            guestlang_host::observability_generated::SPANS
                .iter()
                .any(|s| s.name == name),
            "the spec's span table must cover {name}"
        );
    }
    assert!(
        !guestlang_host::observability_generated::SPANS
            .iter()
            .any(|s| s.name == "calls"),
        "`calls` is the middleware's own export — not spec data"
    );

    rt.call("double", &[Val::U64(21)]).await?;
    let spans = fast_observe::breakdown::drain_spans();
    let double_span = spans
        .iter()
        .find(|s| s.name == "double")
        .expect("the wrapped call must be spanned");
    assert_eq!(
        double_span.tag,
        Some("once"),
        "the delivery tag = the spec's"
    );
    Ok(())
}

// ── Phase 2: the STREAM through the middleware ──────────────────────

/// THE STREAM INTERPOSITION PROOF: the composed watch-counts(n) runs
/// THROUGH the middleware — the interposer returns the INNER's
/// readable half AS the result (the zero-copy handle pass-through; a
/// naive pump would deadlock: a WASI 0.3 stream write blocks until
/// the consumer attaches, and the consumer attaches only after this
/// call returns). The host observes: the items (42,43) flow through
/// the handle, and the CALL counter ticked (the interposition ran).
#[tokio::test]
async fn the_middleware_forwards_the_inner_stream() -> Result<(), Box<dyn std::error::Error>> {
    let Some(path) = canonicalize_or_skip(
        &composed_path(),
        &format!("skipping: run `just splicer-mw` to build {:?}", composed_path()),
    ) else {
        return Ok(());
    };
    let engine = HostEngine::new()?;
    let component = engine.load_component(&path)?;
    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    // the STREAM rows: the call + the drain in ONE event loop — the
    // consumer must be a background task while the loop pumps the
    // guest's pending writes (same shape as wasm_diff's stream rows).
    let out: Arc<Mutex<Vec<u64>>> = Arc::new(Mutex::new(Vec::new()));
    let instance = rt.instance().expect("instance").clone();
    let sink = out.clone();
    rt.store_mut()
        .run_concurrent(async move |accessor| {
            let f = accessor
                .with(|access| instance.get_func(access, "watch-counts").expect("export"));
            let mut results = [Val::U64(0)];
            f.call_concurrent(accessor, &[Val::U64(3)], &mut results).await?;
            let any = match results[0].clone() {
                Val::Stream(a) => a,
                other => panic!("watch-counts: not a stream: {other:?}"),
            };
            let reader = any.try_into_stream_reader::<u64>()?;
            accessor
                .spawn(DrainTask::new(reader, sink, |v: &u64| v.clone()))?
                .await;
            Ok::<(), wasmtime::Error>(())
        })
        .await??;

    // the INNER's items arrived THROUGH the interposer, in order
    let items = out.lock().unwrap().clone();
    assert_eq!(items, vec![42, 43], "forwarded stream items");

    // the CALL counter ticked once (the wrapped call itself)
    let r = rt.call("calls", &[]).await?;
    assert!(matches!(&r[0], Val::U64(1)), "calls after 1 stream call: {:?}", r[0]);

    Ok(())
}

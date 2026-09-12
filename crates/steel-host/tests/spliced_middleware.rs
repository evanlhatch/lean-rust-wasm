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

use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll};

use steel_host::{CapabilitySet, ComponentRuntime, SteelEngine, HostState};
use wasmtime::component::{StreamConsumer, StreamResult, Source, Val};
use wasmtime::StoreContextMut;
use wasmtime::component::AccessorTask;

fn composed_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/spliced-mw/spliced-mw.component.wasm")
}

#[tokio::test]
async fn the_middleware_interposes_the_inner() -> Result<(), Box<dyn std::error::Error>> {
    let Ok(path) = std::fs::canonicalize(composed_path()) else {
        eprintln!(
            "skipping: run `just splicer-mw` to build {:?}",
            composed_path()
        );
        return Ok(());
    };
    let engine = SteelEngine::new()?;
    let component = engine.load_component(&path)?;
    let mut rt = ComponentRuntime::new(engine, CapabilitySet::NONE).await?;
    rt.instantiate(&component).await?;

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
    let Ok(path) = std::fs::canonicalize(composed_path()) else {
        eprintln!(
            "skipping: run `just splicer-mw` to build {:?}",
            composed_path()
        );
        return Ok(());
    };
    let engine = SteelEngine::new()?;
    let component = engine.load_component(&path)?;
    let mut rt = ComponentRuntime::new(engine, CapabilitySet::NONE).await?;
    rt.instantiate(&component).await?;

    // the spec's manifest covers the wrapped surface
    for name in ["double", "is-big"] {
        assert!(
            steel_host::observability_generated::SPANS
                .iter()
                .any(|s| s.name == name),
            "the spec's span table must cover {name}"
        );
    }
    assert!(
        !steel_host::observability_generated::SPANS
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

/// The stream-drain consumer: forwards the guest stream's u64 items
/// into a shared Vec (same shape as wasm_diff's DrainCommon — empty +
/// not-finished = Pending; returning Dropped there would lose in-flight
/// items).
struct DrainU64 {
    out: Arc<Mutex<Vec<u64>>>,
}
impl StreamConsumer<HostState> for DrainU64 {
    type Item = u64;
    fn poll_consume(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        store: StoreContextMut<'_, HostState>,
        mut source: Source<'_, u64>,
        finish: bool,
    ) -> Poll<wasmtime::Result<StreamResult>> {
        let mut buf: Vec<u64> = Vec::with_capacity(16);
        source.read(store, &mut buf)?;
        if buf.is_empty() {
            if finish {
                return Poll::Ready(Ok(StreamResult::Dropped));
            }
            return Poll::Pending;
        }
        self.out.lock().unwrap().extend(buf.drain(..));
        Poll::Ready(Ok(StreamResult::Completed))
    }
}

/// The drain task: pipes `reader` into [`DrainU64`] (a background task
/// — a sync pipe-set is never polled: the event loop exits first).
struct DrainU64Task {
    reader: wasmtime::component::StreamReader<u64>,
    sink: Arc<Mutex<Vec<u64>>>,
}
impl AccessorTask<HostState> for DrainU64Task {
    fn run(
        self,
        accessor: &wasmtime::component::Accessor<HostState>,
    ) -> impl std::future::Future<Output = wasmtime::Result<()>> + Send {
        let DrainU64Task { reader, sink } = self;
        async move {
            accessor
                .with(|access| reader.pipe(access, DrainU64 { out: sink }))
        }
    }
}

/// THE STREAM INTERPOSITION PROOF: the composed watch-counts(n) runs
/// THROUGH the middleware — the interposer returns the INNER's
/// readable half AS the result (the zero-copy handle pass-through; a
/// naive pump would deadlock: a WASI 0.3 stream write blocks until
/// the consumer attaches, and the consumer attaches only after this
/// call returns). The host observes: the items (42,43) flow through
/// the handle, and the CALL counter ticked (the interposition ran).
#[tokio::test]
async fn the_middleware_forwards_the_inner_stream() -> Result<(), Box<dyn std::error::Error>> {
    let Ok(path) = std::fs::canonicalize(composed_path()) else {
        eprintln!(
            "skipping: run `just splicer-mw` to build {:?}",
            composed_path()
        );
        return Ok(());
    };
    let engine = SteelEngine::new()?;
    let component = engine.load_component(&path)?;
    let mut rt = ComponentRuntime::new(engine, CapabilitySet::NONE).await?;
    rt.instantiate(&component).await?;

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
            accessor.spawn(DrainU64Task { reader, sink })?.await;
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

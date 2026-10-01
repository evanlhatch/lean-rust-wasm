//! THE STREAM RUNTIME FACE (the D2 `stream<u64>` WIT row's host lane).
//!
//! THE PULL DISCIPLINE: a component export returning `stream<u64>`-shaped
//! is consumed by the host as a PULL — the host reads the stream's items
//! until the end (`StreamResult::Dropped` closes the pull). The wasmtime
//! 47 stream API's shape (read from the vendored source): the export's
//! result lifts as `Val::Stream(StreamAny)` (a u32 handle in the flat
//! ABI); `StreamAny::try_into_stream_reader::<u64>()` recovers the typed
//! [`StreamReader`]; `StreamReader::pipe` attaches a
//! [`StreamConsumer`]; the consumer is polled by `Store::run_concurrent`'s
//! event loop — a pipe registered OUTSIDE the loop is never pumped (the
//! legacy `DrainTask` evidence: spawn the drain INSIDE `run_concurrent`
//! and await the join handle).
//!
//! THE SESSION'S RUNTIME FACE: the producer/consumer discipline IS the
//! session (`Machines.AsyncSession`'s shape, `ComponentTests.
//! StreamFixture`'s `guestStreamExport`/`hostStreamDrain`): the guest's
//! stream export delivers items IN ORDER then the end; the host's drain
//! is the DUAL (derived, never hand-written); the wire law pins the
//! order — the items cross 7, 8, 9, then the end (the session's
//! guarantee; the Lean pin `StreamFixture.msgs_wire`).
//!
//! THE HONEST BOUNDARY (named, never papered over): THIS lane's guest
//! fixture is a SYNC `func() -> stream<u64>` whose body creates the
//! stream and returns the readable half EMPTY (the `stream.new` +
//! `stream.drop-writable` canon intrinsics — a full sync crossing). A
//! guest PRODUCING items mid-body — suspending a write until the
//! consumer attaches, the legacy 1c — is the stack-switching /
//! async-lift CALLBACK discipline, NOT landed: wasmtime traps a sync
//! `stream.write` outside an async task (`check_blocking`), so
//! guest-side production rides the async-lift lane — the named seam
//! (`crate::wasi_async`, the async-lift lane now landed alongside).
//! The multi-item face tested here is the HOST-producer side of the
//! SAME pull discipline (wasmtime 47's `StreamProducer` for
//! `Vec<u64>`: items in order, then end) plus the zero-copy handle
//! pass-through export (the legacy `splicer-mw` evidence: the readable
//! half crosses the boundary AS a handle; the items flow through it).
//!
//! No unsafe; every failure is a [`crate::HostError`] — no panics on
//! real error paths (12 §8).

use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll};

use wasmtime::component::types::ComponentItem;
use wasmtime::component::{
    Accessor, AccessorTask, Component, Linker, ResourceTable, Source, StreamAny, StreamConsumer,
    StreamReader, StreamResult, Val,
};
use wasmtime::{Config, Engine, Store, StoreContextMut};

use crate::HostError;

// ---------------------------------------------------------------------------
// The store state + the engine (the stream lane's substrate)
// ---------------------------------------------------------------------------

/// The stream store's state: the resource table (the stream handles ride
/// the store's CONCURRENT state, not this table — the table is the p3
/// face's conventional carrier, kept empty here).
pub struct StreamState {
    /// The host's resource table.
    pub table: ResourceTable,
}

/// THE PUMP: yields the event loop until the pull's terminal flag is
/// set — each wake lets the executor pump the queued
/// produce/consume futures (the drain task registers them; the loop
/// runs them only while the run's future is PENDING). BOUNDED: a
/// stuck pump returns and the teeth's assertions fail loudly — never
/// a hang.
async fn pump_until_ended(ended: Arc<AtomicBool>) {
    let mut spins: u32 = 0;
    std::future::poll_fn(|cx| {
        if ended.load(Ordering::Relaxed) || spins > 10_000 {
            return Poll::Ready(());
        }
        spins += 1;
        cx.waker().wake_by_ref();
        Poll::Pending
    })
    .await;
}

/// The stream lane's engine: the component model + the ASYNC edge (the
/// stream lift's substrate — the same config face `crate::wasi`'s p3
/// lane carries; `stream.new`'s intrinsic validation requires it).
pub fn stream_engine() -> Result<Engine, HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    config.wasm_component_model_async(true);
    Engine::new(&config).map_err(|e| HostError::Engine(format!("engine init: {e:?}")))
}

// ---------------------------------------------------------------------------
// The surface checks (the pre-instantiation skew teeth)
// ---------------------------------------------------------------------------

/// THE SURFACE CHECK (the skew fail-fast's stream face): the component
/// TYPE's export `name` must be a func with NO params whose single
/// result is `stream<u64>` — the D2 row's runtime shape (`Ty.stream
/// Ty.u64`), read pre-instantiation (the ground truth; the check runs
/// BEFORE the linker — a mis-shaped export never instantiates). The
/// mismatch names the export + the expected surface.
pub fn check_stream_surface(
    engine: &Engine,
    component: &Component,
    name: &str,
) -> Result<(), HostError> {
    let expected = "func() -> stream<u64>";
    let func = component
        .component_type()
        .exports(engine)
        .find(|(n, _)| *n == name)
        .map(|(_, e)| e.ty);
    let Some(ComponentItem::ComponentFunc(f)) = func else {
        return Err(HostError::MissingExport(name.to_string()));
    };
    if f.params().count() != 0 {
        return Err(HostError::SurfaceSkew(format!(
            "export `{name}`: expected {expected}, got a non-vacuous param list"
        )));
    }
    let mut results = f.results();
    let mut got = match results.next() {
        Some(wasmtime::component::Type::Stream(st)) => match st.ty() {
            Some(wasmtime::component::Type::U64) => None,
            _ => Some("stream<non-u64>".to_string()),
        },
        Some(_) => Some("a non-stream result".to_string()),
        None => Some("func() -> ()".to_string()),
    };
    if results.next().is_some() {
        got.clone_from(&Some("multi-result".to_string()));
    }
    match got {
        None => Ok(()),
        Some(g) => Err(HostError::SurfaceSkew(format!(
            "export `{name}`: expected {expected}, got {g}"
        ))),
    }
}

/// THE PASS-THROUGH SURFACE CHECK (the pipeline tooth): the export
/// `name` must be `func(stream<u64>) -> stream<u64>` — the legacy
/// middleware's zero-copy pass-through shape (the readable half
/// crosses AS a handle; the items flow through it).
pub fn check_stream_pipeline_surface(
    engine: &Engine,
    component: &Component,
    name: &str,
) -> Result<(), HostError> {
    let expected = "func(stream<u64>) -> stream<u64>";
    let stream_u64 = |t: &wasmtime::component::Type| match t {
        wasmtime::component::Type::Stream(st) => {
            matches!(st.ty(), Some(wasmtime::component::Type::U64))
        }
        _ => false,
    };
    let func = component
        .component_type()
        .exports(engine)
        .find(|(n, _)| *n == name)
        .map(|(_, e)| e.ty);
    let Some(ComponentItem::ComponentFunc(f)) = func else {
        return Err(HostError::MissingExport(name.to_string()));
    };
    let params: Vec<_> = f.params().collect();
    let mut results = f.results();
    let shaped = params.len() == 1
        && stream_u64(&params[0].1)
        && matches!(results.next(), Some(t) if stream_u64(&t))
        && results.next().is_none();
    if shaped {
        Ok(())
    } else {
        Err(HostError::SurfaceSkew(format!(
            "export `{name}`: expected {expected}"
        )))
    }
}

// ---------------------------------------------------------------------------
// The drain consumer + task (the pull discipline's host face)
// ---------------------------------------------------------------------------

/// THE DRAIN CONSUMER: the stream's items → a shared Vec, IN ARRIVAL
/// ORDER (the session's guarantee's enforcement face). Empty + not
/// finished = Pending (returning `Dropped` there would END the stream
/// and lose in-flight items — the legacy `DrainCommon` discipline,
/// kept); finished with nothing in flight = the pull's end.
struct DrainConsumer {
    out: Arc<Mutex<Vec<u64>>>,
    ended: Arc<AtomicBool>,
}

impl StreamConsumer<StreamState> for DrainConsumer {
    type Item = u64;

    fn poll_consume(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        store: StoreContextMut<'_, StreamState>,
        mut source: Source<'_, Self::Item>,
        finish: bool,
    ) -> Poll<wasmtime::Result<StreamResult>> {
        let mut buf: Vec<u64> = Vec::with_capacity(16);
        source.read(store, &mut buf)?;
        if buf.is_empty() {
            if finish {
                self.ended.store(true, Ordering::Relaxed);
                return Poll::Ready(Ok(StreamResult::Dropped));
            }
            return Poll::Pending;
        }
        self.out.lock().unwrap().extend(buf.drain(..));
        self.ended.store(true, Ordering::Relaxed);
        Poll::Ready(Ok(StreamResult::Completed))
    }
}

/// THE DRAIN TASK: pipes the reader into [`DrainConsumer`] — a
/// BACKGROUND task in the call's event loop (a pipe registered outside
/// `run_concurrent` is never polled: the loop exits before pumping).
/// Spawn it inside `run_concurrent` and AWAIT the join handle (a
/// dropped handle may cancel the task) — the legacy `DrainTask`
/// discipline, kept.
struct DrainTask {
    reader: StreamReader<u64>,
    out: Arc<Mutex<Vec<u64>>>,
    ended: Arc<AtomicBool>,
}

impl AccessorTask<StreamState> for DrainTask {
    fn run(
        self,
        accessor: &Accessor<StreamState>,
    ) -> impl std::future::Future<Output = wasmtime::Result<()>> + Send {
        let DrainTask { reader, out, ended } = self;
        async move { accessor.with(|access| reader.pipe(access, DrainConsumer { out, ended })) }
    }
}

// ---------------------------------------------------------------------------
// The lane: instantiate + pull
// ---------------------------------------------------------------------------

/// THE STREAM LANE (the pull discipline's face): the component compiled,
/// its `stream<u64>` surface CHECKED (the skew tooth, pre-instantiation),
/// instantiated through the SYNC linker (the sync-first discipline —
/// `crate::wasi`'s component path; the async-lift integration is the
/// named seam), then the export called and the stream DRAINED: the
/// host pulls the items until the end, in order. The returned Vec IS
/// the session's wire (`StreamFixture.msgs_wire`'s payloads, the end
/// marker dropped).
pub fn drain_stream_u64_export(wasm: &[u8], name: &str) -> Result<Vec<u64>, HostError> {
    let engine = stream_engine()?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;
    check_stream_surface(&engine, &component, name)?;

    let mut store = Store::new(
        &engine,
        StreamState {
            table: ResourceTable::new(),
        },
    );
    let linker = Linker::<StreamState>::new(&engine);
    let instance = linker
        .instantiate(&mut store, &component)
        .map_err(|e| HostError::Engine(format!("component instantiate: {e:?}")))?;

    let out: Arc<Mutex<Vec<u64>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = out.clone();
    let ended = Arc::new(AtomicBool::new(false));
    let export = name.to_string();

    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .map_err(|e| HostError::Engine(format!("stream drain executor: {e:?}")))?;
    rt.block_on(async move {
        store
            .run_concurrent(async move |accessor| {
                let f = accessor.with(|access| {
                    instance
                        .get_func(access, export.as_str())
                        .expect("the surface check pinned the export")
                });
                // The placeholder's shape is never read — the lift
                // OVERWRITES the slot (the legacy `default_val` discipline).
                let mut results = [Val::List(Vec::new())];
                f.call_concurrent(accessor, &[], &mut results).await?;
                let any: StreamAny = match results[0].clone() {
                    Val::Stream(a) => a,
                    other => {
                        return Err(wasmtime::Error::msg(format!(
                            "export `{export}` did not answer a stream: {other:?}"
                        )));
                    }
                };
                let reader = any.try_into_stream_reader::<u64>()?;
                accessor.spawn(DrainTask {
                    reader,
                    out: sink,
                    ended: ended.clone(),
                })?;
                pump_until_ended(ended).await;
                Ok::<(), wasmtime::Error>(())
            })
            .await
    })
    .map_err(|e| HostError::Engine(format!("stream drain: {e:?}")))?
    .map_err(|e| HostError::Engine(format!("stream drain: {e:?}")))?;

    let pulled = out.lock().unwrap().clone();
    Ok(pulled)
}

/// THE HOST-PRODUCER FACE: the host creates the stream over a `Vec<u64>`
/// producer (wasmtime 47's own `StreamProducer` impl — items in order,
/// then the end) and drains it through the SAME pull consumer. The
/// multi-item + empty teeth's substrate (the guest-produced multi-item
/// stream is the async-lift seam — the module doc's boundary).
pub fn drain_host_stream(items: Vec<u64>) -> Result<Vec<u64>, HostError> {
    let engine = stream_engine()?;
    let mut store = Store::new(
        &engine,
        StreamState {
            table: ResourceTable::new(),
        },
    );
    let out: Arc<Mutex<Vec<u64>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = out.clone();
    let ended = Arc::new(AtomicBool::new(false));

    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .map_err(|e| HostError::Engine(format!("stream drain executor: {e:?}")))?;
    rt.block_on(async move {
        store
            .run_concurrent(async move |accessor| {
                let reader = accessor.with(|access| {
                    StreamReader::new(access, items)
                        .map_err(|e| wasmtime::Error::msg(format!("host stream: {e:?}")))
                })?;
                accessor.spawn(DrainTask {
                    reader,
                    out: sink,
                    ended: ended.clone(),
                })?;
                pump_until_ended(ended).await;
                Ok::<(), wasmtime::Error>(())
            })
            .await
    })
    .map_err(|e| HostError::Engine(format!("host stream drain: {e:?}")))?
    .map_err(|e| HostError::Engine(format!("host stream drain: {e:?}")))?;

    let pulled = out.lock().unwrap().clone();
    Ok(pulled)
}

/// THE ZERO-COPY HANDLE PASS-THROUGH (the legacy `splicer-mw`
/// evidence): the host creates the stream over the item producer,
/// LOWERS the readable half into the guest's `pass` export (the handle
/// crosses the boundary AS a u32), the guest's body returns it
/// unchanged, and the drain pulls the items THROUGH the returned
/// handle — the items never touch the guest's memory. The pull
/// discipline's boundary face.
pub fn pass_through_stream(
    wasm: &[u8],
    name: &str,
    items: Vec<u64>,
) -> Result<Vec<u64>, HostError> {
    let engine = stream_engine()?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;
    check_stream_pipeline_surface(&engine, &component, name)?;

    let mut store = Store::new(
        &engine,
        StreamState {
            table: ResourceTable::new(),
        },
    );
    let linker = Linker::<StreamState>::new(&engine);
    let instance = linker
        .instantiate(&mut store, &component)
        .map_err(|e| HostError::Engine(format!("component instantiate: {e:?}")))?;

    let out: Arc<Mutex<Vec<u64>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = out.clone();
    let ended = Arc::new(AtomicBool::new(false));
    let export = name.to_string();

    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .map_err(|e| HostError::Engine(format!("stream pass-through executor: {e:?}")))?;
    rt.block_on(async move {
        store
            .run_concurrent(async move |accessor| {
                // The host-produced readable half → the wire as a
                // `stream<u64>` handle.
                let reader: StreamReader<u64> = accessor.with(|access| {
                    StreamReader::new(access, items)
                        .map_err(|e| wasmtime::Error::msg(format!("host stream: {e:?}")))
                })?;
                let handle: StreamAny =
                    accessor.with(|access| reader.try_into_stream_any(access))?;

                // THE PASS-THROUGH: the guest's identity body answers
                // the same handle (the flat ABI's u32, re-lifted).
                let f = accessor.with(|access| {
                    instance
                        .get_func(access, export.as_str())
                        .expect("the surface check pinned the export")
                });
                let mut results = [Val::List(Vec::new())];
                f.call_concurrent(accessor, &[Val::Stream(handle)], &mut results)
                    .await?;
                let answered: StreamAny = match results[0].clone() {
                    Val::Stream(a) => a,
                    other => {
                        return Err(wasmtime::Error::msg(format!(
                            "export `{export}` did not answer a stream: {other:?}"
                        )));
                    }
                };
                let reader = StreamReader::try_from_stream_any(answered)?;

                // THE DRAIN: the items flow through the handle, in
                // order, until the end (the same pull consumer).
                accessor.spawn(DrainTask {
                    reader,
                    out: sink,
                    ended: ended.clone(),
                })?;
                pump_until_ended(ended).await;
                Ok::<(), wasmtime::Error>(())
            })
            .await
    })
    .map_err(|e| HostError::Engine(format!("stream pass-through: {e:?}")))?
    .map_err(|e| HostError::Engine(format!("stream pass-through: {e:?}")))?;

    let pulled = out.lock().unwrap().clone();
    Ok(pulled)
}

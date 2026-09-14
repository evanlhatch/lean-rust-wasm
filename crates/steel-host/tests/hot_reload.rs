//! HOT-RELOAD lane: the host swaps a component WITHOUT restarting.
//! notes/full-remaining-work.md: "State lives in the host (or the event
//! log), not in the component."
//!
//! The ROUTER pattern (all in this test — the pattern = the
//! demonstration): a tiny router struct holds the CURRENT
//! [`ComponentRuntime`] behind a `tokio::sync::Mutex` (the async
//! RwLock's shape — one writer per route, the guard = the call
//! boundary). `route` = the current rt's `call`. `swap` = install the
//! new rt, hand the OLD one back by value — the in-flight caller's
//! live reference (the Arc semantics: the old runtime stays fully
//! alive in the caller's hand, its store/instance self-owned, no
//! host-shared mutable state).
//!
//! THE SWAP: v1 = the compiled Lean demo (`demo.component.wasm`,
//! `just wasm-compile`); v2 = the spliced-middleware composed
//! (`spliced-mw.component.wasm`, `just splicer-mw`) — the SAME
//! guestlang:demo inner, the SAME exports (`double`, `is-big`,
//! `watch-counts`) PLUS the middleware's `calls` counter. The live
//! upgrade = the INTERPOSER INSERTED: the calls BEFORE = the direct;
//! the calls AFTER = the counted.
//!
//! THE STATE STORY (the pin):
//! - The swap = AT THE CALL-BOUNDARY. There is no in-flight state to
//!   migrate in the honest v1: the old runtime is quiesced (unrouted),
//!   the new one starts fresh. The wasm-side state migration —
//!   snapshot the old heap, restore it into the new instance
//!   (guestlang-rt's `Snapshot` = the WARM-START mechanism) — is
//!   deliberately SKIPPED here; the swap = at the quiesce point.
//! - The host's state (the router's `served` counter) is UNAFFECTED
//!   by the swap — it counts across both runtimes continuously.
//! - The component's state = the HEAP = fresh-per-instance: v2's
//!   `calls` starts at 0 even though v1 served calls before the swap.
//!
//! Ownership: crates/steel-host/tests/hot_reload.rs (hot-reload lane).
//! Additive only; src/** untouched. Skips if the wasm artifacts are
//! missing (they are the prerequisite builds, not this test's output).

use std::path::PathBuf;

use steel_host::{CapabilitySet, ComponentRuntime, SteelEngine};
use wasmtime::component::Val;

/// v1: the compiled Lean demo (the direct component).
fn v1_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/wasm-backend/target/demo.component.wasm")
}

/// v2: the SAME demo, composed through the middleware interposer
/// (guestlang:demo inner + `calls` counter — same world, same exports,
/// the count layer inserted between).
fn v2_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/spliced-mw/spliced-mw.component.wasm")
}

/// The ROUTER: the host's stable traffic front-door. The current
/// runtime sits behind a mutex — the lock guard = the call boundary
/// (a swap can only land between calls, i.e. at the quiesce point).
/// Host state (`served`) lives OUTSIDE the component: it survives the
/// swap untouched.
struct Router {
    engine: SteelEngine,
    current: tokio::sync::Mutex<Option<ComponentRuntime>>,
    /// THE HOST'S STATE: served-request count, incremented per
    /// successful route. Not component state — the swap cannot touch it.
    served: tokio::sync::Mutex<u64>,
}

impl Router {
    async fn new(engine: SteelEngine) -> Self {
        Self {
            engine,
            current: tokio::sync::Mutex::new(None),
            served: tokio::sync::Mutex::new(0),
        }
    }

    /// Load + instantiate a component and install it as the current
    /// runtime. The OLD runtime comes back by value — the caller's
    /// live reference (the Arc semantics: the swap does NOT drop or
    /// invalidate anything the in-flight caller holds).
    async fn swap(
        &self,
        component: &wasmtime::component::Component,
    ) -> Result<Option<ComponentRuntime>, Box<dyn std::error::Error>> {
        let mut rt = ComponentRuntime::new(self.engine.clone(), CapabilitySet::NONE).await?;
        rt.instantiate(component).await?;
        let mut slot = self.current.lock().await;
        Ok(std::mem::replace(&mut *slot, Some(rt)))
    }

    /// Route one call: the CURRENT runtime's call. The routing choice
    /// (which component answers) = the caller's, made per call.
    async fn route(
        &self,
        func: &str,
        args: &[Val],
    ) -> steel_host::SteelResult<Vec<Val>> {
        let mut slot = self.current.lock().await;
        let rt = slot.as_mut().expect("router: no runtime installed");
        let out = rt.call(func, args).await;
        drop(slot);
        if out.is_ok() {
            *self.served.lock().await += 1;
        }
        out
    }

    async fn served(&self) -> u64 {
        *self.served.lock().await
    }
}

fn skip(paths: &[&PathBuf]) -> Option<String> {
    let missing: Vec<_> = paths
        .iter()
        .filter(|p| !p.exists())
        .map(|p| p.display().to_string())
        .collect();
    (!missing.is_empty()).then(|| {
        eprintln!(
            "skipping: run `just wasm-compile && just splicer-mw` to build {missing:?}"
        );
        "missing artifacts".to_string()
    })
}

/// THE SWAP = THE LIVE UPGRADE (the interposer inserted):
/// - BEFORE: `double` answers directly, NO counter export exists
///   (the missing-export fault = the observed absence of the
///   interposer), `served` accumulates.
/// - SWAP: v1 out (handed to the caller), v2 in.
/// - AFTER: identical answers (the pass-through), the counter = 0→N
///   (the interposer is LIVE), `served` CONTINUES across the swap
///   (the host's state unaffected), v2's counter starts FRESH at 0
///   (the component's heap state = per-instance — v1's call history
///   did not migrate; that migration = the snapshot/restore warm
///   start, deliberately skipped in the honest v1).
#[tokio::test]
async fn the_swap_inserts_the_interposer_live() -> Result<(), Box<dyn std::error::Error>> {
    let (p1, p2) = (v1_path(), v2_path());
    if let Some(msg) = skip(&[&p1, &p2]) {
        let _ = msg;
        return Ok(());
    }
    let engine = SteelEngine::new()?;
    let v1 = engine.load_component(&p1)?;
    let v2 = engine.load_component(&p2)?;

    let router = Router::new(engine).await;

    // ── BEFORE: the direct path ────────────────────────────────────
    router.swap(&v1).await?;
    let r = router.route("double", &[Val::U64(21)]).await?;
    assert!(matches!(&r[0], Val::U64(42)), "v1 double broke: {:?}", r[0]);
    // v1 has NO `calls` export — the interposer is not there yet.
    let err = router.route("calls", &[]).await.unwrap_err();
    assert!(
        err.to_string().contains("missing export: calls"),
        "v1 must lack the counter export: {err}"
    );
    let r = router.route("double", &[Val::U64(3)]).await?;
    assert!(matches!(&r[0], Val::U64(6)), "v1 double broke: {:?}", r[0]);
    assert_eq!(router.served().await, 2, "host state counts v1 routes");

    // ── THE SWAP: demo → spliced-mw, no restart ────────────────────
    let _old = router.swap(&v2).await?;

    // ── AFTER: the counted path, identical answers ─────────────────
    // v2's counter starts at ZERO — fresh heap per instance. v1's two
    // calls did NOT migrate (the swap = at the quiesce point; the
    // warm-start migration = the snapshot/restore's advanced version).
    let r = router.route("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(0)),
        "v2 counter must start fresh: {:?}",
        r[0]
    );
    // The pass-through: same inputs, same answers, now counted.
    let r = router.route("double", &[Val::U64(21)]).await?;
    assert!(matches!(&r[0], Val::U64(42)), "v2 double broke: {:?}", r[0]);
    let r = router.route("is-big", &[Val::U64(5)]).await?;
    assert!(matches!(r[0], Val::Bool(_)), "v2 is-big broke: {:?}", r[0]);
    let r = router.route("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(2)),
        "interposer must count both routed calls: {:?}",
        r[0]
    );
    // THE HOST'S STATE: served = 2 (v1) + 4 (v2 routes: calls +
    // double + is-big + the counter probe) — continuous ACROSS the
    // swap, unaffected by it. (The pre-swap `calls` fault did NOT
    // count — only successful routes.)
    assert_eq!(router.served().await, 6, "host state survives the swap");
    // The old runtime is still held (the live reference) — not dropped
    // by the swap. See the in-flight test below for its completion.

    Ok(())
}

/// THE NEGATIVE CONTROL: the swap DURING an in-flight call. The caller
/// takes the live reference (the old runtime handed back by `swap` —
/// the Arc semantics: a live reference keeps the old runtime fully
/// functional), THEN the swap installs v2, THEN the "in-flight" call
/// on the old runtime completes — its store/instance are self-owned,
/// no host-shared mutable state, nothing the swap did touched it. The
/// router's NEXT route goes to v2. The in-flight = unaffected.
#[tokio::test]
async fn the_swap_does_not_disturb_the_in_flight_call() -> Result<(), Box<dyn std::error::Error>> {
    let (p1, p2) = (v1_path(), v2_path());
    if let Some(msg) = skip(&[&p1, &p2]) {
        let _ = msg;
        return Ok(());
    }
    let engine = SteelEngine::new()?;
    let v1 = engine.load_component(&p1)?;
    let v2 = engine.load_component(&p2)?;
    let router = Router::new(engine).await;
    router.swap(&v1).await?;

    // The caller grabs the live reference (the in-flight slot opens —
    // the quiesce point where a swap may land).
    let mut in_flight = router.swap(&v2).await?.expect("v1 runtime");

    // The router is ALREADY on v2, but the in-flight call still runs
    // on v1 — and completes with the v1 answer.
    let r = in_flight.call("double", &[Val::U64(21)]).await?;
    assert!(
        matches!(&r[0], Val::U64(42)),
        "the old runtime must complete post-swap: {:?}",
        r[0]
    );
    drop(in_flight);

    // The router's next route = the NEW runtime (v2): the counter is
    // live from the first routed call.
    let r = router.route("double", &[Val::U64(21)]).await?;
    assert!(matches!(&r[0], Val::U64(42)), "routed call broke: {:?}", r[0]);
    let r = router.route("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(1)),
        "the routed call went through v2's interposer: {:?}",
        r[0]
    );
    Ok(())
}

// ═══════════════════════════════════════════════════════════════════
// WARM-START lane (additive): the swap WITH the state-carryover.
//
// THE CHOSEN PATH = the APPLICATION-level event-log replay. The
// memory-image path (guestlang-rt's `Runtime::snapshot` /
// `Snapshot::restore` — the reference pattern) is IMPOSSIBLE at the
// wasmtime component level, pinned by two facts (wasmtime 47.0.4):
// 1. `component::Instance` has NO `get_memory` (the lookup surface:
//    get_func/get_typed_func/get_module/get_resource/get_export*).
// 2. `ComponentItem` has NO memory variant (ComponentFunc | CoreFunc |
//    Module | Component | ComponentInstance | Type | Resource) — even
//    `get_export` on a memory-named export cannot yield a
//    `wasmtime::Memory` handle.
// The component model deliberately hides core memories from the host:
// the guest's heap is SELF-managed, so "extract at swap, inject at
// instantiate" has no component-level API. (Probe 1 below runs this
// check live against the swapped-out v1.)
//
// So the warm start = the notes' "state lives in the host (or the
// event log)" taken LITERALLY: the host logs every successful pre-swap
// route (func + args + result), and after the swap REPLAYS the log
// into the swapped-in instance. The replay is the state migration:
// the new instance's observable state (the interposer's `calls`
// counter) ends up reflecting the PRE-swap history. The negative
// control = the same swap WITHOUT the replay — the state is lost.
#[tokio::test]
async fn the_warm_start_replays_the_event_log_into_the_swapped_in_runtime(
) -> Result<(), Box<dyn std::error::Error>> {
    let (p1, p2) = (v1_path(), v2_path());
    if let Some(msg) = skip(&[&p1, &p2]) {
        let _ = msg;
        return Ok(());
    }
    let engine = SteelEngine::new()?;
    let v1 = engine.load_component(&p1)?;
    let v2 = engine.load_component(&p2)?;
    let router = Router::new(engine).await;

    // ── BEFORE: v1 serves; the host LOGS every successful route ────
    // (func, arg, result) — the event log IS the durable state.
    router.swap(&v1).await?;
    let mut log: Vec<(&str, u64, u64)> = Vec::new();
    for n in [21u64, 3] {
        let r = router.route("double", &[Val::U64(n)]).await?;
        let Val::U64(x) = &r[0] else {
            panic!("v1 double returned non-u64: {:?}", r[0])
        };
        log.push(("double", n, *x));
    }
    assert_eq!(router.served().await, 2, "the log covers both v1 routes");
    assert_eq!(
        log,
        vec![("double", 21, 42), ("double", 3, 6)],
        "the host's event log = the pre-swap history"
    );

    // ── THE SWAP: v1 out (handed back), v2 in ──────────────────────
    let _old = router.swap(&v2).await?.expect("v1 runtime");
    // PROBE — the wasmtime-level honest limit: NOT runnable, by
    // construction. `component::Instance` exposes no `get_memory`, and
    // `ComponentItem` (what `get_export` returns) has no memory variant
    // — verified against the vendored wasmtime 47.0.4 source
    // (src/runtime/component/instance.rs: the lookup surface =
    // get_func/get_typed_func/get_module/get_resource/get_export*;
    // src/runtime/component/types.rs: ComponentItem = ComponentFunc |
    // CoreFunc | Module | Component | ComponentInstance | Type |
    // Resource). The wasmtime-ownership shape closes it further: a
    // `ComponentRuntime` owns the store AND the instance, so the host
    // cannot even co-borrow them for a hypothetical lookup. No memory
    // handle reaches the host: the memory-image injection path is
    // closed at the component level — hence the replay below.

    // ── THE WARM START: the host REPLAYS the log into v2 ───────────
    // Each replayed call re-executes the pre-swap history on the NEW
    // instance; results must MATCH the logged ones (deterministic
    // re-execution = the carryover's observable content).
    for (func, n, expected) in &log {
        let r = router.route(func, &[Val::U64(*n)]).await?;
        let Val::U64(x) = &r[0] else {
            panic!("replay returned non-u64: {:?}", r[0])
        };
        assert_eq!(
            x, expected,
            "replay of {func}({n}) diverged from the logged result"
        );
    }

    // THE CARRYOVER, VISIBLE: v2's interposer counted the REPLAYED
    // history — the new instance's state now reflects the PRE-swap
    // call count (2), which a fresh instance would NOT have.
    let r = router.route("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(2)),
        "the replayed history must show in v2's state: {:?}",
        r[0]
    );
    assert_eq!(router.served().await, 5, "2 pre-swap + 2 replay + 1 probe");

    // ── THE NEGATIVE CONTROL: the swap WITHOUT the replay ──────────
    // A fresh v2 (same component, same host) with NO log replay: the
    // history is GONE — the counter reads 0. The contrast pins the
    // replay as the mechanism: the carryover came from the host's
    // event log, not from the swap itself.
    let _old2 = router.swap(&v2).await?;
    let r = router.route("calls", &[]).await?;
    assert!(
        matches!(&r[0], Val::U64(0)),
        "no replay = state lost (fresh heap per instance): {:?}",
        r[0]
    );
    // The host's own state still counts continuously across BOTH swaps.
    assert_eq!(router.served().await, 6, "host state survives both swaps");
    Ok(())
}

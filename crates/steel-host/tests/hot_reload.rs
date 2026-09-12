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

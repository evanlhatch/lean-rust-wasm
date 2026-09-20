//! The WARM-START pattern demo — the swap WITH the state-carryover.
//!
//! Moved out of `tests/hot_reload.rs` (the consolidation): this is a
//! PATTERN demonstration, not a behavior gate — it exercises no
//! `src/**` code beyond what the kept gates already cover
//! (`ComponentRuntime::call` across a swap). The negative control for
//! the BEHAVIOR (fresh heap per instance, no silent state migration)
//! stays in `tests/hot_reload.rs`'s `the_swap_inserts_the_interposer_live`.
//!
//! THE CHOSEN PATH = the APPLICATION-level event-log replay. The
//! memory-image path (guestlang-rt's `Runtime::snapshot` /
//! `Snapshot::restore` — the reference pattern) is IMPOSSIBLE at the
//! wasmtime component level, pinned by two facts (wasmtime 47.0.4):
//! 1. `component::Instance` has NO `get_memory` (the lookup surface:
//!    get_func/get_typed_func/get_module/get_resource/get_export*).
//! 2. `ComponentItem` has NO memory variant (ComponentFunc | CoreFunc |
//!    Module | Component | ComponentInstance | Type | Resource) — even
//!    `get_export` on a memory-named export cannot yield a
//!    `wasmtime::Memory` handle.
//! The component model deliberately hides core memories from the host:
//! the guest's heap is SELF-managed, so "extract at swap, inject at
//! instantiate" has no component-level API.
//!
//! So the warm start = "state lives in the host (or the event log)"
//! taken LITERALLY: the host logs every successful pre-swap route
//! (func + args + result), and after the swap REPLAYS the log into the
//! swapped-in instance. The replay is the state migration.
//!
//! Run: `cargo run -p guestlang-host --example warm_start_event_log`
//! (after `just wasm-compile && just splicer-mw`; skips if the
//! artifacts are missing).

use std::path::PathBuf;

use guestlang_host::{CapabilitySet, ComponentRuntime, HostEngine};
use wasmtime::component::Val;

fn v1_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean/wasm-backend/target/demo.component.wasm")
}

fn v2_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/spliced-mw/spliced-mw.component.wasm")
}

/// The ROUTER: the host's stable traffic front-door (the hot-reload
/// lane's pattern — see tests/hot_reload.rs for the full derivation).
struct Router {
    engine: HostEngine,
    current: tokio::sync::Mutex<Option<ComponentRuntime>>,
    served: tokio::sync::Mutex<u64>,
}

impl Router {
    async fn new(engine: HostEngine) -> Self {
        Self {
            engine,
            current: tokio::sync::Mutex::new(None),
            served: tokio::sync::Mutex::new(0),
        }
    }

    async fn swap(
        &self,
        component: &wasmtime::component::Component,
    ) -> Result<Option<ComponentRuntime>, Box<dyn std::error::Error>> {
        let mut rt = ComponentRuntime::new(self.engine.clone(), CapabilitySet::NONE).await?;
        rt.instantiate(component).await?;
        let mut slot = self.current.lock().await;
        Ok(std::mem::replace(&mut *slot, Some(rt)))
    }

    async fn route(&self, func: &str, args: &[Val]) -> guestlang_host::HostResult<Vec<Val>> {
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

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (p1, p2) = (v1_path(), v2_path());
    let missing: Vec<_> = [&p1, &p2]
        .into_iter()
        .filter(|p| !p.exists())
        .map(|p| p.display().to_string())
        .collect();
    if !missing.is_empty() {
        eprintln!(
            "skipping: run `just wasm-compile && just splicer-mw` to build {missing:?}"
        );
        return Ok(());
    }
    let engine = HostEngine::new()?;
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
    println!("served: {}", router.served().await);
    println!("log: {log:?}");
    assert_eq!(router.served().await, 2, "the log covers both v1 routes");
    assert_eq!(
        log,
        vec![("double", 21, 42), ("double", 3, 6)],
        "the host's event log = the pre-swap history"
    );

    // ── THE SWAP: v1 out (handed back), v2 in ──────────────────────
    let _old = router.swap(&v2).await?.expect("v1 runtime");

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
    println!("served after warm start: {}", router.served().await);
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
    println!("fresh instance after no-replay swap: calls = 0 (state lost, as pinned)");
    // The host's own state still counts continuously across BOTH swaps.
    assert_eq!(router.served().await, 6, "host state survives both swaps");
    Ok(())
}

//! Shared harness for guestlang-host's integration suites (one copy of the
//! setup every test was hand-rolling):
//!
//! - FIXTURE PATHS — the demo-wasm location discipline in one place:
//!   the compiled Lean guests live under `lean/wasm-backend/target/`
//!   (repo root, NOT the crate's own `target/`), the spliced/composed
//!   artifacts and rustc guest builds under the repo `target/`, and the
//!   test-only fixtures under `tests/fixtures/`. Every path helper
//!   below is THE spelling of one artifact's location.
//! - SETUP — `canonicalize_or_skip` (the skip-if-unbuilt discipline)
//!   and `instantiate` (engine + capability set → a live
//!   [`ComponentRuntime`], the default GuestSetup shape). Per-test
//!   custom setups (the typed bindgen path, hot-reload's Router, the
//!   plain-core-module edgepython duel) stay in their suites.
//! - STREAM DRAIN — [`drain::DrainCommon`] / [`drain::DrainTask`]:
//!   the consumer = polled by the event loop as a BACKGROUND task (a
//!   sync pipe-set is never polled: the loop exits before pumping).
//!   Empty + not-finished = Pending — returning Dropped there ENDS the
//!   stream and the in-flight items are lost. Do not "simplify" that.
//! - HOUSE HELPERS — `fail` (no bare unwrap in tests), `tempdir`, and
//!   the wit-parser lookup trio (`wit::resolve_gateway` etc.).
//!
//! Ownership: crates/guestlang-host/tests/common/mod.rs. Additive to
//! src/**: nothing here touches it. The suites' ASSERTIONS stay in the
//! suites — the harness carries no expectations of its own.

// Per-binary compilation (each tests/*.rs includes this module) leaves
// most helpers unused in any given binary — the harness is the shared
// surface, not each inclusion.
#![allow(dead_code)]

use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll};

use guestlang_host::{CapabilitySet, ComponentRuntime, HostState, HostEngine};
use wasmtime::StoreContextMut;
use wasmtime::component::{
    Accessor, AccessorTask, Component, Lift, Source, StreamConsumer, StreamReader, StreamResult,
};

// ── fixture paths ───────────────────────────────────────────────────

/// A path relative to the REPO ROOT (the fixture location discipline:
/// the wasm artifacts are the wasm-backend's builds, not this crate's
/// output — tests only consume them).
pub fn repo_path(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../{rel}"))
}

/// The compiled Lean demo component (`just wasm-compile`) — THE guest
/// every suite loads. Component-wrapped (`demo.wasm` + component embed/new).
pub fn demo_component_path() -> PathBuf {
    repo_path("lean/wasm-backend/target/demo.component.wasm")
}

/// The pre-`component new` CORE module (`just wasm-compile`'s inner
/// artifact — a well-formed wasm binary of the wrong layer).
pub fn demo_core_path() -> PathBuf {
    repo_path("lean/wasm-backend/target/demo.wasm")
}

/// The passthrough-spliced demo component (`just splice-smoke`).
pub fn spliced_component_path() -> PathBuf {
    repo_path("lean/wasm-backend/target/spliced.component.wasm")
}

/// The middleware-COMPOSED demo (`just splicer-mw`): the same
/// guestlang:demo inner + the `calls` counter interposer.
pub fn spliced_mw_path() -> PathBuf {
    repo_path("target/spliced-mw/spliced-mw.component.wasm")
}

/// The rustc core-module guest's component (`just wasm-guest-component`).
pub fn guest_demo_component_path() -> PathBuf {
    repo_path("target/wasm32-unknown-unknown/debug/guest_demo.component.wasm")
}

/// The gateway-world component (`just wasm-guest-gateway`) — the typed
/// bindgen path's artifact.
pub fn gateway_component_path() -> PathBuf {
    repo_path("target/wasm32-unknown-unknown/debug/guest_demo.gateway.component.wasm")
}

/// The wasip3 artifact (`just wasm-guest`): std linked against wasi
/// 0.3 component imports.
pub fn wasip3_guest_path() -> PathBuf {
    repo_path("target/wasm32-wasip3-local/debug/guest_demo.wasm")
}

/// The EdgePython duel module (`just edgepython`).
pub fn py_wasm_path() -> PathBuf {
    repo_path("lean/edgepython/target/py.wasm")
}

/// The differential manifest — the wasm-backend oracle's generated rows.
pub fn diff_json_path() -> PathBuf {
    repo_path("lean/wasm-backend/target/diff.json")
}

/// Lean's committed schema-surface rendering (`lake exe oracle coverage`).
pub fn coverage_md_path() -> PathBuf {
    repo_path("lean/wasm-backend/COVERAGE.md")
}

/// The COMMITTED universe snapshot (the byte-tied SSOT).
pub fn universe_snapshot_path() -> PathBuf {
    repo_path("lean/schema-lang/goldens/universe.snapshot")
}

/// The GENERATED wit the host's `bindgen!` consumed.
pub fn gateway_wit_path() -> PathBuf {
    repo_path("wit/gateway.wit")
}

/// The crate's test fixtures (wit sweeps, the tampered snapshot).
pub fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// A file under [`fixtures_dir`].
pub fn fixture(rel: &str) -> PathBuf {
    fixtures_dir().join(rel)
}

// ── setup helpers ───────────────────────────────────────────────────

/// Canonicalize-or-skip: the artifact-loading tests skip (with a
/// message naming the `just` recipe) when the prerequisite build is
/// absent — the artifacts are the prerequisite builds, not the tests'
/// output. `skip_msg` = the test's own skip diagnostic (printed
/// verbatim, matching the pre-harness wording).
pub fn canonicalize_or_skip(path: &Path, skip_msg: &str) -> Option<PathBuf> {
    match std::fs::canonicalize(path) {
        Ok(p) => Some(p),
        Err(_) => {
            eprintln!("{skip_msg}");
            None
        }
    }
}

/// Engine + capability set → a live runtime over `component`: the
/// default guest-setup shape (fresh `ComponentRuntime` on the engine,
/// instantiated, no skew check — the checked variant stays per-test).
pub async fn instantiate(
    engine: &HostEngine,
    component: &Component,
    caps: CapabilitySet,
) -> Result<ComponentRuntime, Box<dyn std::error::Error>> {
    let mut rt = ComponentRuntime::new(engine.clone(), caps).await?;
    rt.instantiate(component).await?;
    Ok(rt)
}

// ── house helpers ───────────────────────────────────────────────────

/// Fail loud, fail clear (the house pattern: no bare `unwrap`).
#[track_caller]
#[allow(clippy::panic, reason = "test helper: fail loud, fail clear")]
pub fn fail(msg: &str) -> ! {
    panic!("{msg}");
}

/// Unique tempdir per test (the wasm-delta pattern).
pub fn tempdir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "guestlang-host-{tag}-{}-{:x}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.subsec_nanos())
            .unwrap_or(0)
    ));
    std::fs::create_dir_all(&dir).unwrap_or_else(|e| fail(&format!("tempdir: {e}")));
    dir
}

// ── wit-parser lookups (shared by the round-trip + byte-tie gates) ──

pub mod wit {
    use std::path::PathBuf;
    use wit_parser::{Interface, Resolve, Type, TypeDefKind, TypeId};

    /// Resolve `wit/gateway.wit` into a fully-resolved `Resolve` plus
    /// the parsed package's id.
    pub fn resolve_gateway() -> Result<(Resolve, wit_parser::PackageId), Box<dyn std::error::Error>>
    {
        let mut resolve = Resolve::default();
        let (pkg_id, _sources) = resolve.push_path(&PathBuf::from(super::gateway_wit_path()))?;
        Ok((resolve, pkg_id))
    }

    /// Look up an interface by name inside the parsed package.
    pub fn interface<'r>(
        resolve: &'r Resolve,
        pkg: wit_parser::PackageId,
        name: &str,
    ) -> Result<&'r Interface, Box<dyn std::error::Error>> {
        let pkg = &resolve.packages[pkg];
        let id = pkg.interfaces.get(name).ok_or(format!(
            "package {}:{} has no interface `{name}`",
            pkg.name.namespace, pkg.name.name
        ))?;
        Ok(&resolve.interfaces[*id])
    }

    /// Follow `type` aliases (a `use`d type gets its own TypeDef whose
    /// kind is `Type(Type::Id(original))`) down to the underlying
    /// definition.
    pub fn follow_alias(resolve: &Resolve, mut id: TypeId) -> TypeId {
        while let TypeDefKind::Type(Type::Id(next)) = resolve.types[id].kind {
            id = next;
        }
        id
    }
}

// ── the stream-drain machinery ──────────────────────────────────────

pub mod drain {
    use super::{
        Accessor, AccessorTask, Arc, Context, HostState, Lift, Mutex, PhantomData, Pin, Poll,
        Source, StoreContextMut, StreamConsumer, StreamReader, StreamResult,
    };

    /// The stream-drain consumer: the guest stream's items → a shared
    /// Vec (rendered item-by-item by `render`). Polled by the event
    /// loop; empty + not-finished = Pending (returning Dropped there
    /// ENDS the stream and the in-flight items are lost).
    pub struct DrainCommon<T, R, F = fn(&T) -> R> {
        out: Arc<Mutex<Vec<R>>>,
        render: F,
        _ty: PhantomData<fn(&T) -> R>,
    }

    impl<T, R, F> DrainCommon<T, R, F> {
        pub fn new(out: Arc<Mutex<Vec<R>>>, render: F) -> Self {
            Self {
                out,
                render,
                _ty: PhantomData,
            }
        }
    }

    impl<T, R, F> StreamConsumer<HostState> for DrainCommon<T, R, F>
    where
        T: Lift + Send + Sync + 'static,
        R: Send + Sync + 'static,
        F: Fn(&T) -> R + Send + Sync + 'static,
    {
        type Item = T;
        fn poll_consume(
            self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            store: StoreContextMut<'_, HostState>,
            mut source: Source<'_, Self::Item>,
            finish: bool,
        ) -> Poll<wasmtime::Result<StreamResult>> {
            let mut buf: Vec<T> = Vec::with_capacity(16);
            source.read(store, &mut buf)?;
            if buf.is_empty() {
                if finish {
                    return Poll::Ready(Ok(StreamResult::Dropped));
                }
                return Poll::Pending;
            }
            let render = &self.render;
            self.out
                .lock()
                .unwrap()
                .extend(buf.drain(..).map(move |t| render(&t)));
            Poll::Ready(Ok(StreamResult::Completed))
        }
    }

    /// The drain task: pipes `reader` into [`DrainCommon`] — a
    /// BACKGROUND task in the call's event loop (a sync pipe-set is
    /// never polled: the loop exits before pumping). Spawn it inside
    /// `run_concurrent` and AWAIT the join handle (a dropped handle may
    /// cancel the task).
    pub struct DrainTask<T, R, F = fn(&T) -> R> {
        reader: StreamReader<T>,
        sink: Arc<Mutex<Vec<R>>>,
        render: F,
    }

    impl<T, R, F> DrainTask<T, R, F> {
        pub fn new(reader: StreamReader<T>, sink: Arc<Mutex<Vec<R>>>, render: F) -> Self {
            Self {
                reader,
                sink,
                render,
            }
        }
    }

    impl<T, R, F> AccessorTask<HostState> for DrainTask<T, R, F>
    where
        T: Lift + Send + Sync + 'static,
        R: Send + Sync + 'static,
        F: Fn(&T) -> R + Send + Sync + 'static,
    {
        fn run(
            self,
            accessor: &Accessor<HostState>,
        ) -> impl std::future::Future<Output = wasmtime::Result<()>> + Send {
            let DrainTask {
                reader,
                sink,
                render,
            } = self;
            async move {
                accessor.with(|access| reader.pipe(access, DrainCommon::new(sink, render)))
            }
        }
    }
}

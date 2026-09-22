//! Shared harness for guestlang-host's integration suites (one copy of the
//! setup every test was hand-rolling):
//!
//! - FIXTURE PATHS — the demo-wasm location discipline in one place: the compiled Lean guests live
//!   under `lean/wasm-backend/target/` (repo root, NOT the crate's own `target/`), the
//!   spliced/composed artifacts and rustc guest builds under the repo `target/`, and the test-only
//!   fixtures under `tests/fixtures/`. Every path helper below is THE spelling of one artifact's
//!   location.
//! - SETUP — `canonicalize_or_skip` (the skip-if-unbuilt discipline) and `instantiate` (engine +
//!   capability set → a live [`ComponentRuntime`], the default GuestSetup shape). Per-test custom
//!   setups (the typed bindgen path, hot-reload's Router, the plain-core-module edgepython duel)
//!   stay in their suites.
//! - STREAM DRAIN — [`drain::DrainCommon`] / [`drain::DrainTask`]: the consumer = polled by the
//!   event loop as a BACKGROUND task (a sync pipe-set is never polled: the loop exits before
//!   pumping). Empty + not-finished = Pending — returning Dropped there ENDS the stream and the
//!   in-flight items are lost. Do not "simplify" that.
//! - HOUSE HELPERS — `fail` (no bare unwrap in tests), `tempdir`, `user_val`/`try_load` (the
//!   record-arg + artifact-loading preludes), the fixture-pair parser (`parse_pairs`), the fuzz
//!   PRNG ([`Lcg`]), the generated-manifest loader (`strip_header_comments` +
//!   `load_json_manifest`), and the wit-parser lookup trio (`wit::resolve_gateway` etc.).
//!
//! Ownership: crates/guestlang-host/tests/common/mod.rs. Additive to
//! src/**: nothing here touches it. The suites' ASSERTIONS stay in the
//! suites — the harness carries no expectations of its own.

// Per-binary compilation (each tests/*.rs includes this module) leaves
// most helpers unused in any given binary — the harness is the shared
// surface, not each inclusion.
#![allow(dead_code)]

use std::marker::PhantomData;
use std::path::Path;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::Mutex;
use std::task::Context;
use std::task::Poll;

use guestlang_host::CapabilitySet;
use guestlang_host::ComponentRuntime;
use guestlang_host::HostEngine;
use guestlang_host::HostState;
use wasmtime::StoreContextMut;
use wasmtime::component::Accessor;
use wasmtime::component::AccessorTask;
use wasmtime::component::Component;
use wasmtime::component::Lift;
use wasmtime::component::Source;
use wasmtime::component::StreamConsumer;
use wasmtime::component::StreamReader;
use wasmtime::component::StreamResult;
use wasmtime::component::Val;

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

/// The artifact-loading prelude every suite hand-rolled: canonicalize-
/// or-skip → engine → `load_component`. `skip_msg` prints verbatim
/// (`canonicalize_or_skip`'s wording — the pre-harness skip
/// diagnostics) when the artifact is absent; `Ok(None)` = the test
/// skips. `Err` = a REAL load failure — a built artifact that fails to
/// load is a test failure, never a skip.
pub fn try_load(
    path: &Path,
    skip_msg: &str,
) -> Result<Option<(HostEngine, Component)>, Box<dyn std::error::Error>> {
    let Some(path) = canonicalize_or_skip(path, skip_msg) else {
        return Ok(None);
    };
    let engine = HostEngine::new()?;
    let component = engine.load_component(&path)?;
    Ok(Some((engine, component)))
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

/// The user-record `Val` (the record-ARG convention: a record-valued
/// param crosses the boundary as the FLAT field list — id, name,
/// email, tags; the wasm_diff manifest rows adapt their string slice
/// to this typed form).
pub fn user_val(id: u64, name: &str, email: &str, tags: &[&str]) -> Val {
    Val::Record(vec![
        ("id".into(), Val::U64(id)),
        ("name".into(), Val::String(name.into())),
        ("email".into(), Val::String(email.into())),
        (
            "tags".into(),
            Val::List(tags.iter().map(|t| Val::String(t.to_string())).collect()),
        ),
    ])
}

// ── fixture-pair parsing (the snapshot differential + fuzz layer) ───

/// One generated pair: the snapshot text + the authority's parse dump
/// (format `SnapshotRT.fixtureFile` writes: `== u<i>` headers, `snap:`
/// and `expect:` sections).
pub struct Pair {
    pub name: String,
    pub snap: Vec<String>,
    pub expect: Vec<String>,
}

/// Split the fixture file into pairs. STRICT: content outside a
/// section (or before the first pair) is corruption, failed loudly.
pub fn parse_pairs(text: &str) -> Vec<Pair> {
    let mut pairs = Vec::new();
    // (name, snap lines, expect lines, section: 0=none 1=snap 2=expect)
    let mut cur: Option<(String, Vec<String>, Vec<String>, usize)> = None;
    for line in text.lines() {
        if let Some(name) = line.strip_prefix("== ") {
            if let Some((n, s, e, _)) = cur.take() {
                pairs.push(Pair {
                    name: n,
                    snap: s,
                    expect: e,
                });
            }
            cur = Some((name.to_string(), Vec::new(), Vec::new(), 0));
        } else if line == "snap:" {
            if let Some((_, _, _, sect)) = &mut cur {
                *sect = 1;
            }
        } else if line == "expect:" {
            if let Some((_, _, _, sect)) = &mut cur {
                *sect = 2;
            }
        } else if line.is_empty() || line.starts_with('#') {
            // header comment or blank — outside the sections
        } else if let Some((_, snap, expect, sect)) = &mut cur {
            match *sect {
                1 => snap.push(line.to_string()),
                2 => expect.push(line.to_string()),
                _ => fail(&format!("fixture: content outside a section: `{line}`")),
            }
        } else {
            fail(&format!("fixture: content before the first pair: `{line}`"));
        }
    }
    if let Some((n, s, e, _)) = cur.take() {
        pairs.push(Pair {
            name: n,
            snap: s,
            expect: e,
        });
    }
    pairs
}

// ── the fuzz layer's deterministic PRNG ─────────────────────────────

/// Deterministic small PRNG seeded from the fuzz input (FNV-1a over
/// the bytes, forced odd): the pair choice and mutation schedule are
/// pure functions of the input, so a printed `BOLERO_RANDOM_SEED`
/// replays exactly. Knuth consts; the draw order is pinned
/// (`from_bytes` → `next` → `below`) everywhere it is used.
pub struct Lcg(u64);

impl Lcg {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut seed = 0xcbf2_9ce4_8422_2325u64; // FNV offset basis
        for b in bytes {
            seed ^= u64::from(*b);
            seed = seed.wrapping_mul(0x0000_0100_0000_01b3);
        }
        Self(seed | 1)
    }

    pub fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 16
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

// ── the generated-manifest loader ───────────────────────────────────

/// Strip the GENERATED header (`//` comment lines) — serde_json
/// rejects them, and the header contract applies to every generated
/// artifact (the corrupted-manifest control needs the stripped TEXT
/// separately from the parsed value).
pub fn strip_header_comments(text: &str) -> String {
    text.lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Load + strip + parse a GENERATED JSON manifest: ONE strip + ONE
/// parse with ONE panic text — the loader every manifest-consuming
/// test shares.
pub fn load_json_manifest(path: &Path) -> serde_json::Value {
    let raw = std::fs::read_to_string(path).unwrap_or_else(|e| fail(&format!("manifest: {e}")));
    let json = strip_header_comments(&raw);
    serde_json::from_str(&json).unwrap_or_else(|e| fail(&format!("manifest parse: {e}")))
}

// ── wit-parser lookups (shared by the round-trip + byte-tie gates) ──

pub mod wit {
    use std::path::PathBuf;

    use wit_parser::Interface;
    use wit_parser::Resolve;
    use wit_parser::Type;
    use wit_parser::TypeDefKind;
    use wit_parser::TypeId;

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
    use super::Accessor;
    use super::AccessorTask;
    use super::Arc;
    use super::Context;
    use super::HostState;
    use super::Lift;
    use super::Mutex;
    use super::PhantomData;
    use super::Pin;
    use super::Poll;
    use super::Source;
    use super::StoreContextMut;
    use super::StreamConsumer;
    use super::StreamReader;
    use super::StreamResult;

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
            async move { accessor.with(|access| reader.pipe(access, DrainCommon::new(sink, render))) }
        }
    }
}

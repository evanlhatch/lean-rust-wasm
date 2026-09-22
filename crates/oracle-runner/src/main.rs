//! oracle-runner — the differential oracle's host-side driver + debug loop
//! (W6.3 phase 2).
//!
//! WHAT IT IS: the oracle manifest (lean/wasm-backend/target/diff.json —
//! Lean's own evals, the semantics authority) replayed against the emitted
//! component, with the comparison pushed INTO the oracle's terms: a mismatch
//! reports a VERDICT — the first-divergence triple (observed vs expected vs
//! the divergence CATEGORY, a ctor, never a string) — not a raw row dump.
//!
//! Subcommands:
//!   probe [--compare rows|verdict] [--manifest P] [--component P]
//!       Replay the whole manifest. rows mode (default): failures print as
//!       raw rows (the wasm_diff format). verdict mode: failures print as
//!       the structured verdict JSON (category + both outcomes + first
//!       payload offset + schema-surface echo).
//!   explain <row-index | fn:arg,arg,...> [--manifest P] [--component P]
//!       Rerun ONE oracle row with the full witness: the path, both
//!       outcomes, the divergence category, the first payload offset, the
//!       schema hash — plus the LEAN-side verdict (`oracle verdict …`) when
//!       the oracle exe is built (the cross-check: this mirror vs Lean's
//!       authority).
//!   schema-surface [--manifest P]
//!       Print the manifest-derived canonical schema surface + its sha256
//!       (the hash the verdicts echo; Lean owns the string —
//!       `lake exe oracle schema-surface` — consumers hash).
//!
//! The CompareMode/Outcome/verdict/classify code MIRRORS Oracle.lean
//! arm-for-arm (the same discipline as guestlang-host's wasm_diff.rs phase-1
//! mirror; Tests/Main.lean pins the Lean arms). The ser forms (ser_val)
//! MUST match Lean's `resultOf` byte-for-byte.
//!
//! Provenance: the replay machinery (the flat-arg conventions, the stream
//! drain) is lifted from guestlang-host/tests/wasm_diff.rs — kept honest by
//! both sides replaying the SAME byte-frozen manifest against the SAME
//! component. Skipped: the sabotage control (wasm_diff owns it).

// error! emits Error::provide — nightly-only (same gate as the root crate).
#![feature(error_generic_member_access)]

#[global_allocator]
static GLOBAL_ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll};
use fast_observe::exn::Fault;
use sha2::{Digest, Sha256};
use guestlang_host::bindings::GatewayUser;
use guestlang_host::{CapabilitySet, ComponentRuntime, HostState, HostEngine};
use wasmtime::StoreContextMut;
use wasmtime::component::{Source, StreamConsumer, StreamResult, Val};

// The driver's fault domain for its INPUT: the user-supplied oracle
// manifest (diff.json — `--manifest P` is arbitrary user input) and its
// rows' flat-arg conventions. O-space codes — the Lean faults registry
// owns E1xx; no collision. The replay machinery's own errors are NOT
// this type: they are wasmtime faults (guestlang-host's HostFault via
// HostResult) and a row's call error is an ORACLE OUTCOME (a trap
// identity), not a driver fault.
fast_observe::error! {
    /// An oracle-driver input fault: the manifest or a row is malformed.
    #[derive(Debug)]
    pub enum OracleFault {
        /// The oracle manifest (diff.json) is unreadable, malformed, or
        /// vacuous.
        #[error("oracle manifest: {detail}")]
        #[code = "O101", category = Content, advice = "regenerate diff.json (`just gen`); the manifest is the Lean authority's output"]
        Manifest {
            detail: String,
        },

        /// A manifest row's arg strings don't fit the flat-arg
        /// conventions (missing arg / non-numeric payload).
        #[error("oracle manifest row: {detail}")]
        #[code = "O102", category = Content, advice = "the row's args must match the manifest schema (fn/args/expected strings)"]
        RowArgs {
            detail: String,
        },
    }
}

/// The driver's fallible INPUT flow: fast-observe faults over
/// [`OracleFault`]. (main keeps its `Box<dyn Error>` Termination — the
/// debug loop's exit-code contract stays 1.)
type OracleResult<T> = fast_observe::Result<T, OracleFault>;

// ── the Oracle.lean mirror (CompareMode/Outcome/verdict) ─────────────

/// How a row's outcome is compared against the replay. Every row in the
/// current manifest binds `Full` (Oracle.lean's `modeOf`) — the other
/// arms stay: the mirror is the WHOLE truth table (the Lean side pins
/// every arm; the wire gains the mode column in a later phase).
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum CompareMode {
    /// Errors waive: an error on either side passes.
    Ignore,
    /// Compare error identity only — payloads never read.
    Identity,
    /// Compare identity AND payload, byte-for-byte (today's behavior).
    Full,
}

/// The error identity an outcome can carry. Mirrors `Oracle.ErrorId`;
/// the replay side's only identity today is `Trap` (a wasmtime trap
/// carries no payload the oracle may read). `UnknownFn`/`ArityDrift`
/// are the LEAN-side identities — constructed by the mirror's tests,
/// kept for the arm-for-arm truth table.
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ErrorId {
    UnknownFn,
    ArityDrift,
    Trap,
}

impl ErrorId {
    fn as_str(self) -> &'static str {
        match self {
            ErrorId::UnknownFn => "unknownFn",
            ErrorId::ArityDrift => "arityDrift",
            ErrorId::Trap => "trap",
        }
    }
}

/// One side of a comparison. Mirrors `Oracle.Outcome`.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Outcome {
    error: Option<ErrorId>,
    payload: String,
}

impl Outcome {
    fn value(s: String) -> Self {
        Outcome { error: None, payload: s }
    }
    fn trap() -> Self {
        Outcome { error: Some(ErrorId::Trap), payload: String::new() }
    }
}

/// The mode truth table — mirrors `Oracle.CompareMode.compare`
/// arm-for-arm.
fn compare(mode: CompareMode, expected: &Outcome, got: &Outcome) -> bool {
    use CompareMode::*;
    match (mode, expected.error, got.error) {
        (Ignore, Some(_), _) | (Ignore, _, Some(_)) => true,
        (Ignore, None, None) => expected.payload == got.payload,
        (Identity, Some(e), Some(f)) => e == f,
        (Identity, None, None) => true,
        (Identity, _, _) => false,
        (Full, Some(e), Some(f)) => e == f && expected.payload == got.payload,
        (Full, None, None) => expected.payload == got.payload,
        (Full, _, _) => false,
    }
}

/// The divergence category — mirrors `Oracle.DivergenceClass`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DivergenceCategory {
    ValueMismatch,
    ExpectedValueGotError,
    ExpectedErrorGotValue,
    ErrorIdentityMismatch,
    ErrorPayloadMismatch,
}

impl DivergenceCategory {
    fn as_str(self) -> &'static str {
        use DivergenceCategory::*;
        match self {
            ValueMismatch => "valueMismatch",
            ExpectedValueGotError => "expectedValueGotError",
            ExpectedErrorGotValue => "expectedErrorGotValue",
            ErrorIdentityMismatch => "errorIdentityMismatch",
            ErrorPayloadMismatch => "errorPayloadMismatch",
        }
    }
}

/// The first-divergence witness — mirrors `Oracle.Divergence`.
struct Divergence {
    expected: Outcome,
    observed: Outcome,
    category: DivergenceCategory,
    payload_diff_at: Option<usize>,
}

/// The first char offset at which two rendered payloads differ.
/// Mirrors `Oracle.firstDiffAt` (char-wise; the ser forms are ASCII).
fn first_diff_at(a: &str, b: &str) -> Option<usize> {
    let mut i = 0;
    let mut ac = a.chars();
    let mut bc = b.chars();
    loop {
        match (ac.next(), bc.next()) {
            (None, None) => return None,
            (None, Some(_)) | (Some(_), None) => return Some(i),
            (Some(x), Some(y)) if x == y => i += 1,
            (Some(_), Some(_)) => return Some(i),
        }
    }
}

/// Mirrors `Oracle.classify` — total over the failure arms of every mode.
fn classify(expected: &Outcome, observed: &Outcome) -> DivergenceCategory {
    use DivergenceCategory::*;
    match (expected.error, observed.error) {
        (None, None) => ValueMismatch,
        (None, Some(_)) => ExpectedValueGotError,
        (Some(_), None) => ExpectedErrorGotValue,
        (Some(e), Some(f)) => {
            if e == f { ErrorPayloadMismatch } else { ErrorIdentityMismatch }
        }
    }
}

/// The mode's verdict — mirrors `Oracle.CompareMode.verdict`: `None` =
/// pass, `Some(d)` = the first divergence.
fn verdict(mode: CompareMode, expected: &Outcome, observed: &Outcome) -> Option<Divergence> {
    if compare(mode, expected, observed) {
        None
    } else {
        Some(Divergence {
            expected: expected.clone(),
            observed: observed.clone(),
            category: classify(expected, observed),
            payload_diff_at: first_diff_at(&expected.payload, &observed.payload),
        })
    }
}

fn json_str(s: &str) -> String {
    // DELIBERATE INVARIANT (audit class (a)): serde_json's string
    // serialization is infallible by construction (no pending failure
    // state) — the expect documents that, never fires.
    serde_json::to_string(s).expect("string serializes")
}

fn outcome_json(o: &Outcome) -> String {
    let err = match o.error {
        None => "null".to_string(),
        Some(e) => json_str(e.as_str()),
    };
    format!("{{\"error\": {}, \"payload\": {}}}", err, json_str(&o.payload))
}

/// The verdict as JSON — mirrors `Oracle.jsonVerdict`'s shape byte-for-byte
/// (the schema echo = the canonical surface STRING; hash it consumer-side).
fn verdict_json(v: Option<&Divergence>, schema_surface: &str) -> String {
    match v {
        None => format!("{{\"ok\": true, \"schema\": {}}}", json_str(schema_surface)),
        Some(d) => {
            let at = match d.payload_diff_at {
                None => "null".to_string(),
                Some(n) => n.to_string(),
            };
            format!(
                "{{\"ok\": false, \"category\": {}, \"expected\": {}, \"observed\": {}, \"payload_diff_at\": {}, \"schema\": {}}}",
                json_str(d.category.as_str()),
                outcome_json(&d.expected),
                outcome_json(&d.observed),
                at,
                json_str(schema_surface)
            )
        }
    }
}

// ── the schema surface (derived from ANY manifest, first-occurrence
//    order — the same string `Oracle.schemaSurface` renders) ──────────

/// The sha256 of the schema surface — the hash the verdicts echo. The
/// hasher is LOCAL on purpose: guestlang-host's copy is the twin,
/// pinned by the triple-agreement test (the two must stay in lockstep).
fn schema_hash(surface: &str) -> String {
    let digest = Sha256::digest(surface.as_bytes());
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

/// One manifest row's string field — a missing/mistyped field is a
/// Manifest fault naming the row (was an index-panic on the expect).
fn row_str<'a>(row: &'a serde_json::Value, i: usize, key: &str) -> OracleResult<&'a str> {
    Ok(row[key]
        .as_str()
        .ok_or_else(|| {
            OracleFault::Manifest(Manifest {
                detail: format!("row {i}: missing `{key}` string"),
            })
        })?)
}

/// One manifest row's array field — same fault discipline as `row_str`.
fn row_arr<'a>(
    row: &'a serde_json::Value,
    i: usize,
    key: &str,
) -> OracleResult<&'a Vec<serde_json::Value>> {
    Ok(row[key]
        .as_array()
        .ok_or_else(|| {
            OracleFault::Manifest(Manifest {
                detail: format!("row {i}: missing `{key}` array"),
            })
        })?)
}

fn manifest_surface(rows: &[serde_json::Value]) -> OracleResult<String> {
    let mut seen: Vec<(String, usize)> = Vec::new();
    for (i, row) in rows.iter().enumerate() {
        let f = row_str(row, i, "fn")?.to_string();
        let n = row_arr(row, i, "args")?.len();
        if !seen.iter().any(|(g, _)| *g == f) {
            seen.push((f, n));
        }
    }
    Ok(seen
        .iter()
        .map(|(f, n)| format!("{f}/{n}"))
        .collect::<Vec<_>>()
        .join(","))
}

// ── the ser forms (MUST match Lean's `resultOf` byte-for-byte) ───────

fn ser_val(v: &Val) -> String {
    match v {
        Val::Bool(b) => {
            if *b { "1".into() } else { "0".into() }
        }
        Val::U8(n) => n.to_string(),
        Val::U16(n) => n.to_string(),
        Val::U32(n) => n.to_string(),
        Val::U64(n) => n.to_string(),
        Val::S8(n) => n.to_string(),
        Val::S16(n) => n.to_string(),
        Val::S32(n) => n.to_string(),
        Val::S64(n) => n.to_string(),
        Val::Float32(f) => f.to_string(),
        Val::Float64(f) => f.to_string(),
        Val::Char(c) => c.to_string(),
        Val::String(s) => s.clone(),
        Val::Option(None) => "none".into(),
        Val::Option(Some(inner)) => format!("some({})", ser_val(inner)),
        Val::Record(fields) => {
            let inner: Vec<String> =
                fields.iter().map(|(k, v)| format!("{k}={}", ser_val(v))).collect();
            format!("{{ {} }}", inner.join(", "))
        }
        Val::List(items) => {
            let inner: Vec<String> = items.iter().map(ser_val).collect();
            format!("({})", inner.join(","))
        }
        Val::Stream(_) => "<stream>".into(),
        other => format!("{other:?}"),
    }
}

// ── the flat-arg conventions (lifted from wasm_diff.rs) ──────────────

/// One flat arg, by index — a short row is a RowArgs fault naming the
/// missing slot, not a panic (was `.expect(...)` on user-supplied
/// manifest data).
fn arg<'a>(strs: &'a [&str], idx: usize, what: &str) -> OracleResult<&'a str> {
    Ok(strs.get(idx).ok_or_else(|| {
        OracleFault::RowArgs(RowArgs {
            detail: format!("missing arg #{idx} ({what}) — row too short"),
        })
    })?)
}

/// One flat arg → u64 (the oracle's boundary rows are u64-range); a
/// short or non-numeric arg is a RowArgs fault, not a panic (was
/// `.expect("user id")` etc. on user-supplied manifest data).
fn arg_u64(strs: &[&str], idx: usize, what: &str) -> OracleResult<u64> {
    let s = arg(strs, idx, what)?;
    s.parse::<u64>().map_err(|e| {
        OracleFault::RowArgs(RowArgs {
            detail: format!("arg #{idx} ({what}): `{s}` does not parse as u64: {e}"),
        })
        .into()
    })
}

/// One flat arg → f64 (the variant payload's f64 slot). Same discipline.
fn arg_f64(strs: &[&str], idx: usize, what: &str) -> OracleResult<f64> {
    let s = arg(strs, idx, what)?;
    s.parse::<f64>().map_err(|e| {
        OracleFault::RowArgs(RowArgs {
            detail: format!("arg #{idx} ({what}): `{s}` does not parse as f64: {e}"),
        })
        .into()
    })
}

/// The record-ARG convention: a record-valued param's row args = the
/// FIELD VALUES FLAT (id, name, email, tags comma-joined).
fn user_record(strs: &[&str]) -> OracleResult<Val> {
    Ok(Val::Record(vec![
        ("id".into(), Val::U64(arg_u64(strs, 0, "user id")?)),
        ("name".into(), Val::String(arg(strs, 1, "name")?.to_string())),
        ("email".into(), Val::String(arg(strs, 2, "email")?.to_string())),
        (
            "tags".into(),
            Val::List(
                arg(strs, 3, "tags")?
                    .split(',')
                    .map(|t| Val::String(t.to_string()))
                    .collect(),
            ),
        ),
    ]))
}

/// The VARIANT-ARG convention: [discr, payload] — the canonical-ABI
/// flat form (discr = the WIT case order; the payload rides the joined
/// i64 slot — u64 raw, f64 bits).
fn order_error_variant(strs: &[&str]) -> OracleResult<Val> {
    Ok(match arg(strs, 0, "order-error discr")? {
        "0" => Val::Variant("empty-cart".into(), None),
        "1" => Val::Variant(
            "invalid-item".into(),
            Some(Box::new(Val::U64(arg_u64(strs, 1, "invalid-item payload")?))),
        ),
        _ => Val::Variant(
            "insufficient-funds".into(),
            Some(Box::new(Val::Float64(arg_f64(
                strs,
                1,
                "insufficient-funds payload",
            )?))),
        ),
    })
}

fn build_args(f: &str, strs: &[&str]) -> OracleResult<Vec<Val>> {
    if f == "user-valid" || f == "user-complete" {
        Ok(vec![user_record(strs)?])
    } else if f == "order-error-valid" {
        Ok(vec![order_error_variant(strs)?])
    } else {
        strs.iter()
            .enumerate()
            .map(|(i, a)| -> OracleResult<Val> {
                match (f, i, *a) {
                    ("pick", 0, "0" | "1") => Ok(Val::Bool(*a == "1")),
                    (_, _, _) => Ok(Val::U64(arg_u64(strs, i, "u64 arg")?)),
                }
            })
            .collect()
    }
}

// ── the stream drain (lifted from wasm_diff.rs) ──────────────────────

struct DrainCommon<T, F> {
    out: Arc<Mutex<Vec<String>>>,
    render: F,
    _ty: std::marker::PhantomData<T>,
}
impl<T, F> StreamConsumer<HostState> for DrainCommon<T, F>
where
    T: wasmtime::component::Lift + Send + Sync + 'static,
    F: Fn(&T) -> String + Send + Sync + 'static,
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
        // DELIBERATE INVARIANT (audit class (a)): lock poisoning requires
        // a panic while HOLDING this lock — the section only drains into
        // the Vec (render is infallible string formatting), so the
        // poisoned state is unreachable.
        self.out.lock().unwrap().extend(buf.drain(..).map(move |t| render(&t)));
        Poll::Ready(Ok(StreamResult::Completed))
    }
}

// The concrete drains (documentation names for the two stream shapes).
#[allow(dead_code)]
type DrainU64 = DrainCommon<u64, fn(&u64) -> String>;
#[allow(dead_code)]
type DrainUser = DrainCommon<GatewayUser, fn(&GatewayUser) -> String>;

fn render_user(u: &GatewayUser) -> String {
    format!(
        "{{ id={}, name={}, email={}, tags=({}) }}",
        u.id,
        u.name,
        u.email,
        u.tags.join(",")
    )
}

struct DrainTaskU64 {
    reader: wasmtime::component::StreamReader<u64>,
    sink: Arc<Mutex<Vec<String>>>,
}
impl wasmtime::component::AccessorTask<HostState> for DrainTaskU64 {
    fn run(
        self,
        accessor: &wasmtime::component::Accessor<HostState>,
    ) -> impl std::future::Future<Output = wasmtime::Result<()>> + Send {
        let DrainTaskU64 { reader, sink } = self;
        async move {
            accessor.with(|access| {
                reader.pipe(
                    access,
                    DrainCommon { out: sink, render: |v: &u64| v.to_string(), _ty: Default::default() },
                )
            })
        }
    }
}

struct DrainTaskUser {
    reader: wasmtime::component::StreamReader<GatewayUser>,
    sink: Arc<Mutex<Vec<String>>>,
}
impl wasmtime::component::AccessorTask<HostState> for DrainTaskUser {
    fn run(
        self,
        accessor: &wasmtime::component::Accessor<HostState>,
    ) -> impl std::future::Future<Output = wasmtime::Result<()>> + Send {
        let DrainTaskUser { reader, sink } = self;
        async move {
            accessor.with(|access| {
                reader.pipe(
                    access,
                    DrainCommon { out: sink, render: render_user, _ty: Default::default() },
                )
            })
        }
    }
}

// ── the replay ───────────────────────────────────────────────────────

struct Row {
    f: String,
    args: Vec<String>,
    expected: String,
}

fn load_manifest(path: &std::path::Path) -> OracleResult<Vec<Row>> {
    // The io/serde errors ride the tree as wrapped originals AND in the
    // detail (the diagnostic carries the phase + cause).
    let raw = std::fs::read_to_string(path).map_err(|e| {
        let detail = format!("read: {e}");
        Fault::new(e).wrap(OracleFault::Manifest(Manifest { detail }))
    })?;
    let rows: Vec<serde_json::Value> = serde_json::from_str(&raw).map_err(|e| {
        let detail = format!("parse: {e}");
        Fault::new(e).wrap(OracleFault::Manifest(Manifest { detail }))
    })?;
    if rows.len() < 100 {
        return Err(OracleFault::Manifest(Manifest {
            detail: format!("only {} rows — vacuous", rows.len()),
        })
        .into());
    }
    let mut out = Vec::with_capacity(rows.len());
    for (i, r) in rows.iter().enumerate() {
        let args = row_arr(r, i, "args")?
            .iter()
            .map(|a| {
                a.as_str()
                    .map(str::to_string)
                    .ok_or_else(|| {
                        OracleFault::Manifest(Manifest {
                            detail: format!("row {i}: non-string `args` element"),
                        })
                    })
            })
            .collect::<core::result::Result<Vec<String>, OracleFault>>()?;
        out.push(Row {
            f: row_str(r, i, "fn")?.to_string(),
            args,
            expected: row_str(r, i, "expected")?.to_string(),
        });
    }
    Ok(out)
}

/// Replay ONE row against the instantiated component. The outcome is
/// the ser form or a Trap identity (payload-free — see wasm_diff).
async fn replay_row(
    rt: &mut ComponentRuntime,
    f: &str,
    args: &[Val],
) -> Result<Outcome, Box<dyn std::error::Error>> {
    if f == "watch-counts" || f == "watch-users" {
        // the STREAM rows: the call + the drain in ONE event loop (a
        // post-call drain never gets polled — the loop already exited).
        let out = Arc::new(Mutex::new(Vec::new()));
        // DELIBERATE INVARIANT (audit class (a)): replay_row runs only
        // after `rt.instantiate` (probe/explain) — a missing instance is
        // a driver bug, not an input condition.
        let instance = rt.instance().expect("instance").clone();
        let is_counts = f == "watch-counts";
        let fname = f.to_string();
        let args: Vec<Val> = args.to_vec();
        let sink = out.clone();
        rt.store_mut()
            .run_concurrent(async move |accessor| {
                // The export's existence is DATA-driven (the row's fn
                // must exist on the component) — a named error, not a
                // panic (was `.expect("export")`).
                let f = accessor
                    .with(|access| instance.get_func(access, &fname))
                    .ok_or_else(|| {
                        wasmtime::Error::msg(format!(
                            "oracle replay: export `{fname}` missing on the component"
                        ))
                    })?;
                let mut results = [if is_counts { Val::U64(0) } else { Val::List(vec![]) }];
                f.call_concurrent(accessor, &args, &mut results).await?;
                let any = match results[0].clone() {
                    Val::Stream(a) => a,
                    other => {
                        // The row's result type isn't the stream the
                        // drain expects — named error, not a panic
                        // (was `panic!("{fname}: not a stream")`).
                        return Err(wasmtime::Error::msg(format!(
                            "{fname}: not a stream: {other:?}"
                        )));
                    }
                };
                if is_counts {
                    let reader = any.try_into_stream_reader::<u64>()?;
                    accessor.spawn(DrainTaskU64 { reader, sink })?.await;
                } else {
                    let reader = any.try_into_stream_reader::<GatewayUser>()?;
                    accessor.spawn(DrainTaskUser { reader, sink })?.await;
                }
                Ok::<(), wasmtime::Error>(())
            })
            .await??;
        // DELIBERATE INVARIANT (audit class (a)): poisoning requires a
        // panic while holding this lock — only the infallible render
        // runs inside; see DrainCommon::poll_consume.
        let items = out.lock().unwrap();
        Ok(Outcome::value(format!(
            "({})",
            items.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(",")
        )))
    } else {
        match rt.call(f, args).await {
            Ok(results) => match results.into_iter().next() {
                Some(v) => Ok(Outcome::value(ser_val(&v))),
                None => Ok(Outcome::value("?".into())),
            },
            Err(_) => Ok(Outcome::trap()),
        }
    }
}

// ── the CLI ──────────────────────────────────────────────────────────

fn repo_path(rel: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").join(rel)
}

struct Cli {
    manifest: std::path::PathBuf,
    component: std::path::PathBuf,
    rest: Vec<String>,
}

fn parse_flags(args: &[String]) -> Result<Cli, String> {
    let mut cli = Cli {
        manifest: repo_path("lean/wasm-backend/target/diff.json"),
        component: repo_path("lean/wasm-backend/target/demo.component.wasm"),
        rest: Vec::new(),
    };
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--manifest" => {
                i += 1;
                cli.manifest = args.get(i).ok_or("--manifest needs a path")?.into();
            }
            "--component" => {
                i += 1;
                cli.component = args.get(i).ok_or("--component needs a path")?.into();
            }
            other => cli.rest.push(other.to_string()),
        }
        i += 1;
    }
    Ok(cli)
}

const USAGE: &str = "oracle-runner — the differential oracle's host-side driver (W6.3 phase 2)
usage:
  oracle-runner probe [--compare rows|verdict] [--manifest P] [--component P]
  oracle-runner explain <row-index | fn:arg,arg,...> [--manifest P] [--component P]
  oracle-runner schema-surface [--manifest P]";

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = argv.first() else {
        eprintln!("{USAGE}");
        std::process::exit(2);
    };
    let cli = parse_flags(&argv[1..]).map_err(|e| format!("{e}\n{USAGE}"))?;
    match cmd.as_str() {
        "schema-surface" => {
            let rows: Vec<serde_json::Value> =
                serde_json::from_str(&std::fs::read_to_string(&cli.manifest)?)?;
            let surface = manifest_surface(&rows)?;
            println!("{surface}");
            println!("sha256: {}", schema_hash(&surface));
            Ok(())
        }
        "probe" => {
            let compare_as: &str = match cli.rest.first().map(String::as_str) {
                None => "rows",
                Some("--compare") => cli.rest.get(1).map(String::as_str).ok_or(USAGE)?,
                Some(_) => return Err(USAGE.into()),
            };
            if compare_as != "rows" && compare_as != "verdict" {
                return Err(USAGE.into());
            }
            let rows_json: Vec<serde_json::Value> =
                serde_json::from_str(&std::fs::read_to_string(&cli.manifest)?)?;
            let surface = manifest_surface(&rows_json)?;
            let rows = load_manifest(&cli.manifest)?;
            let engine = HostEngine::new()?;
            let component =
                engine.load_component_bytes(&std::fs::read(&cli.component)?)?;
            let mut rt = ComponentRuntime::new(engine, CapabilitySet::NONE).await?;
            rt.instantiate(&component).await?;
            let mut failures = 0usize;
            for row in &rows {
                let strs: Vec<&str> = row.args.iter().map(String::as_str).collect();
                let args = build_args(&row.f, &strs)?;
                let expected = Outcome::value(row.expected.clone());
                let got = replay_row(&mut rt, &row.f, &args).await?;
                if compare_as == "rows" {
                    if !compare(CompareMode::Full, &expected, &got) {
                        failures += 1;
                        println!(
                            "{} {:?}: expected {}, got {}",
                            row.f,
                            row.args,
                            expected.payload,
                            match got.error {
                                Some(e) => format!("TRAP({})", e.as_str()),
                                None => got.payload.clone(),
                            }
                        );
                    }
                } else if let Some(d) = verdict(CompareMode::Full, &expected, &got) {
                    failures += 1;
                    println!("{}", verdict_json(Some(&d), &surface));
                }
            }
            eprintln!(
                "probe: {} rows, {} failed, schema sha256 {}",
                rows.len(),
                failures,
                schema_hash(&surface)
            );
            if failures > 0 {
                std::process::exit(1);
            }
            Ok(())
        }
        "explain" => {
            let id = cli.rest.first().ok_or(USAGE)?;
            let rows_json: Vec<serde_json::Value> =
                serde_json::from_str(&std::fs::read_to_string(&cli.manifest)?)?;
            let surface = manifest_surface(&rows_json)?;
            let rows = load_manifest(&cli.manifest)?;
            let (idx, row) = match id.parse::<usize>() {
                Ok(i) => {
                    let row = rows.get(i).ok_or(format!("no row #{i} ({} rows)", rows.len()))?;
                    (i, row)
                }
                Err(_) => {
                    let (f, args) = id.split_once(':').ok_or("explain id: row-index or fn:arg,arg,...")?;
                    let want: Vec<String> =
                        if args.is_empty() { vec![] } else { args.split(',').map(str::to_string).collect() };
                    rows.iter()
                        .enumerate()
                        .find(|(_, r)| r.f == f && r.args == want)
                        .ok_or(format!("no row {id}"))?
                }
            };
            let engine = HostEngine::new()?;
            let component =
                engine.load_component_bytes(&std::fs::read(&cli.component)?)?;
            let mut rt = ComponentRuntime::new(engine, CapabilitySet::NONE).await?;
            rt.instantiate(&component).await?;
            let strs: Vec<&str> = row.args.iter().map(String::as_str).collect();
            let args = build_args(&row.f, &strs)?;
            let expected = Outcome::value(row.expected.clone());
            let got = replay_row(&mut rt, &row.f, &args).await?;
            let v = verdict(CompareMode::Full, &expected, &got);
            println!("explain: row #{idx}  fn={} args={:?}", row.f, row.args);
            println!("  expected: {}", outcome_json(&expected));
            println!("  observed: {}", outcome_json(&got));
            match &v {
                None => println!("  verdict: ok"),
                Some(d) => println!(
                    "  verdict: MISMATCH category={} payload_diff_at={}",
                    d.category.as_str(),
                    d.payload_diff_at.map(|n| n.to_string()).unwrap_or_else(|| "null".into())
                ),
            }
            println!("  schema: sha256({}) = {}", surface, schema_hash(&surface));
            // the LEAN-side cross-check (the authority's own verdict) —
            // when the oracle exe is built.
            let oracle_exe = repo_path("lean/wasm-backend/.lake/build/bin/oracle");
            if oracle_exe.exists() {
                let observed_arg = match got.error {
                    Some(_) => "@trap".to_string(),
                    None => got.payload.clone(),
                };
                let out = std::process::Command::new(&oracle_exe)
                    .arg("verdict")
                    .arg(&row.f)
                    .args(&row.args)
                    .arg("--observed")
                    .arg(&observed_arg)
                    .output()?;
                println!("  lean-oracle: {}", String::from_utf8_lossy(&out.stdout).trim());
                if !out.status.success() {
                    eprintln!(
                        "  lean-oracle exited {}: {}",
                        out.status,
                        String::from_utf8_lossy(&out.stderr)
                    );
                }
            } else {
                println!("  lean-oracle: not built (lake build oracle) — mirror-only verdict");
            }
            if v.is_some() {
                std::process::exit(1);
            }
            Ok(())
        }
        _ => {
            eprintln!("{USAGE}");
            std::process::exit(2);
        }
    }
}

// ── the mirror's pins (the Lean side pins the same arms in
//    Tests/Main.lean) ─────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Outcome {
        Outcome::value(s.to_string())
    }
    fn e(id: ErrorId, p: &str) -> Outcome {
        Outcome { error: Some(id), payload: p.to_string() }
    }

    #[test]
    fn verdict_truth_table_mirrors_lean() {
        use CompareMode::*;
        use DivergenceCategory::*;
        let va = v("42");
        let vb = v("43");
        let eu = e(ErrorId::UnknownFn, "oracle row: unknown fn 'doble'");
        let ea1 = e(ErrorId::ArityDrift, "oracle row: 'double' expects 1 args, got 2");
        let ea2 = e(ErrorId::ArityDrift, "oracle row: 'total' expects 3 args, got 1");
        // pass → None
        assert!(verdict(Full, &va, &va).is_none());
        assert!(verdict(Identity, &va, &vb).is_none());
        assert!(verdict(Identity, &ea1, &ea2).is_none());
        assert!(verdict(Ignore, &eu, &va).is_none());
        // fail → the category names the divergence KIND
        assert_eq!(verdict(Full, &va, &vb).map(|d| d.category), Some(ValueMismatch));
        assert_eq!(verdict(Full, &va, &eu).map(|d| d.category), Some(ExpectedValueGotError));
        assert_eq!(verdict(Full, &eu, &va).map(|d| d.category), Some(ExpectedErrorGotValue));
        assert_eq!(verdict(Full, &eu, &ea1).map(|d| d.category), Some(ErrorIdentityMismatch));
        assert_eq!(verdict(Full, &ea1, &ea2).map(|d| d.category), Some(ErrorPayloadMismatch));
        assert_eq!(verdict(Identity, &eu, &ea1).map(|d| d.category), Some(ErrorIdentityMismatch));
        assert_eq!(verdict(Ignore, &va, &vb).map(|d| d.category), Some(ValueMismatch));
    }

    #[test]
    fn first_diff_at_mirrors_lean() {
        assert_eq!(first_diff_at("42", "43"), Some(1));
        assert_eq!(first_diff_at("abc", "abd"), Some(2));
        assert_eq!(first_diff_at("abc", "abc"), None);
        assert_eq!(first_diff_at("abc", "ab"), Some(2));
        assert_eq!(
            first_diff_at(
                "oracle row: unknown fn 'doble'",
                "oracle row: 'double' expects 1 args, got 2"
            ),
            Some(12)
        );
    }

    #[test]
    fn verdict_json_shape_mirrors_lean() {
        let d = verdict(CompareMode::Full, &v("42"), &v("43")).expect("mismatch");
        let surface = "double/1,is-big/1";
        assert_eq!(
            verdict_json(Some(&d), surface),
            "{\"ok\": false, \"category\": \"valueMismatch\", \"expected\": {\"error\": null, \"payload\": \"42\"}, \"observed\": {\"error\": null, \"payload\": \"43\"}, \"payload_diff_at\": 1, \"schema\": \"double/1,is-big/1\"}"
        );
        assert_eq!(
            verdict_json(None, surface),
            "{\"ok\": true, \"schema\": \"double/1,is-big/1\"}"
        );
    }

    #[test]
    fn surface_derivation_is_first_occurrence_order() {
        let rows: Vec<serde_json::Value> = serde_json::from_str(
            r#"[{"fn":"double","args":["3"],"expected":"6"},
                {"fn":"user-valid","args":["0","zero","0@g.dev","a"],"expected":"0"},
                {"fn":"double","args":["4"],"expected":"8"}]"#,
        )
        .expect("rows");
        assert_eq!(
            manifest_surface(&rows).expect("valid manifest rows"),
            "double/1,user-valid/4"
        );
    }
}

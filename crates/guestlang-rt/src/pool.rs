//! Worker pool — the "Monty pattern" for untrusted runs.
//!
//! CREDIT + SCOPE: the API shape is the Monty worker-pool pattern (a
//! job goes in, a value or a killed-Err comes out, the pool replen-
//! ishes and keeps serving). This is NOT the Monty crate — it is this
//! crate's own honest v1 of that shape, with zero new dependencies
//! (std::thread + std::sync::mpsc only).
//!
//! THE HONEST V1 ISOLATION MODEL — thread-pool + engine-level limits,
//! NOT process isolation:
//!
//! * Each job runs on a pooled worker thread with its OWN wasmi
//!   `Engine` + `Store` (`Runtime::new` per job — see `execute`). The
//!   wasmi 2.0 `Engine` is `Send + Sync` (compile-time pinned below),
//!   so sharing a compiled module across workers is a valid future
//!   optimization; v1 compiles per job and takes the strongest
//!   isolation available in-process: no state survives a job, so a
//!   trapped/OOM/panicked job cannot poison the next one.
//! * The caps are wasmi's ENFORCED deterministic limits: fuel (the
//!   job's budget), the refused feature set (no floats/simd/memory64 —
//!   `Runtime::new`), and the engine's enforced limits. A runaway
//!   guest dies on fuel, deterministically.
//! * TIMEOUT: wasmi has no epoch/wall-clock preemption. The job's
//!   FUEL is the deterministic timeout proxy — `PoolError::OutOfFuel`
//!   IS the v1 timeout. `PoolError::OutOfTime` is reserved for the
//!   follow-up (see below). A wall-clock deadline would require
//!   either epochs or killing a worker thread — the latter leaks the
//!   store, so v1 refuses to fake it.
//! * PANIC containment: job execution is wrapped in `catch_unwind`;
//!   a panicking job answers `PoolError::Trapped` and the worker
//!   keeps serving. (wasmi itself is panic-free on traps; this is
//!   belt-and-braces for host-code regressions.)
//!
//! KNOWN LIMIT (documented, deliberate): threads share an address
//! space — a UB bug in the ENGINE (not the guest) could corrupt the
//! pool. Hard process isolation (re-spawning a worker SUBPROCESS —
//! the same binary re-invoked with a `--worker` flag) is the
//! documented follow-up and requires a binary-crate companion; a
//! library crate has no `main` to re-invoke. Until then the
//! deterministic fuel/limits caps are the crash containment.
//!
//! THE TWO MODES (the limit above is FIXED as of the subprocess lane:
//! this crate now HAS the binary companion — `src/bin/worker.rs`):
//!
//! | mode | constructor | job substrate | isolation | wall-clock deadline |
//! |------|-------------|---------------|-----------|---------------------|
//! | soft | `Pool::new` | pooled THREAD, private wasmi engine per job | in-process: no state survives a job, but a UB bug in the ENGINE could corrupt the pool (threads share an address space) | NOT enforceable — killing a thread leaks the store; fuel is the deterministic timeout proxy (`OutOfFuel`); `OutOfTime` unused |
//! | hard | `Pool::new_hard` | fresh SUBPROCESS per job (`worker --fuel N`, spawn-per-job — the process is born and dies with the job) | OS process: trap/OOM/panic tears down nothing but that child | LIVE — the parent polls `try_wait` against the deadline and `kill()`s the child: `PoolError::OutOfTime` |
//!
//! TRADE-OFF: hard mode pays a process spawn + serialize per job
//! (module bytes cross the boundary as base64 on the child's stdin —
//! the worker protocol is documented in `bin/worker.rs`) and buys
//! OS-grade crash containment plus the REAL wall-clock kill. Soft
//! mode is the low-latency default; hard mode is for genuinely
//! hostile jobs and the hang-proof guarantee.
//!
//! Worker-binary resolution (hard mode): the `GUESTLANG_RT_WORKER`
//! env override, then cargo's `CARGO_BIN_EXE_worker` (set
//! automatically for this crate's own integration tests). A hard pool
//! that cannot locate the binary answers `PoolError::BadModule` at
//! run time — `new_hard` itself stays infallible.

use std::io::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::Runtime;

// The checked claim the isolation model rests on: the wasmi Engine is
// usable from multiple threads (module sharing = the future opt). If
// an upstream release drops Send/Sync, this fails to COMPILE — the
// pool's docs go stale the same day the claim does.
const _: () = {
    const fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<wasmi::Engine>();
};

/// One unit of untrusted work: compile `wasm`, call export `func`
/// with `args` (the scalar-ABI i64s), under `fuel` — the deterministic
/// budget AND the v1 timeout proxy.
pub struct Job {
    /// The compiled CORE wasm module. `Arc<[u8]>` so one hot module
    /// can be fanned out to every worker without a copy.
    pub wasm: Arc<[u8]>,
    /// The export to invoke.
    pub func: String,
    /// The scalar-ABI args (same coercion as `invoke_core`).
    pub args: Vec<i64>,
    /// Fuel endowment: the deterministic bound on the run. Exhausted
    /// → `PoolError::OutOfFuel` (the v1 timeout).
    pub fuel: u64,
}

/// The job's outcome or the reason it was killed.
#[derive(Debug)]
pub enum PoolError {
    /// The module failed to LOAD, or does not expose `func` at the
    /// requested arity — the job's surface doesn't match the module's.
    BadModule(String),
    /// Fuel exhausted: the deterministic cap fired. This is the v1
    /// TIMEOUT (wasmi has no epoch; fuel is the only preemption).
    OutOfFuel,
    /// The guest trapped (or the worker executing it panicked — the
    /// message says which). The pool survives either way.
    Trapped(String),
    /// LIVE in HARD mode only: the job blew its wall-clock deadline,
    /// the worker SUBPROCESS was killed, the pool survived. In soft
    /// mode this variant is still never produced (threads cannot be
    /// preempted — see the mode table in the header).
    OutOfTime,
}

impl std::fmt::Display for PoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BadModule(m) => write!(f, "bad module: {m}"),
            Self::OutOfFuel => write!(f, "out of fuel (the deterministic timeout proxy)"),
            Self::Trapped(m) => write!(f, "trapped: {m}"),
            Self::OutOfTime => write!(
                f,
                "out of time (hard mode: the worker was killed at the deadline)"
            ),
        }
    }
}
impl std::error::Error for PoolError {}

struct Submitted {
    job: Job,
    // HARD mode only: the wall-clock deadline for this job. Soft mode
    // cannot enforce one (see the mode table) and ignores it.
    timeout: Option<Duration>,
    reply: mpsc::Sender<Result<Vec<i64>, PoolError>>,
}

/// A pool of `workers` threads, each executing jobs in a private
/// wasmi engine. Replenishing: failed jobs free their worker; the
/// pool serves until dropped.
pub struct Pool {
    tx: Option<mpsc::Sender<Submitted>>,
    handles: Vec<std::thread::JoinHandle<()>>,
    workers: usize,
    in_flight: Arc<AtomicUsize>,
    max_in_flight: Arc<AtomicUsize>,
    // soft = in-process threads; hard = a fresh worker SUBPROCESS per
    // job (see the mode table in the header).
    hard: bool,
}

impl Pool {
    /// Spawn `workers` worker threads. `workers == 0` is treated as 1
    /// (a pool that cannot run anything is a footgun, not a feature).
    /// Thread spawn failure panics, matching `std::thread::spawn`.
    pub fn new(workers: usize) -> Self {
        let workers = workers.max(1);
        let (tx, rx) = mpsc::channel::<Submitted>();
        let rx = Arc::new(Mutex::new(rx));
        let in_flight = Arc::new(AtomicUsize::new(0));
        let max_in_flight = Arc::new(AtomicUsize::new(0));
        let handles = Self::spawn_workers(&rx, &in_flight, &max_in_flight, workers, false);
        Self {
            tx: Some(tx),
            handles,
            workers,
            in_flight,
            max_in_flight,
            hard: false,
        }
    }

    /// The HARD mode: same dispatcher, but every job runs in a FRESH
    /// worker SUBPROCESS (`src/bin/worker.rs`, spawn-per-job — the
    /// process is born and dies with the job, so isolation is maximal
    /// and the wall-clock deadline is LIVE: a hung job is `kill()`ed
    /// at the deadline and answers `PoolError::OutOfTime`). See the
    /// mode table in the header for the trade-off (spawn + serialize
    /// per job, vs OS-grade crash containment).
    pub fn new_hard(workers: usize) -> Self {
        let workers = workers.max(1);
        let (tx, rx) = mpsc::channel::<Submitted>();
        let rx = Arc::new(Mutex::new(rx));
        let in_flight = Arc::new(AtomicUsize::new(0));
        let max_in_flight = Arc::new(AtomicUsize::new(0));
        let handles = Self::spawn_workers(&rx, &in_flight, &max_in_flight, workers, true);
        Self {
            tx: Some(tx),
            handles,
            workers,
            in_flight,
            max_in_flight,
            hard: true,
        }
    }

    /// The shared dispatcher loop: the mode only changes HOW one job
    /// executes, not how jobs are handed out — capacity semantics are
    /// identical (the same negative control pins both modes).
    fn spawn_workers(
        rx: &Arc<Mutex<mpsc::Receiver<Submitted>>>,
        in_flight: &Arc<AtomicUsize>,
        max_in_flight: &Arc<AtomicUsize>,
        workers: usize,
        hard: bool,
    ) -> Vec<std::thread::JoinHandle<()>> {
        let mut handles = Vec::with_capacity(workers);
        for w in 0..workers {
            let rx = Arc::clone(rx);
            let in_flight = Arc::clone(in_flight);
            let max_in_flight = Arc::clone(max_in_flight);
            handles.push(
                std::thread::Builder::new()
                    .name(format!("guestlang-pool-{w}"))
                    .spawn(move || {
                        loop {
                            let submitted = {
                                let rx = rx.lock().unwrap();
                                // Sender dropped = pool dropped = worker exits.
                                match rx.recv() {
                                    Ok(s) => s,
                                    Err(_) => break,
                                }
                            };
                            in_flight.fetch_add(1, Ordering::SeqCst);
                            max_in_flight
                                .fetch_max(in_flight.load(Ordering::SeqCst), Ordering::SeqCst);
                            let out = catch_unwind(AssertUnwindSafe(|| {
                                if hard {
                                    execute_hard(&submitted.job, submitted.timeout)
                                } else {
                                    execute(&submitted.job)
                                }
                            }))
                            .unwrap_or_else(|_| {
                                Err(PoolError::Trapped(
                                    "worker panicked while executing the job \
                                     (caught; the pool survives)"
                                        .into(),
                                ))
                            });
                            in_flight.fetch_sub(1, Ordering::SeqCst);
                            let _ = submitted.reply.send(out);
                        }
                    })
                    .expect("guestlang-rt pool: worker thread spawn failed"),
            );
        }
        handles
    }

    /// The configured worker count.
    pub fn workers(&self) -> usize {
        self.workers
    }

    /// The pool's mode: `true` = HARD (a fresh worker SUBPROCESS per
    /// job — see the mode table in the header), `false` = soft
    /// (in-process threads).
    pub fn is_hard(&self) -> bool {
        self.hard
    }

    /// Jobs executing RIGHT NOW (the capacity watermark's live half —
    /// the negative control in `tests/pool.rs` pins it).
    pub fn in_flight(&self) -> usize {
        self.in_flight.load(Ordering::SeqCst)
    }

    /// Peak concurrent executions observed — the capacity's proof:
    /// never above `workers()`, and it REACHES `workers()` under load.
    pub fn max_in_flight(&self) -> usize {
        self.max_in_flight.load(Ordering::SeqCst)
    }

    /// Dispatch `job` to a free worker and block until it answers.
    /// Concurrent callers queue: the pool's capacity is `workers()`,
    /// no matter how many threads call `run`.
    ///
    /// HARD mode: no wall-clock deadline (run unbounded — pair with
    /// `run_timeout` when the job is untrusted).
    pub fn run(&self, job: Job) -> Result<Vec<i64>, PoolError> {
        self.submit(job, None)
    }

    /// `run` with a WALL-CLOCK DEADLINE. HARD mode: enforced for real —
    /// at the deadline the worker subprocess is killed and the answer
    /// is `PoolError::OutOfTime` (the guarantee the soft mode could
    /// not make — see the mode table). SOFT mode: the deadline is
    /// IGNORED (a thread cannot be preempted without leaking its
    /// store) — fuel remains the soft timeout proxy; the method exists
    /// so callers keep one call-site across modes.
    pub fn run_timeout(&self, job: Job, timeout: Duration) -> Result<Vec<i64>, PoolError> {
        self.submit(job, Some(timeout))
    }

    fn submit(&self, job: Job, timeout: Option<Duration>) -> Result<Vec<i64>, PoolError> {
        let (reply_tx, reply_rx) = mpsc::channel();
        let tx = self
            .tx
            .as_ref()
            .expect("pool: sender dropped while running");
        tx.send(Submitted {
            job,
            timeout,
            reply: reply_tx,
        })
        .map_err(|_| PoolError::Trapped("pool: worker gone (pool is shutting down)".into()))?;
        // Err here = the worker DIED holding the reply sender: the
        // catch_unwind above makes that near-impossible (panics are
        // caught), so this is the loud residual, not the expected path.
        reply_rx
            .recv()
            .map_err(|_| PoolError::Trapped("pool: worker died without answering".into()))?
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        // Drop the sender: every worker's recv() disconnects → exit.
        self.tx = None;
        for h in self.handles.drain(..) {
            let _ = h.join();
        }
    }
}

/// Execute one job in the CALLING worker's context: a private engine,
/// store, and instance per job — nothing survives the call.
fn execute(job: &Job) -> Result<Vec<i64>, PoolError> {
    let mut rt =
        Runtime::new(&job.wasm, job.fuel).map_err(|e| PoolError::BadModule(e.0.clone()))?;
    rt.call(&job.func, &job.args, job.fuel)
        .map(|(out, _)| out)
        .map_err(|e| classify(e.0))
}

/// Map the rt's string-carried error onto the pool's taxonomy.
/// The CONTRACT with `lib.rs`'s formatting: wasmi out-of-fuel surfaces
/// "fuel" in every wasmi 2.0 variant (TrapCode display "all fuel
/// consumed by WebAssembly"; FuelError "…of fuel…"); a missing export
/// or arity mismatch is rt's "no export"/"arity" prefix; everything
/// else is a guest trap. (The existing conformance test already pins
/// the "wasmi: …" message channel — this classifier sits on the same
/// seam, and the pool's tests pin each arm.)
fn classify(msg: String) -> PoolError {
    if msg.to_lowercase().contains("fuel") {
        PoolError::OutOfFuel
    } else if msg.starts_with("no export") || msg.starts_with("arity") {
        PoolError::BadModule(msg)
    } else {
        PoolError::Trapped(msg)
    }
}

// ── HARD MODE: the subprocess execution ──────────────────────────────
// One `src/bin/worker.rs` process per job; the protocol (argv / stdin
// JSON / stdout JSON / exit codes) is documented in the binary's
// header and pinned by the hard-mode tests in `tests/pool.rs`.

/// The worker binary's exit-code vocabulary (mirrored in
/// `bin/worker.rs`; 101 is std's own panic code).
const WORKER_EXIT_TRAP: i32 = 1;
const WORKER_EXIT_FUEL: i32 = 2;
const WORKER_EXIT_BAD_MODULE: i32 = 3;

/// Locate the worker binary: the `GUESTLANG_RT_WORKER` override, then
/// cargo's `CARGO_BIN_EXE_worker` (set for this crate's own
/// integration tests). Outside tests, an embedder sets the env var.
fn worker_bin() -> Result<std::path::PathBuf, String> {
    if let Ok(p) = std::env::var("GUESTLANG_RT_WORKER") {
        return Ok(std::path::PathBuf::from(p));
    }
    if let Ok(p) = std::env::var("CARGO_BIN_EXE_worker") {
        return Ok(std::path::PathBuf::from(p));
    }
    Err(
        "guestlang-rt: hard pool cannot locate the worker binary — set \
         GUESTLANG_RT_WORKER (cargo sets CARGO_BIN_EXE_worker for this crate's tests)"
            .into(),
    )
}

/// Execute one job in a FRESH worker subprocess: spawn, serialize the
/// job as JSON on the child's stdin, wait (bounded by `timeout` when
/// set — a hit deadline = `kill` = `OutOfTime`), classify by exit
/// code + stdout. Nothing the child does can outlive this function:
/// the process is reaped or killed on every path.
fn execute_hard(job: &Job, timeout: Option<Duration>) -> Result<Vec<i64>, PoolError> {
    let bin = worker_bin().map_err(PoolError::BadModule)?;
    let mut child = Command::new(&bin)
        .arg("--fuel")
        .arg(job.fuel.to_string())
        // v1: parsed + echoed by the worker, not engine-enforced —
        // fuel already bounds memory growth deterministically (see
        // the binary's header).
        .arg("--mem-bytes")
        .arg("0")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| PoolError::Trapped(format!("worker spawn failed: {e}")))?;

    // The job payload: module bytes as base64 (the process boundary
    // carries JSON, not Arcs). The write runs on its own thread so a
    // payload larger than the pipe buffer cannot deadlock the wait.
    let payload = serde_json::json!({
        "wasm-b64": b64_encode(&job.wasm),
        "func": job.func,
        "args": job.args,
    })
    .to_string();
    let mut stdin = child.stdin.take().expect("piped stdin");
    std::thread::spawn(move || {
        let _ = stdin.write_all(payload.as_bytes());
        // dropping closes the pipe: the worker's read_to_string ends
    });

    // The answer: read on its own thread (read_to_string blocks until
    // the child closes stdout — death or exit both close it).
    let mut stdout = child.stdout.take().expect("piped stdout");
    let reader = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = std::io::Read::read_to_string(&mut stdout, &mut s);
        s
    });

    // The wait. Stable std has no `wait_timeout`, so: poll `try_wait`
    // against the deadline — the poll granularity IS the kill
    // latency. This is the wall-clock enforcement the soft mode's
    // header said threads could not provide.
    let status = match timeout {
        None => child
            .wait()
            .map_err(|e| PoolError::Trapped(format!("worker wait failed: {e}")))?,
        Some(t) => {
            let deadline = Instant::now() + t;
            loop {
                match child.try_wait() {
                    Ok(Some(s)) => break s,
                    Ok(None) => {
                        if Instant::now() >= deadline {
                            // THE KILL: the hung guest dies here, with
                            // the process, not inside the pool.
                            let _ = child.kill();
                            let _ = child.wait();
                            let _ = reader.join();
                            return Err(PoolError::OutOfTime);
                        }
                        std::thread::sleep(Duration::from_millis(2));
                    }
                    Err(e) => return Err(PoolError::Trapped(format!("worker wait failed: {e}"))),
                }
            }
        }
    };
    let out = reader.join().unwrap_or_default();
    classify_exit(&status, &out)
}

/// Map the worker's exit status + stdout onto the pool's taxonomy
/// (the exit-code vocabulary is the worker's own contract).
fn classify_exit(status: &ExitStatus, stdout: &str) -> Result<Vec<i64>, PoolError> {
    // The failure answer's message, when the child got to print one.
    let msg = || {
        serde_json::from_str::<serde_json::Value>(stdout)
            .ok()
            .and_then(|v| {
                v.get("message")
                    .and_then(|m| m.as_str().map(str::to_string))
            })
            .unwrap_or_default()
    };
    if status.success() {
        let v: serde_json::Value = serde_json::from_str(stdout)
            .map_err(|e| PoolError::Trapped(format!("worker stdout unparsable: {e}")))?;
        if v.get("ok").and_then(|b| b.as_bool()) != Some(true) {
            return Err(PoolError::Trapped(
                "worker answered exit-0 without ok:true".into(),
            ));
        }
        let results = v
            .get("results")
            .and_then(|r| r.as_array())
            .ok_or_else(|| PoolError::Trapped("worker answer missing `results`".into()))?;
        return Ok(results.iter().filter_map(|x| x.as_i64()).collect());
    }
    match status.code() {
        Some(WORKER_EXIT_FUEL) => Err(PoolError::OutOfFuel),
        Some(WORKER_EXIT_BAD_MODULE) => Err(PoolError::BadModule(if msg().is_empty() {
            "worker: bad module".into()
        } else {
            msg()
        })),
        Some(WORKER_EXIT_TRAP) => Err(PoolError::Trapped(msg())),
        Some(101) => Err(PoolError::Trapped(if msg().is_empty() {
            "worker panicked (exit 101)".into()
        } else {
            msg()
        })),
        Some(c) => Err(PoolError::Trapped(format!("worker exited {c}: {}", msg()))),
        // No exit code = killed by signal. The TIMEOUT path kills and
        // returns OutOfTime before reaching here, so a signal here is
        // an external kill — reported, not hidden.
        None => Err(PoolError::Trapped(format!(
            "worker killed by signal: {status}"
        ))),
    }
}

/// Minimal standard-alphabet base64 encode (zero deps; the worker's
/// decoder is the mirror).
fn b64_encode(bytes: &[u8]) -> String {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = chunk.get(1).copied().unwrap_or(0) as u32;
        let b2 = chunk.get(2).copied().unwrap_or(0) as u32;
        let n = (b0 << 16) | (b1 << 8) | b2;
        out.push(T[(n >> 18) as usize & 63] as char);
        out.push(T[(n >> 12) as usize & 63] as char);
        out.push(if chunk.len() > 1 {
            T[(n >> 6) as usize & 63] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            T[n as usize & 63] as char
        } else {
            '='
        });
    }
    out
}

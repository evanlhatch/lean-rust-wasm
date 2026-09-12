//! WORKER-POOL CONFORMANCE: the honest v1 "Monty pattern" — a
//! replenishing pool of workers, each job in a PRIVATE wasmi engine
//! (fuel = the deterministic budget AND the v1 timeout proxy), the
//! pool SURVIVING every kill. Each test pins one clause of the
//! contract on `guestlang_rt::Pool`; the negative control pins the
//! capacity itself.

use guestlang_rt::{Job, Pool, PoolError};
use std::sync::Arc;
use std::time::{Duration, Instant};

fn demo_wasm() -> Vec<u8> {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..//lean/wasm-backend/target/demo.wasm");
    std::fs::read(std::fs::canonicalize(&p).expect("run `just wasm-compile`")).unwrap()
}

fn job(wasm: &Arc<[u8]>, func: &str, args: &[i64], fuel: u64) -> Job {
    Job {
        wasm: Arc::clone(wasm),
        func: func.into(),
        args: args.to_vec(),
        fuel,
    }
}

/// Hand-encoded: `(module (func (export "boom") unreachable))` — a
/// guest that ALWAYS traps, no fixture needed (the trap arm's
/// negative control; the demo module traps nowhere).
fn unreachable_wasm() -> Vec<u8> {
    vec![
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, // magic + version
        0x01, 0x04, 0x01, 0x60, 0x00, 0x00, // type: () -> ()
        0x03, 0x02, 0x01, 0x00, // func 0: type 0
        0x07, 0x08, 0x01, 0x04, 0x62, 0x6F, 0x6F, 0x6D, 0x00, 0x00, // export "boom"
        0x0A, 0x05, 0x01, 0x03, 0x00, 0x00, 0x0B, // code: locals 0, unreachable, end
    ]
}

/// (a) THE ORACLE ARM: N parallel jobs, all correct — the pool is a
/// correct dispatcher (double 21 = 42, adder 40 2 = 42, double-area
/// 5 = 100 — the same oracles the conformance suite pins, now from
/// concurrent threads through one pool).
#[test]
fn parallel_jobs_all_answer_the_oracle() {
    let wasm: Arc<[u8]> = demo_wasm().into();
    let pool = Arc::new(Pool::new(4));
    // the direct oracle pins (one pool, the three demo exports)
    assert_eq!(
        pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
        vec![42]
    );
    assert_eq!(
        pool.run(job(&wasm, "adder", &[40, 2], 1_000_000)).unwrap(),
        vec![42]
    );
    assert_eq!(
        pool.run(job(&wasm, "double-area", &[5], 1_000_000))
            .unwrap(),
        vec![100]
    );
    // the CONCURRENT oracle: 8 threads × double 21 through the pool
    let mut handles = Vec::new();
    for _ in 0..8 {
        let wasm = Arc::clone(&wasm);
        let pool = Arc::clone(&pool);
        handles.push(std::thread::spawn(move || {
            assert_eq!(
                pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
                vec![42]
            );
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    // the SHARED-POOL oracle: 8 concurrent callers, ONE pool — the
    // dispatcher interleaves them, every answer is the oracle's
    let mut handles = Vec::new();
    for _ in 0..8 {
        let wasm = Arc::clone(&wasm);
        let pool = Arc::clone(&pool);
        handles.push(std::thread::spawn(move || {
            assert_eq!(
                pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
                vec![42]
            );
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
}

/// (b) THE ISOLATION ARM (fuel): a job whose budget cannot even START
/// the call dies with `PoolError::OutOfFuel` — and the NEXT job on
/// the same pool is green. Fuel = the v1 timeout proxy; the pool
/// replenishes after the kill.
#[test]
fn out_of_fuel_kills_the_job_not_the_pool() {
    let wasm: Arc<[u8]> = demo_wasm().into();
    let pool = Pool::new(2);
    for _ in 0..3 {
        match pool.run(job(&wasm, "double", &[21], 1)) {
            Err(PoolError::OutOfFuel) => {}
            other => panic!("expected OutOfFuel, got {other:?}"),
        }
        // the pool survives: the very next job is correct
        assert_eq!(
            pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
            vec![42]
        );
    }
}

/// (c) THE ISOLATION ARM (trap): a guest that ALWAYS traps dies with
/// `PoolError::Trapped` — and the pool keeps serving correct answers.
#[test]
fn trapped_guest_kills_the_job_not_the_pool() {
    let boom: Arc<[u8]> = unreachable_wasm().into();
    let wasm: Arc<[u8]> = demo_wasm().into();
    let pool = Pool::new(2);
    for _ in 0..3 {
        match pool.run(job(&boom, "boom", &[], 1_000_000)) {
            Err(PoolError::Trapped(m)) => assert!(m.contains("wasmi"), "{m}"),
            other => panic!("expected Trapped, got {other:?}"),
        }
        assert_eq!(
            pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
            vec![42]
        );
    }
}

/// (c') THE CLASSIFICATION ARM: a module that cannot LOAD is
/// `PoolError::BadModule` — distinct from a runtime trap, and equally
/// non-fatal.
#[test]
fn unloadable_module_is_bad_module_and_the_pool_survives() {
    let wasm: Arc<[u8]> = demo_wasm().into();
    let garbage: Arc<[u8]> = vec![0x00, 0x61, 0x73, 0x6D, 0x0E, 0xAF, 0x00, 0x0D].into();
    let pool = Pool::new(1);
    match pool.run(job(&garbage, "double", &[21], 1_000_000)) {
        Err(PoolError::BadModule(m)) => assert!(m.contains("wasmi"), "{m}"),
        other => panic!("expected BadModule, got {other:?}"),
    }
    // a module that loads but lacks the export: also the module's fault
    match pool.run(job(&wasm, "no-such-fn", &[21], 1_000_000)) {
        Err(PoolError::BadModule(m)) => assert!(m.contains("no export"), "{m}"),
        other => panic!("expected BadModule, got {other:?}"),
    }
    assert_eq!(
        pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
        vec![42]
    );
}

/// (d) THE NEGATIVE CONTROL: the pool's capacity is RESPECTED. Two
/// workers, SIX concurrent callers (N+1 and then some): the peak
/// concurrency REACHES the capacity (parallelism is real) and NEVER
/// exceeds it (the surplus queued, not executed) — and every queued
/// job still answers the oracle.
#[test]
fn capacity_is_a_hard_ceiling_and_the_surplus_queues() {
    let wasm: Arc<[u8]> = demo_wasm().into();
    let pool = Arc::new(Pool::new(2));
    assert_eq!(pool.workers(), 2);
    let mut handles = Vec::new();
    for _ in 0..6 {
        let wasm = Arc::clone(&wasm);
        handles.push(std::thread::spawn({
            let pool = Arc::clone(&pool);
            move || {
                // MANY jobs per caller: the busy window must outlive the
                // main thread's poll latency (one job per caller finished
                // before the observer could ever look — a test bug).
                for _ in 0..25 {
                    assert_eq!(
                        pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
                        vec![42]
                    );
                }
            }
        }));
    }
    // wait (bounded) for BOTH workers to be busy simultaneously —
    // proves parallelism, and proves the watermark can be observed
    let deadline = Instant::now() + Duration::from_secs(30);
    while pool.max_in_flight() < 2 {
        assert!(
            Instant::now() < deadline,
            "workers never reached full capacity"
        );
        std::thread::sleep(Duration::from_micros(50));
    }
    // the ceiling holds across the whole run
    for h in handles {
        h.join().unwrap();
    }
    assert!(
        pool.max_in_flight() <= pool.workers(),
        "capacity violated: peak {} > workers {}",
        pool.max_in_flight(),
        pool.workers()
    );
    assert_eq!(
        pool.max_in_flight(),
        2,
        "the watermark never reached capacity — jobs ran serially (or the test's observer is broken)"
    );
    // fully drained
    assert_eq!(pool.in_flight(), 0);
}

// ══ HARD MODE: the subprocess isolation lane ══════════════════════
// Same Pool contract, different substrate: every job in a FRESH
// `worker` SUBPROCESS (spawn-per-job). The arms below pin the
// protocol end-to-end: job JSON in (base64 module on stdin), answer
// JSON out, exit-code classification, and — THE POINT — the LIVE
// wall-clock kill the soft mode's header said threads could not
// provide. A worker bin is resolved via CARGO_BIN_EXE_worker
// (cargo sets it for this package's integration tests).

/// Hand-encoded: `(module (func (export "spin") loop br 0))` — a
/// guest that NEVER halts (the OutOfTime arm's fixture: fed a HUGE
/// fuel so fuel can never fire first).
fn spin_wasm() -> Vec<u8> {
    vec![
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, // magic + version
        0x01, 0x04, 0x01, 0x60, 0x00, 0x00, // type: () -> ()
        0x03, 0x02, 0x01, 0x00, // func 0: type 0
        0x07, 0x08, 0x01, 0x04, 0x73, 0x70, 0x69, 0x6E, 0x00, 0x00, // export "spin"
        0x0A, 0x09, 0x01, 0x07, 0x00, 0x03, 0x40, 0x0C, 0x00, 0x0B,
        0x0B, // code: locals 0, loop br 0
    ]
}

/// (h-a) THE HARD ORACLE: double 21 = 42 through a subprocess — the
/// module bytes crossed the boundary as base64 on the child's stdin,
/// the answer came back as JSON on its stdout, exit 0.
#[test]
fn hard_mode_runs_the_oracle_in_a_subprocess() {
    let wasm: Arc<[u8]> = demo_wasm().into();
    let pool = Pool::new_hard(2);
    assert!(pool.is_hard());
    assert_eq!(pool.workers(), 2);
    assert_eq!(
        pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
        vec![42]
    );
    assert_eq!(
        pool.run(job(&wasm, "adder", &[40, 2], 1_000_000)).unwrap(),
        vec![42]
    );
    // and the next job gets a FRESH process — repeat the oracle
    assert_eq!(
        pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
        vec![42]
    );
}

/// (h-b) THE HARD FUEL ARM: the budget is the worker's `--fuel`, and
/// exhaustion is the child's exit 2 = `PoolError::OutOfFuel` — with
/// the pool (a live, separate parent) unharmed.
#[test]
fn hard_mode_out_of_fuel_kills_the_child_not_the_pool() {
    let wasm: Arc<[u8]> = demo_wasm().into();
    let pool = Pool::new_hard(2);
    for _ in 0..3 {
        match pool.run(job(&wasm, "double", &[21], 1)) {
            Err(PoolError::OutOfFuel) => {}
            other => panic!("expected OutOfFuel, got {other:?}"),
        }
        assert_eq!(
            pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
            vec![42]
        );
    }
}

/// (h-c) THE HARD TRAP ARM: the guest's `unreachable` is the child's
/// nonzero exit = `PoolError::Trapped` — the crash was the CHILD's,
/// and the parent pool never even hiccupped.
#[test]
fn hard_mode_trap_is_the_childs_nonzero_exit() {
    let boom: Arc<[u8]> = unreachable_wasm().into();
    let wasm: Arc<[u8]> = demo_wasm().into();
    let pool = Pool::new_hard(2);
    for _ in 0..3 {
        match pool.run(job(&boom, "boom", &[], 1_000_000)) {
            Err(PoolError::Trapped(m)) => assert!(m.contains("wasmi"), "{m}"),
            other => panic!("expected Trapped, got {other:?}"),
        }
        assert_eq!(
            pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
            vec![42]
        );
    }
}

/// (h-d) THE OUTOFTIME ARM — THE SUBPROCESS'S PROOF: a guest that
/// NEVER halts, fed fuel so huge it can never fire, against a
/// wall-clock deadline: the parent's poll hits the deadline, the
/// child is KILLED, and the answer is `PoolError::OutOfTime` — the
/// live enforcement the soft mode documented as impossible. Then the
/// pool answers the oracle again: the kill cost nothing.
#[test]
fn hard_mode_wall_clock_deadline_kills_the_hang() {
    let spin: Arc<[u8]> = spin_wasm().into();
    let wasm: Arc<[u8]> = demo_wasm().into();
    let pool = Pool::new_hard(2);
    let started = Instant::now();
    match pool.run_timeout(
        job(&spin, "spin", &[], u64::MAX / 4),
        Duration::from_secs(2),
    ) {
        Err(PoolError::OutOfTime) => {}
        other => panic!("expected OutOfTime, got {other:?}"),
    }
    // the kill actually happened AT the deadline (not the child
    // dying on its own with a coincidental classification)
    let elapsed = started.elapsed();
    assert!(
        elapsed >= Duration::from_millis(1900),
        "killed too early: {elapsed:?}"
    );
    assert!(
        elapsed < Duration::from_secs(30),
        "kill latency runaway: {elapsed:?}"
    );
    // (e) THE SURVIVOR: after fuel-kills, traps AND the kill, the pool
    // still serves the oracle.
    assert_eq!(
        pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
        vec![42]
    );
}

/// (h-e) THE HARD SURVIVOR: all three kill classes in sequence on ONE
/// hard pool, then the oracle — every child died, the parent survived.
#[test]
fn hard_mode_survives_fuel_trap_and_time() {
    let wasm: Arc<[u8]> = demo_wasm().into();
    let boom: Arc<[u8]> = unreachable_wasm().into();
    let garbage: Arc<[u8]> = vec![0x00, 0x61, 0x73, 0x6D, 0x0E, 0xAF, 0x00, 0x0D].into();
    let pool = Pool::new_hard(2);
    match pool.run(job(&wasm, "double", &[21], 1)) {
        Err(PoolError::OutOfFuel) => {}
        other => panic!("expected OutOfFuel, got {other:?}"),
    }
    match pool.run(job(&boom, "boom", &[], 1_000_000)) {
        Err(PoolError::Trapped(_)) => {}
        other => panic!("expected Trapped, got {other:?}"),
    }
    match pool.run(job(&garbage, "double", &[21], 1_000_000)) {
        Err(PoolError::BadModule(_)) => {}
        other => panic!("expected BadModule, got {other:?}"),
    }
    assert_eq!(
        pool.run(job(&wasm, "double", &[21], 1_000_000)).unwrap(),
        vec![42]
    );
    assert_eq!(pool.in_flight(), 0);
}

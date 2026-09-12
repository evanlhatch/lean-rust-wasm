//! guestlang-rt worker — the SUBPROCESS HARD-ISOLATION half of the pool
//! (the binary-crate companion `pool.rs`'s v1 header documented).
//!
//! OWNERSHIP: the `subprocess-isolation` lane. Depends only on the
//! library's `invoke_core_fueled` (the deterministic profile is
//! ENFORCED inside `Runtime::new` — the worker cannot widen it) plus
//! serde_json (already an audited dep — the IPC codec) and std.
//!
//! THE PROTOCOL (pinned by `tests/pool.rs`, hard-mode arm):
//!
//!   argv:    worker --fuel N [--mem-bytes M]
//!   stdin:   ONE JSON job — {"wasm-path": P} or {"wasm-b64": B},
//!            plus "func": S, "args": [i64…]
//!   stdout:  ONE JSON answer —
//!            success: {"ok":true,"results":[i64…],"fuel-used":N}
//!            failure: {"ok":false,"message":S}
//!   exit:    0 ok · 1 guest trap · 2 out-of-fuel · 3 bad module/usage ·
//!            101 worker panic (std's own panic exit code)
//!
//! The PARENT (pool hard mode) classifies by EXIT CODE + stdout: 2 →
//! `PoolError::OutOfFuel`, 3 → `BadModule`, 1/101/other-nonzero →
//! `Trapped`, and a wall-clock KILL (signal, no exit code) →
//! `OutOfTime` — the LIVE timeout the thread pool could not enforce.
//!
//! ISOLATION: one process per job (spawn-per-job — maximal isolation:
//! a trap, OOM, or panic tears down NOTHING but this process). The
//! fuel = the job's budget; `--mem-bytes` is parsed and echoed but v1
//! passes no engine-level memory ceiling — fuel bounds `memory.grow`
//! deterministically, and a wasmi `ResourceLimiter` needs store
//! access `Runtime` does not expose (documented follow-up).

use std::io::{Read, Write};
use std::process::ExitCode;

use guestlang_rt::Runtime;

fn main() -> ExitCode {
    let (fuel, _mem_bytes) = match parse_args() {
        Ok(v) => v,
        Err(m) => fail(3, &m),
    };
    let mut input = String::new();
    if std::io::stdin().read_to_string(&mut input).is_err() {
        fail(3, "worker: stdin unreadable");
    }
    let job: serde_json::Value = serde_json::from_str(&input)
        .unwrap_or_else(|e| fail(3, &format!("worker: unparsable job: {e}")));

    // The module: a PATH (the test/CLI convenience) or base64 (the
    // pool's IPC path — the process boundary carries BYTES, not Arcs).
    let wasm: Vec<u8> = if let Some(p) = job.get("wasm-path").and_then(|v| v.as_str()) {
        std::fs::read(p).unwrap_or_else(|e| fail(3, &format!("worker: read wasm-path: {e}")))
    } else if let Some(b) = job.get("wasm-b64").and_then(|v| v.as_str()) {
        match b64_decode(b) {
            Ok(w) => w,
            Err(e) => fail(3, &format!("worker: wasm-b64: {e}")),
        }
    } else {
        fail(3, "worker: job needs `wasm-path` or `wasm-b64`");
    };
    let func = job
        .get("func")
        .and_then(|v| v.as_str())
        .unwrap_or_else(|| fail(3, "worker: job needs `func`"))
        .to_string();
    let args: Vec<i64> = job
        .get("args")
        .and_then(|v| v.as_array())
        .map(|a| a.iter().filter_map(|x| x.as_i64()).collect())
        .unwrap_or_default();

    // LOAD first, CALL second — the split IS the classification: a
    // module that cannot load (or lacks the export surface) is the
    // parent's BadModule (exit 3), exactly like the soft pool's
    // `execute` maps `Runtime::new` errors. The call's own errors
    // keep the fuel/trap/vocabulary split below.
    let mut rt = match Runtime::new(&wasm, fuel) {
        Ok(rt) => rt,
        Err(e) => fail(3, &e.0),
    };
    match rt.call(&func, &args, fuel) {
        Ok((results, used)) => {
            println!(
                "{}",
                serde_json::json!({ "ok": true, "results": results, "fuel-used": used })
            );
            ExitCode::from(0)
        }
        Err(e) => {
            // Same seam the pool's `classify` sits on: wasmi out-of-fuel
            // surfaces "fuel" in every wasmi 2.0 variant; a missing
            // export / arity mismatch is rt's "no export"/"arity"
            // prefix; everything else is a guest trap.
            let msg = e.0;
            if msg.to_lowercase().contains("fuel") {
                fail(2, &msg)
            } else if msg.starts_with("no export") || msg.starts_with("arity") {
                fail(3, &msg)
            } else {
                fail(1, &msg)
            }
        }
    }
}

/// Print the failure answer and exit with `code` (the parent's
/// classifier reads BOTH).
fn fail(code: i32, msg: &str) -> ! {
    println!("{}", serde_json::json!({ "ok": false, "message": msg }));
    let _ = std::io::stdout().flush();
    std::process::exit(code)
}

/// `--fuel N` (REQUIRED — the budget IS the run's bound) and
/// `--mem-bytes M` (parsed, echoed, v1-unenforced — see the header).
fn parse_args() -> Result<(u64, u64), String> {
    let mut fuel = None;
    let mut mem = 0;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--fuel" => {
                fuel = Some(
                    it.next()
                        .ok_or("worker: --fuel needs a value")?
                        .parse::<u64>()
                        .map_err(|e| format!("worker: --fuel: {e}"))?,
                )
            }
            "--mem-bytes" => {
                mem = it
                    .next()
                    .ok_or("worker: --mem-bytes needs a value")?
                    .parse::<u64>()
                    .map_err(|e| format!("worker: --mem-bytes: {e}"))?
            }
            other => {
                return Err(format!(
                    "worker: unknown arg `{other}` (usage: worker --fuel N [--mem-bytes M])"
                ));
            }
        }
    }
    let fuel = fuel.ok_or("worker: --fuel N is required")?;
    Ok((fuel, mem))
}

/// Minimal standard-alphabet base64 decode (zero deps; the pool's
/// encoder is the mirror). Rejects padding/corpus errors loudly.
fn b64_decode(s: &str) -> Result<Vec<u8>, String> {
    fn val(c: u8) -> Result<u32, String> {
        match c {
            b'A'..=b'Z' => Ok((c - b'A') as u32),
            b'a'..=b'z' => Ok((c - b'a') as u32 + 26),
            b'0'..=b'9' => Ok((c - b'0') as u32 + 52),
            b'+' => Ok(62),
            b'/' => Ok(63),
            _ => Err(format!("invalid base64 byte {c:#x}")),
        }
    }
    let bytes: Vec<u8> = s.bytes().filter(|b| !b.is_ascii_whitespace()).collect();
    if bytes.len() % 4 != 0 {
        return Err("length not a multiple of 4".into());
    }
    let mut out = Vec::with_capacity(bytes.len() / 4 * 3);
    for chunk in bytes.chunks(4) {
        let pad = chunk.iter().filter(|&&c| c == b'=').count();
        if pad > 2 || chunk.len() != 4 || chunk[..4 - pad].iter().any(|&c| c == b'=') {
            return Err("bad padding".into());
        }
        let mut n = 0u32;
        for &c in &chunk[..4 - pad] {
            n = (n << 6) | val(c)?;
        }
        n <<= 6 * (4 - chunk[..4 - pad].len()) as u32;
        out.push((n >> 16) as u8);
        if pad < 2 {
            out.push((n >> 8) as u8);
        }
        if pad < 1 {
            out.push(n as u8);
        }
    }
    Ok(out)
}

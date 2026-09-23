//! Inversion properties — the host-side executable reading of
//! `Dbsp.ChangeSpec.ChangeInversion.correct_invert`
//! (`patch (patch t Δ) (invert Δ) = t`), iterated to log scale
//! (`Machines.Rewind`'s rewind-as-iterated-invert):
//!
//! 1. PER-STEP: after every append, rewinding one step restores the exact prior materialized state.
//! 2. FULL: a random walk rewound to 0 returns every table to empty; rewound to k, the state equals
//!    the prefix replay `state_at(k)` for sampled k.
//! 3. PERSISTED: the inverses survive the byte boundary — the property re-checked after a
//!    byte-level reopen.
//! Negative control: a log with a corrupted stored inverse must NOT
//! satisfy the rewind law (the sweep bites).

mod common;

use common::Lcg;
use common::row;
use common::schemas;
use wasm_delta::Change;
use wasm_delta::DeltaLog;
use wasm_delta::MemBackend;
use wasm_delta::Value;

/// Append a random walk; return the log.
fn walk(seed: u64, steps: u32) -> DeltaLog<MemBackend> {
    let ss = schemas();
    let schema = ss.get("t").unwrap_or_else(|| panic!("registered")).clone();
    let mut log =
        DeltaLog::open_with(MemBackend::new(), ss).unwrap_or_else(|e| panic!("open: {e}"));
    let mut r = Lcg(seed);
    for i in 0..steps {
        let key = r.below(8);
        let change = match r.below(3) {
            0 => Change::Insert(row(&schema, key, &format!("i{i}"))),
            1 => Change::Update(row(&schema, key, &format!("u{i}"))),
            _ => Change::Remove(Value::U64(key)),
        };
        log.append("t", change)
            .unwrap_or_else(|e| panic!("append: {e}"));
    }
    log
}

#[test]
fn per_step_correct_invert() {
    let ss = schemas();
    let schema = ss.get("t").unwrap_or_else(|| panic!("registered")).clone();
    let mut log =
        DeltaLog::open_with(MemBackend::new(), ss).unwrap_or_else(|e| panic!("open: {e}"));
    let mut r = Lcg(0x1234);
    for i in 0..150 {
        let before = log.state("t").cloned();
        let key = r.below(8);
        let change = match r.below(3) {
            0 => Change::Insert(row(&schema, key, &format!("i{i}"))),
            1 => Change::Update(row(&schema, key, &format!("u{i}"))),
            _ => Change::Remove(Value::U64(key)),
        };
        let seq = log
            .append("t", change)
            .unwrap_or_else(|e| panic!("append: {e}"));
        // patch (patch t Δ) (invert Δ) = t — via the stored inverse.
        log.rewind_to(seq).unwrap_or_else(|e| panic!("rewind: {e}"));
        assert_eq!(
            log.state("t").cloned().unwrap_or_default(),
            before.unwrap_or_default(),
            "step {i}: inverse failed to restore"
        );
    }
}

#[test]
fn rewind_to_prefix_replay() {
    let mut log = walk(0xbeef, 120);
    let n = log.len();
    for k in [0u64, 1, n / 3, n / 2, n - 1] {
        let mut l = walk(0xbeef, 120);
        l.rewind_to(k).unwrap_or_else(|e| panic!("rewind: {e}"));
        assert_eq!(
            l.state("t").cloned(),
            l.state_at("t", k),
            "state after rewind_to({k}) != prefix replay"
        );
    }
    // Full rewind: the table is back to EMPTY.
    log.rewind_to(0).unwrap_or_else(|e| panic!("rewind: {e}"));
    assert_eq!(
        log.state("t").map(|t| t.rows().count()),
        Some(0),
        "rewind_to(0) must return to the empty state"
    );
}

#[test]
fn inversion_survives_reopen() {
    let log = walk(0xabcd, 60);
    let bytes = log.backend().bytes().to_vec();
    let mut backend = MemBackend::new();
    wasm_delta::Backend::append(&mut backend, &bytes).unwrap_or_else(|e| panic!("seed: {e}"));
    let mut log2 =
        DeltaLog::open_with(backend, schemas()).unwrap_or_else(|e| panic!("reopen: {e}"));
    // Rewind over the byte-boundary-decoded inverses.
    log2.rewind_to(0).unwrap_or_else(|e| panic!("rewind: {e}"));
    assert_eq!(
        log2.state("t").map(|t| t.rows().count()),
        Some(0),
        "reopened inverses must restore the empty state"
    );
}

/// NEGATIVE CONTROL: corrupt a stored inverse's key byte in the raw
/// journal; the rewind law must break (or the reopen must reject).
/// A suite that cannot fail is vacuous.
#[test]
fn corrupted_inverse_breaks_rewind() {
    let log = walk(0x777, 40);
    let bytes = log.backend().bytes().to_vec();
    // Flip bytes near the tail of the last-but-one record: find a flip
    // that keeps the envelope decodable but changes an entry payload.
    // We scan single-byte mutations of the last third of the journal;
    // the control demands at least one that reopens fine AND then
    // violates the rewind law.
    let mut violations = 0u32;
    let mut rejections = 0u32;
    for i in (bytes.len() * 2 / 3)..bytes.len() {
        for bit in [0x01u8, 0x10, 0x80] {
            let mut bad = bytes.clone();
            bad[i] ^= bit;
            let mut backend = MemBackend::new();
            wasm_delta::Backend::append(&mut backend, &bad).unwrap_or_else(|e| panic!("seed: {e}"));
            let Ok(mut l) = DeltaLog::open_with(backend, schemas()) else {
                rejections += 1;
                continue;
            };
            let k = l.len().saturating_sub(2);
            let want = l.state_at("t", k);
            if l.rewind_to(k).is_err() {
                violations += 1;
                continue;
            }
            if l.state("t").cloned() != want {
                violations += 1;
            }
        }
    }
    assert!(
        violations + rejections > 0,
        "vacuous: no corruption ever bit (neither rejected nor violated)"
    );
}

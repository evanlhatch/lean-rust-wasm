//! Shared harness for wasm-delta's integration suites (one copy of the
//! helpers every test was hand-rolling):
//!
//! - DETERMINISTIC SOURCE — `Lcg`: the Knuth-constant LCG (6364136223846793005 /
//!   1442695040888963407) behind every test generator, plus `Lcg::from_bytes` (FNV-1a) for the fuzz
//!   mutation schedule. The SAME stream every run — the seeds below are the byte-identical-input
//!   contract (the value/trace goldens never move).
//! - THE T TABLE — `schemas()` (single table `t`: `k u64`, `v Str`) and `row()`: the row shape the
//!   suites append/rewind/recover over.
//! - HOUSE HELPERS — `fail` (no bare unwrap) and `tempdir` (unique per test, removed by the
//!   caller).
//!
//! Ownership: crates/wasm-delta/tests/common/mod.rs. Additive to
//! src/**: nothing here touches it. The suites' ASSERTIONS stay in the
//! suites — the harness carries no expectations of its own.

// Per-binary compilation (each tests/*.rs includes this module) leaves
// most helpers unused in any given binary — the harness is the shared
// surface, not each inclusion.
#![allow(dead_code)]

use std::path::PathBuf;

use wasm_delta::Field;
use wasm_delta::Row;
use wasm_delta::Schema;
use wasm_delta::SchemaSet;
use wasm_delta::Ty;
use wasm_delta::Value;

/// The suite's deterministic LCG (Knuth constants 6364136223846793005 /
/// 1442695040888963407; output after the multiply-add, >> 16).
pub struct Lcg(pub u64);

impl Lcg {
    pub fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 16
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// LCG seeded from raw bytes via FNV-1a (the fuzz input IS the
    /// seed): the mutation schedule is a pure function of the input, so
    /// a printed bolero seed replays exactly.
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut seed = 0xcbf2_9ce4_8422_2325u64; // FNV offset basis
        for b in bytes {
            seed ^= u64::from(*b);
            seed = seed.wrapping_mul(0x0000_0100_0000_01b3);
        }
        Self(seed | 1)
    }
}

/// The single-table schema set the suites speak: `t` = `k u64`, `v Str`
/// (matches the crash-recovery/fuzz journals).
pub fn schemas() -> SchemaSet {
    let mut s = SchemaSet::new();
    s.register(
        "t",
        Schema::new(vec![
            Field {
                name: "k".into(),
                ty: Ty::U64,
            },
            Field {
                name: "v".into(),
                ty: Ty::Str,
            },
        ]),
    );
    s
}

/// A valid row for table `t` (`row::check` passes by construction).
pub fn row(schema: &Schema, k: u64, v: &str) -> Row {
    Row::new(schema, vec![Value::U64(k), Value::Str(v.into())])
        .unwrap_or_else(|| panic!("test row checks"))
}

/// Fail loud, fail clear (the house pattern: no bare `unwrap`).
#[track_caller]
#[allow(clippy::panic, reason = "test helper: fail loud, fail clear")]
pub fn fail(msg: &str) -> ! {
    panic!("{msg}");
}

/// Unique tempdir per test (the crash-recovery sweep writes a fresh cut
/// per truncation offset; the caller removes it).
pub fn tempdir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "wasm-delta-crash-{tag}-{}-{:x}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.subsec_nanos())
            .unwrap_or(0)
    ));
    std::fs::create_dir_all(&dir).unwrap_or_else(|e| fail(&format!("tempdir: {e}")));
    dir
}

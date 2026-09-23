//! Shared harness for forge's integration suites: the house helpers
//! every test used to hand-roll in one place (the guestlang-host /
//! wasm-delta pattern).
//!
//! - `fail` — fail loud, fail clear (no bare `unwrap` in tests).
//! - `tempdir` — unique tempdir per test (pid + nanos in the name).
//!   Distinct prefix ("forge-test" vs guestlang-host / wasm-delta):
//!   runs of different crates never collide on the same dir.
//!
//! Ownership: crates/forge/tests/common/mod.rs. Additive to src/**:
//! nothing here touches it. The suites' ASSERTIONS stay in the suites
//! — the harness carries no expectations of its own.

// Per-binary compilation (each tests/*.rs includes this module) leaves
// some helpers unused in any given binary — the harness is the shared
// surface, not each inclusion.
#![allow(dead_code)]

use std::path::PathBuf;

/// Fail loud, fail clear (the house pattern: no bare `unwrap`).
#[track_caller]
#[allow(clippy::panic, reason = "test helper: fail loud, fail clear")]
pub fn fail(msg: &str) -> ! {
    panic!("{msg}");
}

/// Unique tempdir per test (the wasm-delta pattern).
pub fn tempdir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "forge-test-{tag}-{}-{:x}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.subsec_nanos())
            .unwrap_or(0)
    ));
    std::fs::create_dir_all(&dir).unwrap_or_else(|e| fail(&format!("tempdir: {e}")));
    dir
}

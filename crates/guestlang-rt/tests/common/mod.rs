//! Shared helpers for the guestlang-rt integration tests (the wasmi half
//! of the dual-engine story).
//!
//! ONE demo-component loader. The three rt test surfaces
//! (`conformance`, `snapshot`, `snapshot_restore_seq`) all exercise the
//! SAME committed artifact: the compiler line's output at
//! `lean/wasm-backend/target/demo.wasm` (`just wasm-compile`). A single
//! read path keeps the load story honest — every call site resolves the
//! artifact identically, and an absent artifact surfaces loudly (the
//! conformance/snapshot tests panic with the compile-line reminder; the
//! fuzz target skips, never faking coverage of a module it does not
//! have — hence the `-opt` twin).
//!
//! Deliberate exclusions: edgepython's `py.wasm` is a DIFFERENT
//! artifact (a second frontend's output — the IR-seam neutrality proof)
//! and keeps its own loader in `edgepython.rs`; the `diff.json` oracle
//! manifest is read by `conformance.rs` alone.
#![allow(
    dead_code,
    reason = "each test crate compiles this module standalone and uses only the loader whose surface it exercises — the twin being unused in one crate is expected, not a defect"
)]

/// The canonical demo-component path; `None` when `just wasm-compile`'s
/// artifact is absent.
fn demo_component_path() -> Option<std::path::PathBuf> {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/wasm-backend/target/demo.wasm");
    std::fs::canonicalize(p).ok()
}

/// The demo component's wasm bytes. Panics with the compile-line
/// reminder when the artifact is absent — the conformance/snapshot
/// tests hard-require it (a test that reads nothing covers nothing).
pub fn demo_wasm() -> Vec<u8> {
    let p = demo_component_path().expect("run `just wasm-compile`");
    std::fs::read(p).unwrap()
}

/// The demo component's bytes as `Option` — the snapshot_restore_seq
/// fuzz target's loud-skip path (missing artifact ⇒ skip the run,
/// never fake coverage).
pub fn demo_wasm_opt() -> Option<Vec<u8>> {
    std::fs::read(demo_component_path()?).ok()
}

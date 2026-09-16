//! Build script for lean-ffi.
//!
//! Compiles the test fixture `tests/lean/Echo.lean` with `lean -c` and links
//! it into this package's test targets so `tests/roundtrip.rs` can call into
//! Lean. Toolchain discovery mirrors lean-sys-v433's build.rs
//! (`LEAN_SYS_ROOT` → `lean --print-prefix` → elan v4.33.* scan); the Lean
//! runtime archives themselves are linked by lean-sys-v433's build script
//! (its `links` key propagates them to all dependents).
//!
//! The generated module initializer symbol depends on the fixture path
//! relative to this crate root: `tests/lean/Echo.lean` →
//! `initialize_tests_lean_Echo`. We assert the symbol exists in the generated
//! C so a module-name drift fails HERE, at build time, not at link time.
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-env-changed=LEAN_SYS_ROOT");
    println!("cargo:rerun-if-changed=tests/lean/Echo.lean");

    let lean_dir = lean_prefix();
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR unset"));

    // The Lean runtime archives themselves are linked via lean-sys-v433's
    // `links` propagation, but `rustc-link-arg` does NOT propagate across
    // packages — so each downstream crate must emit its OWN rpath to the
    // toolchain lib dir, else libc++/libc++abi/libunwind fail to resolve
    // at load time (observed: `libunwind.so.1: cannot open shared object
    // file` running `cargo test -p lean-ffi`).
    println!(
        "cargo:rustc-link-arg=-Wl,-rpath,{}",
        lean_dir.join("lib").display()
    );

    let echo_c = out_dir.join("echo_fixture.c");
    compile_echo_lean(&echo_c);
    let generated = std::fs::read_to_string(&echo_c).expect("generated fixture C unreadable");
    assert!(
        generated.contains("initialize_tests_lean_Echo"),
        "module-init symbol drift: expected initialize_tests_lean_Echo in {}",
        echo_c.display()
    );

    cc::Build::new()
        .file(&echo_c)
        .include(lean_dir.join("include"))
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-label")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .compile("lean_ffi_echo_fixture");
}

fn lean_prefix() -> PathBuf {
    if let Ok(root) = std::env::var("LEAN_SYS_ROOT") {
        return PathBuf::from(root);
    }
    if let Ok(output) = Command::new("lean").args(["--print-prefix"]).output() {
        if output.status.success() {
            return PathBuf::from(
                String::from_utf8(output.stdout)
                    .expect("lean --print-prefix returned invalid UTF-8")
                    .trim(),
            );
        }
    }
    elan_toolchain().join("")
}

fn elan_toolchain() -> PathBuf {
    let elan =
        PathBuf::from(std::env::var("HOME").expect("HOME unset")).join(".elan/toolchains");
    let mut candidates: Vec<PathBuf> = std::fs::read_dir(&elan)
        .unwrap_or_else(|e| {
            panic!("cannot run `lean --print-prefix` and cannot read {}: {e}", elan.display())
        })
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("leanprover--lean4---v4.33."))
        })
        .collect();
    candidates.sort();
    candidates
        .pop()
        .expect("no lean on PATH and no leanprover--lean4---v4.33.* elan toolchain found")
}

fn compile_echo_lean(output: &Path) {
    let src = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("manifest dir"))
        .join("tests/lean/Echo.lean");
    let ok = Command::new("lean")
        .arg(&src)
        .arg("-c")
        .arg(output)
        .status()
        .is_ok_and(|s| s.success());
    if ok {
        return;
    }
    let lean = elan_toolchain().join("bin/lean");
    let status = Command::new(lean)
        .arg(&src)
        .arg("-c")
        .arg(output)
        .status()
        .expect("failed to run elan lean");
    assert!(status.success(), "lean -c on Echo.lean failed: {status}");
}

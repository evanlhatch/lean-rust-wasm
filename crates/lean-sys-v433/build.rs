//! Build script for lean-sys-v433.
//!
//! Discovery: `LEAN_SYS_ROOT` (a Lean toolchain prefix) wins; else
//! `lean --print-prefix` (resolves through the elan shim); else the elan
//! toolchains dir is scanned for `leanprover--lean4---v4.33.*` — the crate is
//! pinned to the 4.33 ABI (see lean-compat.md).
//!
//! Linking is STATIC against the toolchain's archives (the shared
//! `libleanshared.so` path is where the upstream crate's open bugs live; see
//! notes/studies/cedar-study.md). Test fixture: `tests/lean/Smoke.lean` is
//! compiled with `lean -c` and linked into this package's targets so
//! `tests/smoke.rs` can call into Lean.
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    if let Ok(docs_rs) = std::env::var("DOCS_RS") {
        // Detected build on `docs.rs`, so skip trying to link in Lean and just build docs
        if docs_rs == "1" {
            return;
        }
    }

    println!("cargo:rerun-if-env-changed=LEAN_SYS_ROOT");
    println!("cargo:rerun-if-changed=tests/lean/Smoke.lean");

    // Step 1: find the Lean toolchain prefix
    let lean_dir = lean_prefix();
    let lib_dir = lean_dir.join("lib/lean");
    let toolchain_lib_dir = lean_dir.join("lib");

    for archive in ["libInit.a", "libleanrt.a"] {
        assert!(
            lib_dir.join(archive).exists(),
            "{} not found under {} — is this a v4.33 toolchain prefix?",
            archive,
            lib_dir.display()
        );
    }

    // Step 2: compile the smoke-test Lean module to C, then to a static lib
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR unset"));
    let smoke_c = out_dir.join("smoke_fixture.c");
    compile_smoke_lean(&smoke_c);
    cc::Build::new()
        .file(&smoke_c)
        .include(lean_dir.join("include"))
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-label")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .compile("lean_sys_v433_smoke");

    // Step 3: link the runtime statically (mirrors the verified-ledger
    // build.rs; symbol presence verified against the v4.33.0 archives)
    println!("cargo:rustc-link-search=native={}", lib_dir.display());
    println!(
        "cargo:rustc-link-search=native={}",
        toolchain_lib_dir.display()
    );
    println!("cargo:rustc-link-arg=-Wl,--start-group");
    for lib in ["Lean", "Init", "Std", "leancpp", "leanrt"] {
        println!("cargo:rustc-link-lib=static={lib}");
    }
    println!("cargo:rustc-link-arg=-Wl,--end-group");
    for lib in ["gmp", "uv"] {
        println!("cargo:rustc-link-lib=static={lib}");
    }
    // The toolchain's C++ runtime, dynamic (nix's cc is clang+libstdc++;
    // Lean's archives want libc++ — keep exactly one C++ runtime in play).
    for lib in ["c++", "c++abi"] {
        println!("cargo:rustc-link-lib=dylib={lib}");
    }
    for lib in ["m", "dl", "pthread"] {
        println!("cargo:rustc-link-lib=dylib={lib}");
    }
    println!(
        "cargo:rustc-link-arg=-Wl,-rpath,{}",
        toolchain_lib_dir.display()
    );
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
    // Elan fallback: no shim on PATH (e.g. bare devenv shells).
    let elan = PathBuf::from(std::env::var("HOME").expect("HOME unset")).join(".elan/toolchains");
    let mut candidates: Vec<PathBuf> = std::fs::read_dir(&elan)
        .unwrap_or_else(|e| panic!("cannot run `lean --print-prefix` and cannot read {}: {e}", elan.display()))
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

fn compile_smoke_lean(output: &Path) {
    let src = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("manifest dir"))
        .join("tests/lean/Smoke.lean");
    let ok = Command::new("lean")
        .arg(&src)
        .arg("-c")
        .arg(output)
        .status()
        .is_ok_and(|s| s.success());
    if ok {
        return;
    }
    // Elan fallback (no shim on PATH), mirroring `lean_prefix`.
    let elan = PathBuf::from(std::env::var("HOME").expect("HOME unset")).join(".elan/toolchains");
    let mut candidates: Vec<PathBuf> = std::fs::read_dir(&elan)
        .expect("cannot read elan toolchains dir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("leanprover--lean4---v4.33."))
        })
        .collect();
    candidates.sort();
    let lean = candidates
        .pop()
        .expect("no v4.33 elan toolchain")
        .join("bin/lean");
    let status = Command::new(lean)
        .arg(&src)
        .arg("-c")
        .arg(output)
        .status()
        .expect("failed to run elan lean");
    assert!(status.success(), "lean -c on Smoke.lean failed: {status}");
}

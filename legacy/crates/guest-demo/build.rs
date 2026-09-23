//! Build script for the wasm32-wasip3 component link.
//!
//! std on wasip3 passes `-lc` to wasm-component-ld even for a pure-Rust
//! crate; rustc's self-contained dir ships only the crt objects, not
//! wasi-libc. This crate has no C of its own, so it adds the SDK
//! sysroot lib dir itself. No-op everywhere except the custom p3
//! target with `WASIP3_SYSROOT` set (devenv/lang/wasm.nix).

use std::env;
use std::path::PathBuf;

fn main() {
    let Ok(target) = env::var("TARGET") else {
        return;
    };
    if !target.contains("wasip3") {
        return;
    }
    let Ok(sysroot) = env::var("WASIP3_SYSROOT") else {
        return;
    };
    let libdir = PathBuf::from(sysroot).join("lib").join("wasm32-wasip3");
    println!("cargo:rustc-link-search=native={}", libdir.display());
    println!("cargo:rerun-if-env-changed=WASIP3_SYSROOT");
}

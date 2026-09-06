# WASM component toolchain — OPT-IN via profile: devenv --profile wasm
#
# Curated package list (wasmtron pipeline):
#   wasm-tools  — compose, component wit, validate — core of the pipeline
#   wasmtime    — compile AOT CLI, dev/CI driver (library comes via cargo)
#   binaryen    — wasm-opt for the release pipeline
#   wabt        — wasm2wat/wasm-validate for debugging, wasm2c for native-AOT
#   wit-bindgen — generated bindings
#   wac-cli     — component composition
#
# Guest linking (notes/decision-wasip3-linking.md, build-tested):
#   linker = nixpkgs wasm-component-ld + llvmPackages_23.lld (lld 23
#   accepts --cooperative-threading; lld 21/22 reject it). wasi-sdk
#   shrunk to SYSROOT-ONLY (nixpkgs wasilibc v32 lacks
#   __wasilibc_futex_wake — added upstream after wasi-sdk-32; re-test
#   when wasilibc > 32 or wasi-sdk >= 35 lands).
{ pkgs, lib, ... }:
let
  # wasi-sdk-34: sysroot ONLY (pure file copy — no ELF binaries, no
  # patchelf). The linker comes from nixpkgs (decision note). aarch64
  # asset; add per-system hashes when a second host appears.
  wasiSdkTarball = pkgs.fetchurl {
    url = "https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-34-rc.2/wasi-sdk-34.0-rc.2-arm64-linux.tar.gz";
    hash = "sha256-hb3N+itPqOH98Z1eDT/tAe/W6BgdSibhat7z/6+KjeY=";
  };
  wasiSdkSysroot = pkgs.runCommand "wasi-sdk-sysroot-34.0-rc.2" { } ''
    mkdir -p $out
    cp -r ${wasiSdkTarball} sysroot.tar.gz
    mkdir extract
    tar -xzf sysroot.tar.gz -C extract
    cp -r extract/wasi-sdk-34.0-rc.2/share $out/share
  '';

  # wasm-component-ld execs `wasm-ld` via PATH — force lld 23 ahead of
  # anything else (profile carries lld 21 for aarch64 host linking).
  wasmComponentLdWasip3 = pkgs.writeShellScriptBin "wasm-component-ld-wasip3" ''
    export PATH="${pkgs.llvmPackages_23.lld}/bin:$PATH"
    exec ${pkgs.wasm-component-ld}/bin/wasm-component-ld "$@"
  '';
in
{
  packages = with pkgs; [
    lld
    lz4

    # ── WASM component tooling ──
    wasm-tools # compose, component wit, validate
    wasmtime # compile AOT CLI, dev/CI driver
    binaryen # wasm-opt for the release pipeline
    wabt # wasm2wat/wasm-validate debugging, wasm2c native-AOT
    wit-bindgen # generated bindings
    wac-cli # component composition

    # ── wasip3 guest linking (per decision note) ──
    wasm-component-ld # component linker (execs wasm-ld from PATH)
    llvmPackages_23.lld # wasm-ld 23: accepts --cooperative-threading
    wasmComponentLdWasip3 # stable-name wrapper for rustc -C linker
  ];

  env = {
    # Guest build inputs (consumed by RUSTFLAGS_WASIP3 + future
    # wasm-guest-* recipes).
    WASIP3_SYSROOT = "${wasiSdkSysroot}/share/wasi-sysroot";

    # Guest link flag set (wasmtron-verified). Use via
    # `RUSTFLAGS="$RUSTFLAGS_WASIP3" cargo build --target ...`:
    # linker first, panic=abort (no unwinding), stack headroom for std
    # formatting + interpreter state.
    RUSTFLAGS_WASIP3 = lib.concatStringsSep " " [
      "-C lto=no"
      "-C panic=abort"
      "-C debuginfo=1"
      "-C linker=wasm-component-ld-wasip3"
      "-C link-arg=-z"
      "-C link-arg=stack-size=4194304"
    ];

    WASM_WASIP3 = "1";
  };
}

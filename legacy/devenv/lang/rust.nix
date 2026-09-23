# Rust language module — always on.
{ pkgs, config, lib, ... }:
let
  lib' = import ../_lib.nix { inherit pkgs lib config; };
  mkHook = lib'.mkHook;
  mkToggle = lib'.mkToggle;
in
{
  languages.rust = {
    enable = true;
    channel = "nightly";
    components = [
      "rustc"
      "cargo"
      "clippy"
      "rustfmt"
      "rust-analyzer"
      "rust-src"
      "miri"
      "rustc-dev"
      "llvm-tools-preview"
    ];

    # Build flags in two sets (sheath pattern):
    #   RUSTFLAGS      — normal builds (nightly-only speed flags included)
    #   RUSTFLAGS_FIX  — cargo fix / clippy --fix (no -Zthreads; the
    #                    re-entrant subprocess lock model in cargo fix
    #                    conflicts with parallel frontend threads).
    # NOTE: no -fuse-ld flag — the linker is managed by devenv's
    # languages.rust.wild.enable option, not via RUSTFLAGS.
    # NOTE: -C debuginfo is NOT set here — per-package profile overrides in
    # Cargo.toml control it (deps get none, workspace crates line-tables).
    rustflags = lib.concatStringsSep " " [
      "-C lto=off"
      "-C codegen-units=256"
      "-C opt-level=1"
      "-Zshare-generics=y"
      "-Zthreads=8"
      "-Zpolonius=next"
      "-Zinline-mir"
      "-Zub-checks"
      "-C target-cpu=native"
    ];

    wild.enable = true;
  };

  # ── Rust infrastructure packages ──────────────────────────────────
  packages = with pkgs; [
    cmake
    cargo-sweep

    # Toolchain support
    libclang # bindgen dlopens libclang at build time
    llvmPackages.libllvm # bolero libFuzzer backend
    llvmPackages.libclang

    # Testing
    cargo-nextest

    # Development
    bacon # TDD watch mode
    cargo-watch

    # Dependency management
    cargo-edit
    cargo-outdated
    cargo-machete
    cargo-deny

    # Analysis
    cargo-hack
    cargo-bloat
    cargo-llvm-lines
    cargo-expand

    # Property testing
    cargo-bolero

    # Mutation testing
    cargo-mutants

    # Build cache (server starts on demand; no daemon)
    sccache
  ];

  # ── Environment ────────────────────────────────────────────────
  env = {
    LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";

    RUSTFLAGS_FIX = lib.mkForce (lib.concatStringsSep " " [
      "-C lto=off"
      "-C codegen-units=256"
      "-C opt-level=1"
      "-Zshare-generics=y"
      "-C target-cpu=native"
    ]);

    # RUSTC_WRAPPER intentionally not set — workspaces manage sccache via
    # .cargo/config.toml (avoids "server not running"; starts on demand).

    # WASM builds: the dev rustflags carry `-C target-cpu=native` + host
    # -Z flags that break wasm targets. Use this set instead (wasmtron
    # pattern) via `just check-wasip3` / `just check-wasm`.
    RUSTFLAGS_WASIP3 = lib.concatStringsSep " " [
      "-C lto=no"
      "-C panic=abort"
      "-C debuginfo=1"
    ];
    RUSTFLAGS_WASM32 = "-C lto=no -C panic=abort -C debuginfo=1";

    # nexttest default runner
    CARGO_TEST_RUNNER = "nextest";
    NEXTEST_PROFILE = "default";

    # bolero
    BOLERO_LIBFUZZER_PATH = "${pkgs.llvmPackages.libllvm}/lib/libLLVM.so";
    BOLERO_FUZZER = "libfuzzer";
    BOLERO_CORPUS_DIR = "${config.env.DEVENV_STATE}/bolero-corpus";
  };

  # ── Utility scripts ───────────────────────────────────────────────
  scripts = {
    # cargo fix with RUSTFLAGS_FIX (no -Zthreads — avoids lock server
    # timeout from re-entrant cargo rustc subprocess + parallel frontend).
    # Separate target dir (target-fix) avoids IPC conflicts with the cached
    # incremental state; CARGO_INCREMENTAL=0 prevents incremental lock
    # contention.
    cargo-fix.exec = ''
      RUSTFLAGS="$RUSTFLAGS_FIX" CARGO_INCREMENTAL=0 CARGO_TARGET_DIR="${config.env.DEVENV_ROOT}/target-fix" cargo fix --allow-dirty "$@"
    '';
    cargo-clippy-fix.exec = ''
      RUSTFLAGS="$RUSTFLAGS_FIX" CARGO_INCREMENTAL=0 CARGO_TARGET_DIR="${config.env.DEVENV_ROOT}/target-fix" cargo clippy --fix --allow-dirty "$@"
    '';
  };

  # ── git-hooks (format/hygiene live in dev/formatters.nix) ──
  # git-commit env lacks cc/PATH, so wrap clippy with the compiler bins
  # (mkHook from _lib.nix; the nightly toolchain lives in .devenv/profile).
  git-hooks.hooks = {
    clippy = {
      enable = true;
      entry = ''
        ${mkHook {
          command = "cargo-clippy";
          bins = with pkgs; [ stdenv.cc lld binutils ];
          paths = [ "${config.env.DEVENV_ROOT}/.devenv/profile/bin" ];
          args = "clippy --all-targets --all-features";
        }}
      '';
    };
    check-merge-conflicts.enable = true;
    forbid-new-submodules.enable = true;
    cargo-deny = {
      enable = true;
      pass_filenames = false; # deny does not accept file args
      entry = ''
        ${mkHook {
          command = "${pkgs.cargo-deny}/bin/cargo-deny";
          paths = [ "${config.env.DEVENV_ROOT}/.devenv/profile/bin" ];
          args = "check";
        }}
      '';
    };
  };

  enterShell = ''
    export CARGO_BUILD_JOBS=$(($(nproc) - 1))
    mkdir -p "${config.env.DEVENV_STATE}/bolero-corpus"

    # ── Disk autoprune: bound build bloat, keep fresh caches for speed ──
    # cargo never prunes old build-script OUT_DIRs or incremental state;
    # sweep the stale (>5d) ones on every shell entry. Whole target dirs
    # idle >30d get removed entirely. Fresh caches survive → dev loop fast.
    if [ -d target ]; then
      find target/debug/incremental target/debug/build -mindepth 1 -maxdepth 1 -type d -mtime +5 -exec rm -rf {} + 2>/dev/null || true
    fi
    find . -maxdepth 4 \( -name .git -o -name .jj -o -name .devenv -o -name node_modules \) -prune -o \
         -type d -name target -mtime +30 -prune -exec rm -rf {} + 2>/dev/null || true

    # incremental compiles off by default (bloat guard). Override per-session
    # with `CARGO_INCREMENTAL=1` for a hot edit loop; autoprune bounds it.
    export CARGO_INCREMENTAL=0
  '';
}

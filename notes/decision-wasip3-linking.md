# Decision: wasip3 guest linking — 2026-09 (subagent decision-test)

## Verdict: (b) wasi-sdk extraction STAYS, but shrinks to sysroot-only.

## Verified by build test (not speculation)

- **nixpkgs `wasm-component-ld` 0.5.29 + `llvmPackages_23.lld` WORKS**:
  linked a nightly `-Z build-std` wasip3 cdylib against wasi-sdk-34's
  wasip3 libc (9.2MB .wasm). lld 23 accepts `--cooperative-threading`;
  lld 21/22 (nixpkgs default + rust-lld) reject it.
- **nixpkgs `wasilibc` FAILS for wasip3 std**: v32's libc.a lacks
  `__wasilibc_futex_wake` (added upstream after wasi-sdk-32) and its
  CMake only enables thread support for `-threads` triples. Version-
  too-old, not flag-starved. Also not a sysroot-shaped output.
  Repro + threads-rebuild experiment: /tmp/wasip3-link-test,
  /tmp/wasilibc-threads.nix.
- Test tree: /tmp/wasip3-link-test (trivial cdylib, wasmtron's target
  JSON, both linkers). Repro commands in the subagent report.

## Consequence

1. `wasm-ld`/`wasm-component-ld` come from nixpkgs
   (`llvmPackages_23.lld` on PATH ahead of the profile; lld 23 is an
   rc — re-verify on release).
2. The wasi-sdk derivation shrinks to **sysroot-only** (drop the bin/
   dylibs/rpath patchelf block — the linker no longer comes from it).
3. Re-test when nixpkgs wasilibc > 32 or wasi-sdk ≥ 35 ships a
   sysroot nixpkgs can mirror.

## Rejected alternatives

- nixpkgs wasilibc as sysroot: futex symbols missing (above).
- Keep full wasi-sdk linker: duplicate of llvmPackages_23.lld, plus
  the patchelf/rpath maintenance burden.

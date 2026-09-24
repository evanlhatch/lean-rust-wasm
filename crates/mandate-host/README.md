# mandate-host

The honest host seed: a CONSUMER of the checked artifacts
(`notes/v3/03-bidirectional.md` — Lean owns meaning, Rust owns
implementation).

## What the host IS

- It loads `gen/wasm-slice.wasm`, verifies it against its
  `.hdr` sidecar (the content hash re-derived consumer-side — the
  `Kit.Emit.bytesHash` LCG fold, pinned against the committed sidecar
  by test), and runs its `answer` export to the golden `i64 42`.
- It checks the artifact set's completeness (`wasm-slice.wasm`,
  `wasm-slice.wasm.hdr`, `schema-slice.wit`) and the WIT surface's
  presence (the `macht:slice` package, the GENERATED header).
- Any drift — bytes, sidecar, or surface — is a typed STARTUP REFUSAL
  (`HostError`), never a silently-different execution.

## What the host ISN'T

- No second semantics: no re-implementation of the model, the codec,
  or the schema types. The artifacts are the only authority; the host
  pins identity (hashes), not correctness — correctness is
  Lean's (notes/v3/03 §5).
- No panics on real error paths: the failure surface is the typed
  `HostError` enum (notes/v3/12 §8). The fast-observe fault-registry
  integration (`@[host_fault]` E-codes, causal trees, span coverage)
  is a LATER order; each variant maps onto one future fault row.

## Build

```
export PATH="/home/evan/lean-rust-wasm/legacy/.devenv/profiles/wasm/profile/bin:$PATH"
export CC=/home/evan/lean-rust-wasm/legacy/.devenv/profiles/wasm/profile/bin/cc
cargo test
```

Deps: `wasmtime 47` (the engine — version twin of
legacy/crates/guestlang-host, features trimmed to core modules) +
`thiserror 2` (the typed-error derive). Nothing else.

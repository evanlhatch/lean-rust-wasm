# mandate-host

The honest host seed: a CONSUMER of the checked artifacts
(`notes/v3/03-bidirectional.md` — Lean owns meaning, Rust owns
implementation).

## What the host IS

- It loads `gen/wasm-slice.wasm`, verifies it against its
  `.hdr` sidecar (the content hash re-derived consumer-side — the
  `Kit.Emit.bytesHash` LCG fold, pinned against the committed sidecar
  by test), and runs its `answer` export to the golden `i64 42`.
- It loads the COMPONENT path the same way: `gen/component-slice.wasm`
  (the guest function — LCNF-compiled — wrapped as a component through
  the canonical-ABI scalar fragment, the world `gen/component-slice.wit`
  as the contract side) — its `add64 : (u64, u64) -> u64` export is
  called with typed values to the golden `5`; the signature teeth are
  the engine's typed lift, the world surface is presence-checked (a
  world/component skew refuses).
- It checks the artifact set's completeness (`wasm-slice.wasm`,
  `wasm-slice.wasm.hdr`, `schema-slice.wit`, and the component lane's
  trio) and the WIT surfaces' presence (the `macht:slice` package, the
  GENERATED headers).
- Any drift — bytes, sidecar, or surface — is a typed STARTUP REFUSAL
  (`HostError`), never a silently-different execution.
- THE LIFECYCLE (`lifecycle.rs`): the host's phases — `unloaded →
  loaded → instantiated → running` + the terminal `stopped`/`failed`
  — are a MACHINE, modeled Lean-side as `Machines.HostLifecycle`
  (a `machine!` declaration: the transition table, the invariant, the
  conformance battery). The implementation's discipline: every phase
  boundary guards the model's legality (an illegal transition refuses
  with the TYPED `HostError::Lifecycle` — a run export before
  instantiation refuses); the model's refusal rows
  (`refuseLoad`/`refuseInstantiate`/`refuseStart`/`trap`) are explicit
  transitions into `Failed` (the escape paths, 03 §4). Evidence
  level: the DIFFERENTIAL — `tests/lifecycle.rs` drives every legal
  row through the real host, sweeps every illegal (event, from) pair,
  and pins the model table mirror (`MODEL_TRANS`) against
  `Machines.HostLifecycle.hostLifecycleTrans` (tested agreement,
  never a theorem).
- THE LIVE LOOP (`live.rs`): the propose/check/commit adapter over
  the journal — the Lean checker's differential mirror (the commit
  duel). Its journal honesty: the accepted effect is journaled BEFORE
  the in-memory state moves (memory never runs ahead of the durable
  log), so a crash after the journal effect recovers on reopen (the
  durable log IS the truth); a proposal that never committed leaves
  no trace; a torn tail recovers to the last good frame AND reports
  the cut (`Live::recovery`). Pinned in `tests/lifecycle.rs`.

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
legacy/crates/guestlang-host, features trimmed to core modules + the
component-model path) + `thiserror 2` (the typed-error derive) +
`wat` (dev — the tamper/golden teeth build their variant binaries,
components included). Nothing else.

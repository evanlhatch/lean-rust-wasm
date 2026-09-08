# lean-rust-wasm

**guestlang** — Lean schemas, WASM components, Rust hosts.

Lean is the type-definition and policy layer: schemas, state machines,
error taxonomies — kernel-checked, proofs erased before runtime. WASM
components are the universal boundary (WIT is the contract). Rust hosts
them. Codegen is byte-tie enforced: artifacts are committed, drift
fails CI.

## Layout

```
lean/               Lean packages (kernel-checked source of truth)
  TestKit/          test harness: golden byte-tie, negative controls
  Machines/         guarded state machines, refinement, composition
  codegen-core/     registry machinery + emitter discipline
  schema-lang/      Ty universe, items, resolution, compat diff, emitters
  faults/           failure-mode registry -> fast-observe error! blocks
crates/forge        pipeline orchestrator (gen / gen --check byte-tie)
wit/                generated WIT (committed, byte-tie)
src/                host crate consuming generated types
notes/              decisions (dated, with rejected alternatives)
```

## The loop

```
devenv shell --profile wasm
just gen            # lake emitters -> wit/ + src/schema_generated.rs
just gen-check      # byte-tie: regenerate in memory, diff
just gates          # gen-check + wit-check + lean-axioms
just watch-gen      # watchexec wraps the SAME commands
```

Edit `lean/schema-lang/SchemaLang/Spec/Demo.lean`, run `just gen`,
consume the types from Rust. Wrong references fail at Lean elaboration;
drift fails CI; the canonical parser validates the WIT.

## Profiles

`rust` + `lean` are always on. Opt-ins: `wasm` (component toolchain +
wasip3 guest linking), `js`, `docs`, `cloudflare`.

```
devenv shell --profile wasm
```

## Status

Pre-alpha. See `notes/` for decisions. Packages graduate to Reservoir
when their APIs stabilize.

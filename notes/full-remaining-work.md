# The full remaining work

## Where we are

Seven Lean packages green (TestKit, Machines, dbsp, codegen-core,
substrait, schema-lang, faults), three Rust crates (forge, steel-host,
guest-demo), six byte-tied artifacts (WIT world, schema types, Vortex
dtypes, ext-dtype vtables, delta contracts, fault registry), eighteen
test groups passing, all axiom-clean, all gates green.

The pipeline works: `@[schema]` on a Lean structure reflects at
elaboration into registry items; the emitter plugins fold those items
into WIT/Rust/Vortex artifacts; forge byte-ties them into an OCI store;
wasmtime loads the component. The loop closes.

What follows is everything NOT yet built, organized by how far it is
from the current state.

---

## Stage closure (the A-G stages — notes/execution-guide.md)

These are the immediate pipeline-closure stages. Each is independently
demoable. The execution guide has the details; this is the summary.

### A. Unify the spec surface

Right now there are two sources of truth: `Demo.lean` (native
structures with `@[schema]`) and `Spec/Demo.lean` (hand-written `List
Item` data). They must become one.

The reflection (`Meta/Reflect.lean`) currently handles structures only.
It needs to also reflect:
- **Inductives** (variants): read constructor args as payload types,
  register as `Item.variant`
- **Functions**: a `@[schema_fn]` attribute on defs — read the type,
  extract params/ret, register as `Item.func`

Once this works, `Spec/Demo.lean` is deleted — the hand-written data
is replaced by the reflection. The test fixtures (broken/dup/fwd
universes used in resolution tests) move into the test file itself.

Done when: `lake build` green, tests green, `schema-gen` emits the
same artifacts (byte-tie against existing goldens).

### B. Typed host bindings from WIT

The steel-host currently calls guest functions through untyped
`wasmtime::Val` marshalling. The generated WIT defines the interface —
use `wasmtime::component::bindgen!` (or wit-bindgen) to generate
typed host-side bindings.

This turns `call("get-user", &[Val::U64(42)])` into
`gateway.get_user(42)` — the args and return are structured types
connected to `schema_generated.rs`. The "Lean defines the ABI" proof:
the host's API is generated from the Lean-defined world.

Done when: steel-host test calls `add(1,2)` through typed bindings
(not raw `Val`), and `get-user` returns a structured `User`.

### C. Generated host faults

The steel-host hardcodes error codes E110-E113 in its valves module.
The guest's faults (E100-E103) come from the Lean registry. They should
share ONE allocator.

Extend the faults emitter to generate a second module — `HostFault` —
from the same `FailureModeItem` registry. Add host-specific faults
(engine error, missing export, fuel exhausted, timeout) to the
registry. Replace the hardcoded codes.

Done when: `lookup_error("E110")` resolves from both host and guest.
The E-code means the same thing across the boundary.

### D. Guest exports from schema funcs

The guest-demo's exports are hand-written `#[no_mangle]` functions.
The schema's `func` items should generate the export stubs.

Extend reflection to handle `@[schema_fn]` on defs. The emitter
generates a guest-side module of export signatures. The guest-demo
imports the stub and implements the handlers.

Done when: the guest's exports match the schema's func items.

### E. Certified delta impls

The `delta_generated.rs` emits `UserChange` with a `dbsp::Change` impl —
but the impl body is a leaf string with no proof. The `ChangeSpec`
theorems (patch/invert/diff_correct) should have EXECUTABLE Rust tests.

The delta emitter generates `#[cfg(test)]` tests per record:
```rust
#[test]
fn change_roundtrip() {
    let user = User { ... };
    let delta = UserChange::Update(user.clone());
    assert_eq!(delta.patch(&user), user);  // diff_correct, executed
}
```

Done when: `cargo test` proves the change laws on concrete values.

### F. Rust round-trip gate

The Lean side has `Decode.lean` proving `parse ∘ emit = id` for the
Substrait text format. The Rust side should have the equivalent for
WIT: use `wit-parser` to parse `gateway.wit` back and assert the
schema matches. This catches any drift between what Lean emits and
what the Rust side reads.

### G. The end-to-end demo

One command: `just demo`. Edits the schema, regenerates, builds the
component, loads it in steel-host, calls through typed bindings,
verifies the result. The "edit Lean, get a working component" loop,
closed.

---

## The compiler line (the biggest missing piece)

Everything above closes the TYPE pipeline — Lean schemas → WIT/Rust
artifacts. The full vision also compiles Lean LOGIC (function bodies)
to WASM. This is the deepest layer and the one that makes guestlang a
language, not just a schema tool.

### LCNF → WASM backend

Lean's compiler pipeline (parser → elaborator → kernel → LCNF) is
available as a library. The LCNF (Lean Compiler Normal Form) is the
IR: first-order functions, explicit memory ops, no dependent types
(they're erased). A backend that consumes LCNF and emits WASM
instructions gives you Lean logic running in the guest.

The backend is a Lean compiler plugin (like the C backend and LLVM
backend — they're Lean programs consuming `Lean.Compiler.LCNF`).
When Lean updates, the plugin fails at compile time — not runtime.

What it must handle:
- **Perceus RC**: Lean's reference-counting memory model. Each object
  has a header (tag + refcount + fields). `inc`/`dec` are explicit.
  In-place mutation when rc == 1.
- **Bump allocator**: the guest's heap is a linear-memory bump
  allocator. `memory.grow` when the bump pointer exceeds the limit.
  Objects allocated contiguously, freed by RC reaching zero.
- **String**: UTF-8 bytes in linear memory, (ptr, len) representation.
  `String.concat` allocates + copies.
- **Array**: flat array of same-typed values. (ptr, len) or (ptr, len,
  capacity). `Array.push` may reallocate.
- **Nat/Int**: fixed-width u64/i64 by default (no libgmp). Big-int as
  a host capability (opt-in).
- **Closures**: (funcref, env-ptr) pairs. The env is a flat allocation
  of captured variables.
- **IO monad**: maps to WASI 0.3 `future<T>`. Each `do` bind is a
  suspension point. The host (wasmtime) schedules.
- **Pattern matching**: compiles to `br_table` or nested `if` chains.
  Lean's match compiler (the `match` equation compiler) does the
  lowering before LCNF.
- **Recursion**: `return_call` (tail-call proposal) for tail-recursive
  functions. Non-tail recursion → the WASM stack (bounded, stack
  overflow = trap).

The pipeline:
```
Lean source → lean4lean kernel → LCNF (proofs erased)
  → our backend plugin (consumes LCNF.Decl)
  → emits WASM MVP instructions (via wasm-encoder, or via C → clang)
  → core WASM module
  → wit-component (adds the WIT interface)
  → component WASM
```

Two backend strategies (choose per deployment):
- **Direct WASM emission**: the Lean plugin emits WASM instructions
  directly (via the `wasm-encoder` crate from Rust, or by emitting
  WAT text). Smaller output, no C toolchain needed.
- **C emission**: the Lean plugin emits C code (like the existing C
  backend), then `clang --target=wasm32-wasip3` compiles it. Gets
  LLVM optimization for free, but needs clang in the build.

Start with C emission (it's the existing Lean backend's model — port
it), then add direct WASM emission later.

### Perceus RC + allocator

The guest's memory management. The allocator is a bump allocator in
linear memory:

```wasm
(global $heap-ptr (mut i32) (i32.const 0))
(func $alloc (param $size i32) (result i32)
  ;; align to 8
  ;; bump the pointer
  ;; memory.grow if over limit
)
```

RC: each object has a header: `{rc : u32, tag : u8, ...}`. `inc` = 
increment the rc field. `dec` = decrement; if 0, free (return to
bump if it's the top allocation, else mark for sweep — v1: leak).

In-place mutation: when rc == 1, the object is exclusively owned —
mutate in place (no copy). This is Lean's `borrowed`/`owned` distinction.

### guestlang-std

The compiled-to-WASM standard library. Written in Lean, compiled by
the backend to WASM. Replaces Lean's Init for the guest:

- `String` — concat, length, substring, comparison
- `Array` — push, get, set, length, map, filter, fold
- `Nat`/`Int` — fixed-width arithmetic, comparison
- `IO` — the WASI 0.3 bindings: stdout, stderr, files, clocks
- `Option`/`Result` — already in the prelude
- `Future`/`Stream` — the WASI 0.3 async primitives

This is ~5-10KB of WASM (the primitives only — no proofs, no tactics).

### lean4lean as WASM component

The compiler itself, compiled to a WASI component. This enables:
- Sandboxed compilation (the compiler can't escape)
- Browser-based IDE (compile Lean in a web worker)
- Hermetic builds (the compiler is a fixed .wasm artifact)

The compiler is big (~8MB WASM) — it's loaded on demand, not shipped
with every component.

---

## The runtime (guestlang-rt — the standalone product)

The embeddable WASM interpreter crate. This is the "batteries included"
product: a Rust crate that runs pre-compiled guestlang components.

### The crate

```toml
[package]
name = "guestlang-rt"
```

- **wasmi 2.0** as the engine (pure Rust, ~1MB, deterministic, fuel-
  metered)
- **Core WASM only** (no component model — wasmi doesn't support it;
  the host provides the async wrapper)
- **Fuel metering** native (the interpreter counts instructions)
- **Snapshot/restore**: serialize the interpreter state (stack, heap,
  env) to bytes; resume later. Via rkyv (zero-copy) or a custom
  serializer (the object model is ours — we control the layout).
- **Worker pool** (Monty pattern): subprocess isolation for untrusted
  scripts. Crash/stack-overflow/OOM kills only the worker; the host
  replaces it.
- **Resource limits**: custom allocator with memory budget;
  instruction counter; stack depth guard. All enforced natively by
  wasmi.

### Multi-frontend

The runtime doesn't know (or care) what language produced the WASM.
Lean compiles to core WASM; EdgePython compiles to core WASM; both run
in the same runtime. The IR seam (the stable interchange format) is
what makes this work — both frontends emit the same shape.

---

## The transport/distribution layer

### wRPC over QUIC

Component-to-component RPC using the WIT interfaces. The internal mesh
protocol: components call each other's exports over the network, with
WIT types serialized on the wire.

- **wrpc** (Bytecode Alliance) — the WIT-native RPC protocol
- **iroh** (n0-computer) — QUIC-based networking with NAT traversal
- The delta-shaped contracts (`stream<change>`) become the wire
  protocol: changes flow as streams, not snapshots

### OCI registry

The local store exists. Add:
- `forge push` / `forge pull` — push/pull to ghcr.io (or any OCI
  registry) via the `oci-wasm` crate
- Content-addressed caching: if two projects use the same component,
  the blob is stored once
- Provenance layers: kernel hash, schema version, axiom-gate report —
  embedded as manifest annotations

### Splicer middleware

Auth, rate-limiting, tracing, logging as INTERPOSED components —
spliced between the caller and the callee by the build pipeline
(splicer or wac). The Lean component stays pure business logic.

The splice-smoke gate: splicer can interpose a passthrough on our
emitted component = independent proof that our WIT is well-formed.

### Component composition

Multiple components linked via `wac` (declarative) or `wasm-tools
compose`. The composed artifact is itself a component — distribution
via OCI.

### Hot-reload

Swap components without restarting the host. The host loads a new
.wasm, instantiates it, routes traffic. State lives in the host (or
in the event log), not in the component.

---

## The proof/verification line

### Schema-indexed expressions (validators)

The full `HasCol`/`HasField` GADT layer: expressions typed by the
schema's field list. `Expr s t n` — a well-typed expression over
schema `s` returning type `t` with nullability `n`. Field access by
name via `HasCol` instance search; misspelled columns are elaboration
errors.

This generates VALIDATORS: functions that check data against the
schema, compiled to WASM, called by the host before processing.

### Session types for WIT conversations

The protocol between two components as a state machine (Machines).
The WIT interface defines the TYPES; the session type defines the
CHOREOGRAPHY (who sends when, what they expect back). Lean proves the
protocol is deadlock-free.

### Saga / workflow

`Machines.Rewind` — a `RewindableMachine` whose `revert` is the
compensation. The rewind laws (rewind-K = undo-K) prove that
compensation is correct. The order lifecycle as a machine: placed →
paid → shipped → delivered, with compensation on failure.

### Delta-CRDT replicas

`Dbsp.ChangeSpec` across replicas. Each replica applies deltas;
convergence is the theorem (all replicas that receive the same deltas
reach the same state). The WASM determinism + the change group
commutativity = convergence for free.

### Talos

The WASM interpreter written in Lean, with weakest-precondition
calculus. Verifies that the emitted WASM matches the LCNF semantics —
the compiler backend's correctness proof. Dev-dep only (AGPL).

### Deterministic simulation testing

Model the clock and network in Lean. Explore all interleavings of
concurrent events. Prove no deadlock, no data loss. The WASM
determinism makes this possible: same inputs → same outputs, always.

---

## The ecosystem line

### Reservoir publishes

All packages as independently versioned libraries:
- `guestlang-testkit` — the test harness
- `guestlang-machines` — state machines
- `guestlang-dbsp` — the delta theory
- `guestlang-codegen` — the emitter framework
- `guestlang-substrait` — the Substrait query language
- `guestlang-schema` — the schema language
- `guestlang-faults` — the error registry
- `fast-observe-lean` — the fast-observe companion (graduates to the
  fast-observe repo)

### EdgePython frontend

A second language targeting the same IR seam. EdgePython compiles
Python to WASM; the output feeds the same runtime (guestlang-rt) and
the same schema contracts. Multi-frontend conformance: same fixtures →
same IR.

### API docs

From WIT via wit-bindgen markdown. The Astro Starlight site (already
scaffolded) populated with generated docs.

---

## The dependency graph

```
Stages A-G (the loop)
    ↓
LCNF backend → guestlang-std → Perceus RC
    ↓
guestlang-rt (wasmi standalone)
    ↓
wRPC + OCI registry + splicer
    ↓
Talos + DST + session types + CRDT
    ↓
Reservoir + EdgePython
```

The critical path: Stages A-G → LCNF backend → guestlang-rt → wRPC.
Everything else is parallel or downstream.

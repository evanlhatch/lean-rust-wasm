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

STATUS: A-G ALL DONE (committed: Stage A ppkylynr, Stage B przmkomy,
Stage C yvyzqplm, Stages E+F xywqzlop, Stage G = the `just demo`
recipe + this doc). Stage D is subsumed: the guest's export signatures
come from the SSOT wit/gateway.wit via wit-bindgen `generate!` — the
exports ARE the schema's func items by construction.

Each is independently demoable. `just demo` = gen + component build +
typed-call tests in one command.

### A. Unify the spec surface — DONE

Single SSOT: `Demo.lean` with `@[schema]`/`@[schema_fn]`/
`@[schema_resource]`; records/variants/funcs/resources all reflected;
`Spec/Demo.lean` deleted; WIT emitters write `../../wit/*` so forge
byte-ties them.

### B. Typed host bindings from WIT — DONE

`bindings.rs`: `bindgen!({ path: "../../wit/gateway.wit", world:
"gateway" })`. wasmtime 47's crate-level `async` feature is on by
default and FULLY supported — only the `bindgen!` macro OPTION is gone:
async-ness is inferred from the WIT function TYPES (`async func` →
generated `async fn call_*` taking wasmtime 47's `Accessor`). Typed
tests: `get_user(42)` returns structured `User` (sync path);
`watch-orders` runs through the wasi 0.3 async ABI end-to-end —
`store.run_concurrent(async |accessor| iface.call_watch_orders(
accessor, EmptyCart).await)` (test `gateway_typed_watch_orders_async_abi`).
WASI p3 + bindgen check needs the nix cc wrapper:
`export CC=.../profiles/wasm/profile/bin/cc`.

### C. Generated host faults — DONE

`Faults/Spec/Host.lean` registers hostFaults; `faults-gen` emits
`src/host_faults_generated.rs` (codes E110-E113 via `allocateHost`);
steel-host's hand-written `error!` block deleted — `valves.rs` now
re-exports the generated enum. Done-criteria test:
`lookup_error("E110")` (host) and `("E100")` (guest) resolve from ONE
fast-observe registry.

### D. Guest exports from schema funcs — DONE (subsumed)

`guest-demo` implements world gateway via `wit-bindgen::generate!` —
export signatures generated from the SSOT; `get-user` + `watch-orders`
+ `resource db` all match the schema's func/resource items.

### E. Certified delta impls — DONE

The delta emitter appends `#[cfg(test)] mod tests`: one patch-
roundtrip test per keyed record, emitted from the Lean Item grammar.
The trait is OURS: `src/dbsp.rs` `trait Change<Row>` (patch +
valid-with-base, mirroring `Dbsp.ChangeSpec`) — NOT the Feldera
crate. `cargo test -p lean-rust-wasm`: 3/3.

### F. Rust round-trip gate — DONE

`crates/steel-host/tests/wit_roundtrip.rs`: wit-parser 0.258 parses
the GENERATED `wit/gateway.wit`; 4 structural tests (record fields,
variant cases+payloads, func sigs incl. `watch-orders`
AsyncFreestanding, world exports). Lean-emitter ↔ Rust-reader drift
now fails CI.

### G. The end-to-end demo — DONE

`just demo`: gen → gateway component build → typed-call + delta +
round-trip tests. The "edit Lean, get a working component" loop,
closed.

### Wasip3-async emitter fix (Load-bearing discovery)

`Async.Future` returns emit as `async func(...) -> a` — NOT
`func(...) -> future<a>`. The component validator rejects the latter:
"the `async` canonical option requires an async function type" — the
async-ness must live in the FUNCTION TYPE (wit-parser 0.258: `async`
prefix on Func, `FunctionKind::AsyncFreestanding`). wit-bindgen then
binds it as a plain Rust `async fn` returning the payload. Tooling
pin: wasm-tools CLI 1.258 (cargo-installed to
~/.local/guestlang-tools) — wit-bindgen 0.61's wit-component 0.258
async-lift encoding predates nixpkgs' 1.256 CLI.

---

## The compiler line (the biggest missing piece)

Everything above closes the TYPE pipeline — Lean schemas → WIT/Rust
artifacts. The full vision also compiles Lean LOGIC (function bodies)
to WASM. This is the deepest layer and the one that makes guestlang a
language, not just a schema tool.

### LCNF → WASM backend (verified from Lean 4.33 source)

**Architecture:** a SEPARATE EXECUTABLE (like `leanir`, the existing
C backend) — not a compiler pass. It imports the module's olean,
re-runs the LCNF pipeline (the impure-phase LCNF is NOT persisted in
oleans), reads the final `Decl`s from `impureExt`, and emits WAT.

**The LCNF Code constructors we handle:**

| Constructor | WASM emission |
|---|---|
| `.let decl k` | compute + `local.set` |
| `.return arg` | load + `return` |
| `.fun λ k` | alloc closure (funcref + env) |
| `.jp`/`.jmp` | WASM `block`/`loop` + `br` |
| `.cases c` | `br_table` or nested `if` (load tag from offset 4) |
| `.inc`/`.dec`/`.del` | `call $rc_inc`/`$rc_dec` (Perceus — already inserted) |
| `.reset`/`.reuse` | v1: skip (leak) |
| `.oset`/`.uset`/`.sset` | `i32.store` |
| `.unreach` | `unreachable` |

**LetValue:** `.lit`→const, `.fvar`→local.get, `.proj`→`i32.load
offset=8+i*w`, `.ctor`→alloc+tag+fields, `.fap`→`call`, `.pap`→closure
alloc, `.box`/`.unbox`, `.isShared`→rc>1 check.

**CtorInfo** (name, cidx, size, usize, ssize) = the object layout —
generates field offsets for proj and sizes for alloc.

**The re-run recipe (what `leanir` does, what we clone):**

```lean
-- 1. Import the module's olean
let env ← Lean.importModules #[`Demo] {}
-- 2. Re-run the LCNF pipeline (produces impure-phase Decl with RC)
Lean.Compiler.LCNF.main declNames {}  -- in CoreM
-- 3. Read final impure decls
let decls := Lean.Compiler.LCNF.getLocalImpureDecls env
-- 4. Emit WAT for each Decl
```

**Pure checkStruct pattern (no monad generalization):** the check
logic runs in a Sum, not Except/do — the CoreM do-block monad
generalization trap is avoided entirely.

### The toolchain: wasm-tools (not wabt)

**STATUS: WORKING END-TO-END (9d83bc56).** `just wasm-compile`:
DemoFn → LCNF re-run → WAT → `wasm-tools parse -g` → validate →
wasmtime `--invoke` (double 21→42, adder 40 2→42, isBig 250→1/42→0).

The emitter (lean/wasm-backend/WasmBackend.lean, ~250 lines):
- scalar ABI: UInt64→i64, UInt8/Bool/UInt32→i32, objects→i32 ptr
  (borrowed scalars are objects — the `@&s : UInt64` shape)
- guestlang layout {rc u32@0, tag u8@4, fields@8}: sproj byte offsets →
  `i64.load offset=8+off`; tag → `i32.load8_u offset=4`
- handled: let/return/cases (tag in temp local, nested if)/fap-
  primitives (binop table)/lits/sproj; inc/dec/del erased (v1 leak);
  pure-only ctors (.fun/.alt on impure code) discharged by absurd
- name section: every func/param/local named in the WAT — profiler +
  backtrace symbols free (parse -g adds DWARF)

Lean gotchas hit: impure-phase applications are `.fap` (NOT `.const` —
pp renders both identically); `s!` interpolates with `{}` (`\{` is a
LITERAL brace); docstrings can't precede `mutual`; UInt64 patterns
aren't matchable (no GMP — recursion waits for guestlang-std loops).

### What the compiler line still needs (in order)

**DONE since (13fec9db): the differential gate + canonical-ABI adapters
+ elab-time gate + gate/axiom coverage — the hardening plan's 5 steps,
all green.**

1. **Pooled allocator + ctor emission** — DONE (a0332a26): size-class
   free lists (Lean runtime model, NOT pure bump), $alloc/$rc_inc/
   $rc_dec; the ctor+sset split handled; full object lifecycle
   verified (reuse across calls, values intact).
2. **RC runtime** — DONE: inc/dec emit real rc calls.
3. **Closures** — DONE (be8f685a): pap objects, funcref table,
   call_indirect trampolines (2 flavors: boxed-target pass-through /
   raw-target unbox+box); oproj; typed box/unbox.
4. **Canonical-ABI adapters** — DONE (13fec9db): _abi wrappers box
   borrowed-scalar params / unbox object results; scalar cases (Bool/
   UInt8) branch on the VALUE (the tag load was objects-only); pick
   works through the component world.
5. **Differential gate** — DONE (13fec9db): GenMain emits the oracle
   program (real Lean calls over generated inputs — 120 rows incl.
   zero/threshold negatives); `lean --run` → diff.json; steel-host's
   wasm_diff test replays every row — 120/120. Lean semantics govern
   the shipped bytes.
6. **@[guest] elab gate** — DONE (349606fc): pure predicate
   (checkExpr) + reasons renderer; Tests/Main.lean positive/negative
   controls (7 guards).
7. **Robustness contract** — DONE (c37edd1d): unsupported constructs
   throw (never silent comments); wasm-backend in lean_pkgs (axiom
   gate covers it).

### Still open (the next session's list)

1. **Strings/arrays** (guestlang-std): UTF-8 (ptr,len) objects;
   Array with capacity; the ops' LCNF = ctor/sset/oset + helper calls.
2. **return_call**: tail-call proposal for tail-recursive functions
   (wabt lacks it; wasm-tools supports `--enable-tail-call`).
3. **multi-arity closures**: sig_1box covers (boxed) → (boxed);
   generalize the trampoline table per signature.
4. **guestlang-rt**: wasmi 2.0 crate — CORE wasm only (the component
   wrapper is wasmtime-side); fuel metering; snapshot/restore via rkyv
   (the object model is ours); worker pool (Monty pattern).
5. **wRPC/QUIC + OCI registry push/pull + splicer middleware** —
   transport/distribution layer (the local OCI store exists).
4. **Canonical ABI + component wrap** — DONE (13fec9db): the demo
   world's adapters; the GATEWAY world's adapters (option<user>, async
   watch-orders) still open.
5. **Strings/arrays**: UTF-8 (ptr,len) objects; guestlang-std.
6. **Tail calls**: `return_call` for tail-recursive functions.

| Step | Tool | Gives |
|---|---|---|
| Validate + DWARF | `wasm-tools validate -g` | Spec check + DWARF from WAT |
| WAT → binary | `wasm-tools parse` | Name section + DWARF embedded |
| Component wrap | `wasm-tools component new` | Core → component (WIT embedded) |
| Component embed | `wasm-tools component embed` | WIT types → custom section |
| Debug | `wasm-tools addr2line` | Binary offset → file:line (via DWARF) |
| Profile | `wasmtime --profile=guest` | Sampling → Firefox Profiler JSON |
| Explore | `wasmtime explore` | WAT → Cranelift IR → native asm (HTML) |
| Traps | `WasmBacktrace` | Stack trace with names (from name section) |

**Skip wabt** — no DWARF, no stack-switching, less active. Use
`wasm-tools parse` for WAT → binary.

**The name section is CRITICAL** — emit function/local names in WAT;
wasmtime's profiler/backtrace use them. Without: `func[0]`, `func[1]`
— useless for debugging.

### Perceus RC + allocator

The RC instructions (`.inc`/`.dec`) are ALREADY IN THE LCNF — inserted
by Lean's `LCNF.rc` pass. We translate to `call $rc_inc`/`$rc_dec`.
`.reset`/`.reuse` → v1: skip (leak).

Bump allocator (~100 lines WAT, hand-written, linked with generated
code). Object layout: `{rc: u32, tag: u8, pad, field_0, field_1, ...}`.

### guestlang-std

Compiled-to-WASM stdlib (String, Array, Nat/Int as u64/i64, IO → WASI
0.3). ~5-10KB WASM.

### lean4lean as WASM component

Compiler sandboxed: `compile: func(source) -> future<component>`.
~8MB WASM, loaded on demand.

### The full pipeline (verified design)

```
Lean source → lean4lean kernel → LCNF.main (re-runs pipeline)
  → impureExt.getState → our backend: emitDecl → WAT
  → wasm-tools parse -g (binary + DWARF + name section)
  → wasm-tools validate → component embed → component new
  → component.wasm → steel-host (wasmtime, epoch/fuel, fast-observe)
```

Debugging chain: WAT (readable) → DWARF (addr2line) → name section
(profiler/backtrace) → wasmtime --profile=guest (flamegraph) →
wasmtime explore (WAT→IR→asm) → WasmBacktrace → fast-observe spans.

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

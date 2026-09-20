# Async ABI + wRPC/QUIC + OCI push/pull — the implementation plan

Grounded in the empirical dissection of the wit-bindgen 0.61 gateway
component (`wasm-tools print` on the extracted core module) and the
existing code (forge's OCI store, guestlang-host's ComponentRuntime, the
differential gate). The plan for each track; the ordering at the end.

---

## Track 1 — the ASYNC ABI (`watch-orders`)

### What the reference ABI looks like (dissected, not guessed)

The wit-bindgen 0.61 gateway component's core exports:

```
[async-lift]demo:gateway/gateway-exports#watch-orders  (param i32 i64) (result i32)
[callback][async-lift]demo:gateway/gateway-exports#watch-orders  ...
cabi_post_demo:gateway/gateway-exports#get-user        (param i32)
demo:gateway/gateway-exports#get-user                  (param i64) (result i32)
```

Readings:

- **get-user (sync)**: `(param i64) (result i32)` — EXACTLY what our
  adapters already emit (the return-area convention:
  MAX_FLAT_RESULTS=1 → the callee returns the pointer to the results
  area; the area holds the option's memory layout). VALIDATED: our
  200-row differential gate is green with this convention.
- **`cabi_post_*`** (the post-return function): `(param i32)` — the
  host calls it AFTER copying the results out, to let the guest
  deallocate the return area. Our adapters DON'T emit one — wasmtime
  calls it only if present; absent = the area leaks (ours is static —
  nothing to free — FINE, but the general case (a big record) needs
  either the post-return free or the static area). DECISION: emit
  `cabi_post_*` as a NO-OP for the static-area adapters (the protocol
  completeness; wasmtime's lift calls it unconditionally IF present —
  emitting a no-op keeps the shape identical to wit-bindgen's).
- **watch-orders (async)**: the async-lift protocol — TWO core exports:
  1. `[async-lift]#watch-orders (param i32 i64) (result i32)` — the
     params = the sync flattening (order-error = a variant →
     [i32 discr, i64 payload] ✓); the RESULT (i32) = the TASK HANDLE
     (the async task's state), not the return area.
  2. `[callback][async-lift]#watch-orders` — the host (the canonical
     lift) calls it to PROGRESS the task (the polling model); the
     callback returns the task's status (pending / completed / ...).
- The task state = wit-bindgen's `SharedTaskState` + the waitable
  registration (`cabi_waitable_register/unregister/clone/drop` — the
  exports the core module carries) — a mini async runtime IN THE GUEST.

### The implementation phases

**1a. `cabi_post_*` emission** (cheap, protocol-complete):
- the backend: for EVERY export-target with a return-area result, emit
  `cabi_post_<name> (param $area i32)` = a no-op (the static area) +
  the export. The canon lift calls it; the shape now matches
  wit-bindgen's byte-for-byte.
- VERIFY: the component still validates + the diff gate stays green.

**1b. the async-lift task machinery (the compiled watch-orders)**:
- the GUEST side (lean/std): the async task state — for a LEAN-compiled
  function the body is SYNC (the list computes immediately) — the task
  protocol = still the shape: the main export = the sync-flat params →
  allocate the task state (a guest object: {status: completed, the
  result area, the waitable registration}) → return the handle; the
  callback export = called by the lift to poll → return "completed"
  (the task finishes on the first poll — the sync body's privilege).
- the backend: for the `async` targets, emit BOTH exports + the task
  state object layout (a new guest object kind: tag 251?).
- the WORLD: the compiled world gains `watch-orders: async func(into:
  order-error) -> list<user>` — the list<user> RESULT (a list of
  RECORDS) = the flattening: the list's elements = the flattened users
  (the per-element flat = 8 values) → the array = n × 32 bytes — the
  guest lowers each user into the array (the adapter's loop generalizes
  the list<string> walk to list<record>).
- VERIFY: the host's typed binding calls watch-orders on the COMPILED
  component (the async await → the task polls → the list) + the
  differential rows (the oracle = Lean's watchOrders eval).

**1c. the REAL async (yielding)**: the compiled Lean functions are
sync — a task that YIELDS (the stream semantics: the changes TRICKLE)
needs the guest to SUSPEND mid-function — that's the stream<T> ABI (the
guest writes INTO a stream handle; the host reads incrementally). The
`stream<user>` (the delta-shaped contract!) = the stream write
builtins. PHASE: after 1b — the guest's watch-orders writes each user
into the stream (the canon `stream.write`-equivalent via the task
machinery) and the host reads incrementally. This is where the
delta-shaped contracts become LITERALLY the wire protocol.

**Risks**: the wit-bindgen 0.61's async-lift = its OWN protocol flavor
(the [callback] exports) — wasi 0.3's FINAL protocol may differ
(the native stackless tasks). Pin to wit-bindgen 0.61/wasmtime 47 (the
existing pins) and note the version coupling.

---

## Track 2 — wRPC/QUIC (the transport-generic mesh)

### The design constraint (the user's)

Transport-GENERIC: the QUIC implementation is behind a seam; the n0
stack (iroh) = the first adapter, not the identity of the layer. "noq"
= the n0-flavored QUIC stack — the seam keeps it swappable.

### The architecture

```
┌───────────────────────────────────────────────────┐
│ crates/wire (NEW) — the transport seam            │
│                                                   │
│ trait Transport {                                 │
│   type Conn;                                      │
│   async fn connect(addr) -> Conn;                 │
│   async fn accept(&mut self) -> Conn;             │
│   // each conn: bidirectional byte streams        │
│   fn open_stream(&self) -> impl Stream;           │
│ }                                                 │
│                                                   │
│ adapter: IrohTransport (n0's QUIC + relay + the   │
│   hole-punching) — the DEFAULT; the other QUICs   │
│   (quinn raw) plug the same trait                 │
└──────────────┬────────────────────────────────────┘
               │
┌──────────────▼────────────────────────────────────┐
│ wRPC (the BA's crate — the WIT-native RPC):       │
│  the SERVER: serve the host's component over the  │
│    transport (the exports = the RPC surface)      │
│  the CLIENT: the remote proxy = the same          │
│    ComponentRuntime API (call/export) — the       │
│    local/remote TRANSPARENCY (the splice layer    │
│    can't tell)                                    │
└───────────────────────────────────────────────────┘
```

### The implementation phases

**2a. `crates/wire` — the Transport trait + the iroh adapter**:
- the trait: connect/accept/open-stream (the byte streams; the
  cancellation via the async drop).
- the iroh adapter: `iroh` (the n0 crate) — the Endpoint + the NodeAddr
  (the node id + the relay) + the accept/connect. The node's ID =
  the Ed25519 pubkey (iroh's addressing) — the CONFIG: the node id via
  the secretspec (the existing pattern).
- the TEST: two in-process endpoints (the loopback) exchange bytes.

**2b. the wRPC server** (serve the guestlang-host's component):
- `wrpc` + `wrpc-transport` + the iroh integration (`wrpc-transport-iroh`
  exists upstream? — if not, the wRPC's Invocation over the wire trait).
- the server: bind the host's loaded component's exports to the wRPC
  surface (the WIT world = the protocol — the component's WIT = the
  schema's!).
- VERIFY: the loopback client calls `double(21)` → 42 REMOTELY (the
  component runs locally; the CALL travels the wire).

**2c. the remote proxy (the transparency)**:
- `RemoteComponentRuntime` — the SAME trait shape as
  ComponentRuntime (call/instantiate) but the calls = wRPC
  invocations. The generic caller (forge/splice/tests) can't tell.
- the STREAMS: the delta contracts (`stream<change>`) = the wRPC's
  streams — the changes FLOW (the batching = the DBSP delta batches —
  the group structure keeps them order-free: the batch_order_irrelevant
  theorem = the wire's reordering license!).

**2d. the authentication/rate-limiting**: the splicer middleware (the
interposed components) — the transport's node-id allowlist first (the
iroh's pubkey = the identity); the middlewares later.

**Risks**: wRPC's API churn (the BA's crate — the pre-1.0); the iroh
relay's infrastructure (the self-hosted relay for the production; the
direct-connections-only mode for the LAN). The generic seam keeps both
swappable.

---

## Track 3 — OCI push/pull

### What exists

forge's `oci.rs`: the LOCAL OCI image-layout store (target/oci/), the
xxh3-128 digests (the local cache speed), the label annotations, the
verify. NO registry protocol, NO sha256.

### The gaps (in order)

**3a. sha256 digests** (the registries REQUIRE sha256):
- oci.rs: the DUAL digest — the xxh3 for the local cache index, the
  sha256 for the registry-facing manifests. The blob store keys =
  BOTH (the xxh3 for the lookup, the sha256 computed at the push).
- the verify: the sha256 for the push-bound artifacts.

**3b. the OCI manifest for a WASM component**:
- the WASM image spec: the component blob = a layer with the media
  type `application/wasm` (the component = a WASM module for the OCI's
  purposes); the manifest = the OCI image manifest {config (a small
  JSON: the architecture "wasm", the os "wasi"), the layers [the
  component blob]}.
- forge: `forge pack <label>` → the manifest + the config from the
  store's artifacts.

**3c. the registry client** (push/pull):
- the OCI distribution protocol = plain HTTP: 
  - the push: POST /v2/<name>/blobs/uploads/ → the PUT the blob (the
    sha256 digest in the query) → the PUT the manifest (the tag).
  - the pull: GET the manifest (the Accept: the OCI types) → GET the
    blobs → verify the digests.
- the CLIENT crate: `oci-wasm` (the Bytecode Alliance's — the
  wasmtime-compatible OCI client) — OR hand-rolled (the protocol =
  small; reqwest + the digest math). DECISION: use oci-wasm; hand-roll
  only if the dep drags.
- forge: `forge push <label> <registry>/<repo>:<tag>` + `forge pull`.
- the AUTH: the registry tokens via the secretspec (the existing
  pattern); ghcr.io = the first target.

**3d. the provenance annotations**:
- the manifest's annotations: the kernel hash (the toolchain's rev),
  the schema version (the Demo.lean's hash), the AXIOM-GATE REPORT
  (the axiom-clean badge = a fact about the artifact!). The puller can
  VERIFY the provenance before instantiating.

**3e. the content-addressed caching**: the shared layers = the stored
once (the registries do this natively); forge's pull = the dedup into
the local store.

### The verification (the same discipline)

- the round-trip: the pack → the push (to a LOCAL registry —
  `docker run registry:2` or a tiny in-test registry) → the pull →
  byte-identical (the sha256 chain) → the component RUNS (the
  instantiate + the double(21) = 42).
- the byte-tie: the pushed manifest's digest = the pull's digest.

---

## The ordering (the dependency-true critical path)

```
1a cabi_post (30 min) ──────────────────────┐
1b async-lift watch-orders (the big one) ───┤ the compiler line CLOSES
1c stream<T> (the delta wire shape) ────────┘
        ↓
3a sha256 → 3b the manifest → 3c the push/pull → 3d/3e  (the
   distribution — INDEPENDENT of 1b/1c; parallelizable)
        ↓
2a wire/Transport + iroh → 2b the wRPC server → 2c the proxy → 2d
   (the mesh — uses 1c's stream shape for the delta contracts)
```

The true prerequisite for 2c's REMOTE streams = 1c (the stream<T> ABI);
the scalar/record RPC = 2b-only. 3 = independent — start it whenever a
compiler-line step blocks.

## The doctrine ties

- ONE WRITER: the generated worlds/wits stay emitted; the wire crate =
  hand-written infra (not an emitter).
- The gates: the splice-smoke pattern extends — the REMOTE call = the
  splice's cousin (the wire = another interposer); the round-trip
  gates (the pack→push→pull→run) = the byte-tie family.
- The theorems already PAY: batch_order_irrelevant = the wire's
  reordering license; two_replica_converge = the replica sync's
  correctness; the session types (the choreography + duality) = the
  protocol's spec layer for 2b/2c.

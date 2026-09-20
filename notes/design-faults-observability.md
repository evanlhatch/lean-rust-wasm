# Design — the fault plane: ONE observability system, specified in Lean, executed by the runtime

Status: design, the W10 lane's contract. Executor's prerequisite reading:
this file + `notes/canon.md` (name your row) + `notes/design-guest-verified.md`
(the fifth-tier pattern this lane instantiates at the error surface).
Every symbol cited below was grepped against the tree at the paths given;
a citation that no longer resolves is a finding, not a license to
improvise.

## 0. The claim and the canon rows

The owner's goal: the error/observability system becomes ONE cohesive
thing shifted left into Lean. The Lean layer is the source of truth
(fault specs, categories, policies, codes, span specs); the runtime
(host AND guest) executes what Lean proves. Today the system is one
thing only by discipline; this doc makes it one thing by construction
and by proof.

Canon rows this lane names (Part 2/3/4 of `notes/canon.md`):

| This lane's piece | The row it IS | Notes |
|---|---|---|
| a fault / error | = a `Fault` variant: typed at the wire (`result<T, fault>`), E-coded, shared elab↔runtime | Part 3, the W6.5 row — this lane COMPLETES it |
| retry / circuit breaker | = a small machine + a fault policy row (the faults registry) | Part 2 — this lane makes the policy row REAL (W10.4) |
| observability spans | = schema items; trace analysis = a query over the span stream | Part 3, "exists + W2.7" — this lane finishes the SpanSpec lane (W10.2/W10.5) |
| the E-code table's collision-freedom | = a `CodedRegistry` proof field riding the emitters | Part 4 registry/byte-tie rows; LANDED (`Faults.Emit.codesNodupLaw`) |
| a cross-boundary fault | = a `result` err value + ONE remote frame in the consumer's causal tree | NEW row proposed (§3.3); grows in `notes/canon.md`, never in a code comment |

## 1. Baseline — what exists (all verified in-tree)

### 1.1 fast-observe (the execution engine — /home/evan/fast-observe)

- **The registry** (`src/errors.rs`): `ErrorRegistryEntry`
  (code/name/category/display/advice/action/module); native = the
  `ERROR_REGISTRY` linkme distributed slice; wasm = a statically EMPTY
  slice + `register_statics(entries)` populating a runtime
  `STATIC_REGISTRY` that `error_registry()`/`lookup_error` chain after
  the (empty) linkme slice. Duplicate codes: first match wins; the docs
  mandate a workspace uniqueness test. `doctor(code)` renders
  key: value lines with a prefix-search fallback.
- **The causal tree** (`src/exn.rs`): `Fault<E>` wraps a root
  `Arc<Frame>` + the typed `E`. `Frame` = error/location/context/
  children-with-`FrameKind`-edges/type_name/attachments. `FrameKind` =
  `Source | Wrap | Attempt | Batch` (a CLOSED enum). Construction is
  single-path (`Frame::capture`): scope context from
  `current_scope_name()`, source-chain walk, capture hooks run BEFORE
  sharing, one hook firing per constructed fault. `BuiltinKey` pins the
  built-in attachment keys (`scope_path`, `scope_elapsed_ms`,
  `trace_id`, `span_trail`, `backtrace`). `FaultCollection` +
  `into_fault` merge failures; `retry_with_policy`/`retry_with_backoff`
  run `f` while the fault's policy is `Retry`, merge exhausted attempts
  as `FrameKind::Attempt` children, `Backoff` (None/Fixed/Exponential)
  is a PURE schedule iterator (policy/mechanism split; sleep is always
  caller-injected — wasm-safe by construction).
- **The policy axis** (`src/lib.rs`): `ErrorCategory` = Content/
  Invariant/Transient/Fatal (`#[non_exhaustive]`), `policy()` →
  `Policy` = FixInput/Retry/Poison/Abort, `Policy::advice_line` renders
  the report's `action:` sentence. `Fault::policy()` resolves via
  `Error::provide` (nightly `error_generic_member_access`) with a
  registry fallback; `Fault::exit_code` maps categories to sysexits.
- **The report** (`src/report.rs`): `report: fast-observe/1` format
  marker, one fact per line, `Line`-escaped values (data cannot forge a
  line), typed cause lines with FrameKind labels, `fingerprint`,
  `advice`/`action`/`hint`, appendix capped at 32 lines; serde feature
  gives `render_report_json` at `"schema": 2`.
- **Spans** (`src/profiling.rs`, `profiling/instant.rs`):
  `scope!`/`enter(name, tag)` guards; `breakdown.rs` accumulates
  per-phase timings; `deploy.rs`' `observe()` builder returns an
  `InitGuard` (flush on drop), `panic_hook(true)` routes panics through
  the same fault pipeline.
- **The macro** (`fast-observe-macros/src/error_macro.rs`): `error!`
  emits the enum + per-variant structs + Display/Error/source wiring +
  the `ENTRIES: &[ErrorRegistryEntry]` const per enum (the wasm
  composition path).
- **Platform gates**: nightly-only (`error_generic_member_access`,
  `error_iter`, and `backtrace_frames` behind the `backtrace` feature —
  `src/lib.rs` header). wasm deps are target-gated (web-time clock;
  wasm-bindgen only on `wasm32-unknown-unknown`). README caveat:
  hook panic containment uses `catch_unwind` — under wasm's default
  `panic = "abort"` it cannot contain; don't panic in hooks.

### 1.2 The Lean faults lane (lean/faults)

- `Faults.Category`: `Category` = fatal/content/transient/invariant/
  unsupported; `retryable` (transient only); `rustName` renders the
  fast-observe attribute. `.unsupported` is taxonomic-only —
  UNEMITTABLE (fast-observe has no Unsupported category, no degrade
  policy), rejected at registration.
- `Faults.Registry`: `FailureModeItem` (name/display/category/advice/
  `payload : List (String × Ty)` — schema-lang's `Ty` is the type
  authority, no second universe); `@[fault]`/`@[host_fault]` attribute
  registrations into `guestFaultExt`/`hostFaultExt`
  (`applicationTime := .afterCompilation`, compiled-value evaluation,
  duplicate-name elaboration error); `derive_fault_registry name
  [host]` snapshots the extension into a `CodegenCore.CodedRegistry
  FailureModeItem`; codes derive from position via
  `CodegenCore.allocateCodes` (guest starts E100; host starts
  `100 + guest count` — derived, never hand-set). Name uniqueness and
  code collision-freedom are IN THE TYPE (`CodedRegistry.codes_nodup`,
  `codes_length`); a bad registry literal fails to ELABORATE.
- `Faults.Emit.Rust`: `faultModule` folds a registry into ONE
  `fast_observe::error!` block + the init hook — `init_guest()` (the
  wasm contract: `fast_observe::register_statics(<Enum>::ENTRIES)`) or
  `init_host()`. Payload fields render via `SchemaLang.Emit.Rust.tyRust`.
- `Faults.Emit.Registry`: `guestEmitter` → `src/faults_generated.rs`,
  `hostEmitter` → `src/host_faults_generated.rs`, the `forgeJobs`
  manifest with the PROVED coverage (`jobsCoverEmitters_true := rfl`),
  and `codesNodupLaw` discharged by `codesNodupLaw_discharged` — the
  W7.9 `Emitter.law` pattern, landed on both fault emitters. The
  SchemaDiag lane joins the SAME E-code space (`schemaDiagCodes`,
  derived start after both registries).
- `Faults/Spec/Demo.lean` / `Spec/Host.lean`: the seed specs — four
  `@[fault]` items (E100–E103), four `@[host_fault]` items (E104+),
  `derive_schema_type_names knownTypes` (the payload universe, derived).
- `FaultsTests/Main.lean`: elaboration-time negative controls (duplicate
  fault, colliding allocation scheme, rogue emitter output, stale
  knownTypes, sabotaged diag-code lookup) — the TestKit discipline.

### 1.3 The consumption (crates/guestlang-host, src/)

- `src/faults_generated.rs` (committed, byte-tied): the guest
  `OrderError` fast-observe enum E100–E103 + `init_guest()`.
  `src/host_faults_generated.rs`: `HostFault` E104+ + `init_host()`.
- `crates/guestlang-host/src/valves.rs`: `#[path]`-includes the generated
  host module (the hand-written enum was deleted, Stage C complete);
  `register()` calls `init_host()`.
- `crates/guestlang-host/src/runtime.rs`: `HostResult<T> =
  Result<T, fast_observe::exn::Fault<HostFault>>`; THE OBSERVABILITY
  SEAM — `call` looks up the export in
  `observability_generated::SPANS` and enters
  `fast_observe::profiling::instant::enter(spec.name, Some(spec.delivery))`
  ONLY for a registered export (the host cannot invent a span); wasmtime
  errors become `HostFault::Engine` faults; fuel (10M default) + epoch
  interruption bound execution.
- `lean/wasm-backend/WasmGenMain.lean`: `WorldExport := String ×
  SchemaLang.FuncSig`; `worldExportsOf` folds the registered
  `@[schema_fn]` bodies ∩ compiled targets; `observabilityRsOf` emits
  `SpanSpec { name, delivery, fields }` from the SAME fold as the WIT
  world (one writer); the `observabilityEmitter` writes
  `src/observability_generated.rs` (17 rows committed). The wasm
  emitters ride the `wasm-compile` recipe's own byte-tie (the header
  comment records the forge-jobs follow-up).
- `crates/guestlang-host/tests/load_component.rs` (registry round-trip:
  `init_guest()` then `lookup_error("E100")`/`E107`) and
  `tests/fault_injection.rs` (the Rust-side negative-control suite:
  corrupt/truncated artifacts fail structured, never panic-poison).

### 1.4 The audit baseline (what W10 sequences PAST)

`notes/w9-6-guest-checker-audit.md` recorded the guest-compile gap list;
the unblocking work landed/lands as follows (each status verified
in-tree at design time):

| Audit item | Status |
|---|---|
| Nat unlowerable (fuel model) | LANDED — the boxed-Nat lowering (`WasmBackend.lean` ~line 479: `{rc, tag, i64 payload @8}`, cap 2^62, `Nat.lit/decEq/beq/sub/add/decLt/decLe` + the `UInt64↔Nat` seam inline-lowered) |
| Perceus reset/reuse/isShared unlowered | NEUTRALIZED — `compiler.reuse := false` pinned in `WasmGenMain.lean` (both compile passes); the `unsupported` arm stays as the guard |
| `String.decEq` unlowered | LANDED — `GuestlangStd.StrOps.Intrinsic.streq` (+ `runtime.wat` primitive + oracle body); `String.decEq`/`instBEqString.beq` map to it |
| Spec-products excluded from the compile set | LANDED — GenMain includes every local impure decl (the closure fixpoint, the namespace filter deleted) |
| Guest wire-decode lane host-only | LANDING — the decode-lane lowerings are in the emitter (the byte/char/u64 atoms, the boxed-byte rebox, the bytes-param adapter behind `verify-witness`) |
| `verifyWitness` unexportable (not `Ty`-representable) | RESOLVED for v1 — the wrapper export shape (`verify-witness: func(bs: list<u8>) -> bool`) is in the committed world |

The guest compilation surface therefore EXISTS. W10 builds the fault
plane on it.

## 2. The one system — the full path, `@[fault]` to report

### 2.1 The path today (what is already ONE thing)

```
@[fault] FailureModeItem ── guestFaultExt / hostFaultExt
        │  (derive_fault_registry: CodedRegistry, codes_nodup in the type)
        ▼
Faults.Emit.Registry (guestEmitter / hostEmitter, Emitter.law = codesNodupLaw)
        ▼
src/faults_generated.rs / src/host_faults_generated.rs   (byte-tied)
   = one fast_observe::error! block + init_guest()/init_host()
        ▼
guestlang-host: Fault<HostFault>, lookup_error, doctor, render_report
```

What is NOT yet one thing: (a) the wire — a guest fault cannot CROSS as
a fault (the WIT world has no error channel; `order-error` today rides
as an ordinary variant PARAMETER of `watch-orders`); (b) the tree — a
guest fault has no host `Frame`; (c) the policy — `Category.retryable`
is a Bool, fast-observe's `Policy::Retry` machine is hand-wired per
call site; (d) the span law — `SPANS ≡ world exports` is by-construction
but not a stated law, and the guest adapter shapes are a hand list
(`WasmBackend.adapterShape?`); (e) registration completeness —
`init_guest()`/`init_host()` call presence is test folklore, not an
obligation. §3–§5 close these.

### 2.2 The wire: the WIT error channel (the honest mechanism)

The canon row says `result<T, fault>`. The schema lane's own design
intent agrees — `SchemaLang.Item.FuncSig`'s doc: "Errors are `.result`
constructors — no special error channel." `SchemaLang.Ty` has
`.result (ok err : Ty)` (closed-universe ctor, `Value.ok/err`,
`toType` → `Sum`); `SchemaLang.Emit.Wit.tyWit` renders
`result<ok, err>`; `SchemaLang.Emit.Rust.tyRust` renders
`Result<O, E>`; the backend's `flatTyOf` flattens `.result`. The
mechanism is therefore: **a failing export's `FuncSig.ret` is
`.result ok errTy` where `errTy` is the registry-folded fault variant**
— no special WIT channel, no stringly `result<_, string>`, no
out-of-band side channel. wit-bindgen lifts it to
`std::result::Result<T, OrderError>` on the host; the canonical ABI
carries it as the standard result discriminant.

**The one-fault-unification decision (W10.1).** Today TWO OrderError
concepts exist: the schema variant (`Demo.lean`'s `@[schema] inductive
OrderError` — emptyCart/invalidItem/insufficientFunds — the wire type)
and the fault registry (`Spec/Demo.lean`'s `notFound`/`invalidItem`/…
— the E-code source, rendered into the fast-observe enum also named
`OrderError`). This is the last hand-paired seam in the lane and a
drift risk by inspection. Prescription: **the fault registry IS the
wire variant's SSOT** — the faults package gains an emitter that folds
the guest registry's items into a schema `Item.variant`
(name/kebab-cased cases/payload `Ty`s — one-to-one with
`FailureModeItem`), registered into the same universe the WIT world
folds from. A fault is declared ONCE; the wire type, the fast-observe
enum, the codes, and the doctor entries are all projections of the one
row. The existing schema variant (or the registry) is deleted — which
one survives is mechanical: the registry, because it carries
category/advice/code and the variant cannot.

**Codes on the wire: NONE.** The err value crosses as the variant case
+ payload; the host derives the E-code host-side by looking up the
case's registry row (`lookup_error`'s first-match rule + the
registry's name mapping). Carrying the code string too would create a
second copy of the allocation to skew; the surface fingerprint (the
`instantiate_checked`/`verify_surface` skew gate + the byte-tie on the
world) pins the case↔code mapping instead.

### 2.3 The crossing: guest fault → host causal tree

The guest (Lean-compiled wasm) has NO fault machinery — deliberately:
the guest lane has no IO, no hooks, no allocator beyond runtime.wat's.
The guest's fault is the typed err VALUE. The host lifts it
(wit-bindgen) and MAPS it into the causal tree:

1. The host call site (or `ComponentRuntime::call`'s typed wrapper)
   receives `Err(OrderError)`.
2. The host constructs its own typed fault
   (`HostFault::GuestFault { export, code }` — a new registry row,
   `@[host_fault]`, so the mapping ITSELF is registry data) and the
   guest's lifted error becomes a CHILD `Frame` under the root, edge
   kind `Remote` (see the new canon row, §0).
3. The guest frame's fields, honestly: `error` = the registry's
   display render (the payload interpolated — the same format string
   Lean emitted into `#[error(...)]`), `type_name` =
   `<package>::order-error::<case>` (greppable to the registry),
   `location` = the export name (`guest:watch-orders` — the guest has
   no `Location<'static>`; a synthesized constant is the honest
   substitute), `context` = `Context::Scope(export)`. Attachments ride
   `BuiltinKey`-style keys for the payload fields (typed, downcastable,
   `Placement::Inline`).
4. The report renders BOTH sides' frames — the host's cause chain
   (fuel exhaustion, capability denial) above, the guest's fault as a
   typed cause below:

```
report: fast-observe/1
error: [E108] [guestlang_host::HostFault] guest fault in watch-orders
category: Transient (policy: safe to retry with backoff; ...)
location: crates/guestlang-host/src/runtime.rs:133
cause 0: [E101] [guestlang:demo/order-error invalid-item] invalid cart item: 7, at guest:watch-orders
trace_id: 4f3c…
```

   The E-code in the guest frame's line resolves through the SAME
   `lookup_error` registry (the guest codes are registered at the
   composition root via `init_guest()` — already the pattern in
   `load_component.rs`). `render_report_json`'s schema-2 causes carry
   the same structure; NO schema bump needed (type/location/kind are
   existing fields).

**Depth is ONE frame per crossing** (the expressiveness limit, stated
in §8): a WIT result err is a flat variant value — the guest's fault
carries its case + payload, not a tree. Nested guest causality would
need a wire-encoded frame list; §7's flip condition covers it.

### 2.4 The span/profile story (the SpanSpec lane's completion)

Landed: the spans are spec data — `observabilityRsOf` folds the same
`worldExportsOf` as the WIT world (one writer); the host's `call` path
spans exactly the registered surface; delivery (`once`/`stream`) rides
the `FuncSem` delivery axis. Completion items:

- **The adapter hand list** (`WasmBackend.adapterShape?` — per-export
  result shapes as a String-keyed `Option` table) is the lane's last
  hand mirror. W10.2 folds it from the `FuncSig` (the shape is a
  function of the ret type: option-user, list-user, stream-u64,
  result-ok-err, …), keeping the two existing consumers (the
  result-side adapter selection + the WASI task-return flat results)
  on the fold.
- **The span coverage law**: `SPANS ≡ world exports` — today true by
  shared fold, stated as the emitter's `Emitter.law` (the
  `codesNodupLaw` pattern: a pure function over the spec, discharged by
  the registry fold's construction). A second span table instance
  anywhere else is a review finding.
- **The fault-span junction**: a constructed fault already emits an
  error span event and captures `scope_path`/`trace_id`
  (`Frame::capture` + the capture hooks). The host's guest-fault
  construction (§2.3) happens INSIDE the export's span guard, so a
  guest fault lands in the trace timeline under the right span with
  the right trace id — no new machinery, the existing junction.
- **The guest has no profiler** — DELIBERATE: the span is the host's
  call path; the guest's internal structure is the export boundary's
  span + the guest's own fuel/epoch budgeting (host-side). A guest-side
  span lane would need a clock + a sink in the sandbox; recorded as a
  shelf item, no flip condition yet.

### 2.5 The policy story (canon Part 2, made real)

`Category.retryable : Category → Bool` is the policy axis today — one
bit. fast-observe's `Policy::Retry` + `retry_with_backoff` is the
mechanism, hand-wired at call sites. The canon row says a retry /
circuit breaker IS a small machine + a fault policy row. Prescription:

- **The policy row**: `FailureModeItem` gains an optional policy field
  (additive, defaulted — the W7.1 discipline): `policy :
  Option PolicySpec` where `PolicySpec` carries maxAttempts and the
  backoff shape (none/fixed/exponential base-factor-max —
  fast-observe's `Backoff`'s exact ctor set, so the generated config
  is total). Registry-level default: `transient` ⇒ retry row present,
  `content`/`invariant`/`fatal` ⇒ `none` — a fault whose category and
  policy disagree (a `content` with a retry row) fails ELABORATION
  (the category/policy coherence gate, the same registration-time
  rejection style as the `.unsupported` gate).
- **The circuit breaker**: for faults whose policy needs state (open/
  half-open/closed over a failure count), the row is a MACHINE —
  `Machines.Machine` with the state/label/guard/action shape, carrying
  the `Convergent` certificate (`Machines.Convergent`: `terminates`,
  `run_length_bound` — the no-infinite-execution theorem) at whatever
  tier computes. The machine's `Inv` is the circuit's legality
  (an open circuit rejects before the call, a half-open allows one
  probe); `tr_iff_step?` gives the two-projection agreement for free.
- **What Lean PROVES vs what the runtime checks** — §3.

## 3. Shifted left — the proof/check/oracle table per piece

The doctrine's ladder (`notes/lean-doctrine.md`, the Obligation row:
every checkable fact is an `Obligation`, the enforcement tier is a
BACKEND ASSIGNMENT). Each row names its tier honestly:

| Piece | Lean PROVES | Runtime CHECKS | Oracle-swept |
|---|---|---|---|
| Code-space coherence | LANDED — `CodedRegistry.codes_nodup`/`codes_length` in the type; `codesNodupLaw_discharged` rides both emitters; one E-code space incl. SchemaDiag (`schemaDiagCodes`, derived start) | — | the byte-tie pins the committed tables; `FaultsTests` allocation controls |
| Category validity | LANDED — the elaboration gate: `registerFaultItem` rejects `.unsupported` + duplicate names at registration; the category/policy coherence gate lands with W10.4 | — | — |
| Policy soundness | W10.4 — the policy machine's termination (`Convergent.terminates`), the retry row's exhaustiveness (maxAttempts is a natural, the schedule iterator is total), the coherence gate. Tier: `provedAtElab`/`decidableNow` for the coherence + totality; the machine's `Inv` preservation is the machine row's PO slot | fast-observe's `retry_with_backoff` executes the schedule (its exhaustion/merge semantics are its own tested contract) | the duel: a retry row against a flaky fixture — attempts merged as `FrameKind::Attempt` children, count == maxAttempts; negative control: a non-transient fault is NEVER retried |
| Span coverage | W10.5 — the `Emitter.law`: SPANS ≡ world exports (one fold, stated); `worldRetOf`'s delivery render is total over `FuncSem` | the host's `call` span lookup (the host cannot invent a span) | `wasm-compile`'s observability byte-tie (committed vs regenerated) |
| Wire-channel coherence | W10.2 — the emitter law: every export whose impl returns `Sum` (`.result`) names a REGISTERED fault variant as its err type — proved over the registry fold at elaboration | the canonical-ABI lift (wit-bindgen's type-directed Result lift) | the duel's err-path rows: a guest fault → typed host `Err` → rendered report |
| Guest registration completeness | W10.5 — the obligation: every guest fault crossing the world resolves via `lookup_error` after `init_guest()`. Tier: `generatedCheck` (the check is GENERATED — the init fn exists only in the emitted module; the completeness test links both registries, the `load_component.rs` pattern promoted to an obligation row) | the composition root's init call | the planted-missing-init negative control (a workspace crate that skips `init_guest` fails the test) |
| Guest-side verdicts (if W10.6 flips) | the guestVerified tier's machinery (`WitnessCheck`'s lane, `design-guest-verified.md`) | the compiled checker under wasmtime/wasmi | the oracle duel rows (guest verdict ≡ interpreted verdict, sabotage controls) |

The tier discipline from the fifth-tier design applies verbatim: a
piece that cannot compute its tier gets NO tier — the gap is LOUD
(`discharge = none`), never silently downgraded to `oracleSwept`.

## 4. The guest-side execution question — can the POLICY run in the guest?

The honest answer, decided on the backend's ACTUAL surface:

**The policy DECISION can run in the guest; the policy MECHANISM
cannot — and v1 runs both host-side anyway.**

Evidence:

- **For (the decision is expressible)**: a policy machine's step
  function is a decidable finite table — `Machine.step?` is total,
  guard + action over a `State`. The guest-compiled surface handles
  exactly this: fixed-width scalars, enum ctor dispatch, the
  bounded-Nat lane (countdown = `Nat.sub` on the boxed machine int —
  the fuel pattern ALREADY lowered for `checkWitness`),
  `Intrinsic.streq` for name comparisons. A circuit breaker's state
  (an enum: closed/open/half-open) + a u64 failure counter + a
  u64-tick deadline is in the sanctioned closure with NOTHING new. The
  Machines→typestate path (`SchemaLang.Emit.Typestate`, the
  entity-machine preset emitting host-compiled Rust from the SAME
  proved table) is the host-side shape; the Machines→wasm path is the
  SAME step function through OUR backend instead of through
  typestate — the two projections' agreement (`tr_iff_step?`) is
  backend-independent.
- **Against (the mechanism is host-only, by construction)**: sleeping
  (`Backoff`'s delays), the wall clock (half-open deadlines), and
  process abort are IO/time — the guest ban (`LintKit.GuestBan`)
  excludes them and the sandbox has no clock to read (the host owns
  fuel + epoch). fast-observe's own design agrees: `sleep` is always
  caller-injected, never called on wasm by the crate.
- **The v1 decision**: the policy EXECUTES host-side — the Lean policy
  row generates the retry configuration
  (`retry_with_policy`/`retry_with_backoff` arguments) and, for
  stateful policies, the typestate projection (the
  `order_typestate_generated.rs` precedent: host-compiled,
  illegal-transitions-unrepresentable). The guest emits faults (the
  err variants); the host decides and retries. This keeps ONE
  execution of the policy (the host's), which the report and the
  trace then observe coherently.
- **The flip (W10.6)**: when a consumer needs the DECISION in-guest
  (a guest retrying an internal op under a declared policy — the
  outbox/inbox row's "journal + cursor + retry machine" composition),
  the policy machine's step function is guest-marked and compiled via
  our backend. Constraints, stated loudly: the machine state must be
  guest-surface types (enum + u64 counters — NOT Nat-scrutinee case
  dispatch, which the backend rejects by design); the verdict that
  crosses is a command value (the W8.6 effect row: commands as data
  out), the host executes the mechanism. The oracle duel rows pin
  guest verdict ≡ host execution of the same table.

## 5. The end state

A user declares, in Lean, ONE row per failure mode:

```
@[fault] def upstreamTimeout : FailureModeItem :=
  { name := "upstreamTimeout", display := "upstream timed out after {ms}ms"
  , category := .transient, advice := "retry with exponential backoff"
  , payload := [("ms", .u64)]
  , policy := some { maxAttempts := 5, backoff := .exponential … } }
```

Everything else is generated + proved: the E-code (allocated,
collision-freedom in the type), the fast-observe enum + `init_guest`/
`init_host` (byte-tied), the wire variant + the `result<T, err>`
signatures in the world (byte-tied), the adapter shapes + the SPANS
manifest (one fold, law-stated), the retry config / policy typestate
(convergence-proved), the registry-completeness obligation, the duel
rows incl. err paths, the report goldens, the negative controls (a
sabotaged code allocation, a skipped init, a non-retryable retry, a
corrupt wire fault — each must FAIL). The guest's registration, the
host's causal tree, the trace, and the report all render the same
E-codes from the same Lean rows.

**The only hand-written code left**, named honestly:

1. fast-observe itself — the execution engine (the fault pipeline,
   the report renderer, the profilers). It is an external crate at
   0.1; we own it, but it is ENGINE, not spec — it stays hand-written
   and nightly-gated.
2. The guestlang function BODIES that return the faults — the business
   logic (`@[schema_fn]` impls); Lean-proved where the lane proves
   them, but authored.
3. The host's business call sites — the `?`-wiring that turns a
   lifted guest `Err` into the host fault (the mapping fn is
   generated; the CALL is the app).
4. The policy machine's AUTHORING (state/guard/action per circuit) —
   the preset + proofs are the framework's; the instance is the app's.

## 6. Work orders — W10.x (dependency order, per-order gates)

Dispatch per the runbook protocol; each order is atomic, gates green
(`just gates`) before done-when is claimed. W10 sequences PAST the
w9-6 audit's items (§1.4 — landed/landing; a red `just wasm-compile`
blocks W10.2's first build, by design).

### W10.1 The one-fault unification: the registry folds the wire variant `[std]`
The faults package gains the variant-projection emitter: the guest
registry's items fold into a registered schema `Item.variant` (kebab
cases, payload `Ty`s), the WIT world's err types consume it; the
duplicated `Demo.lean` `OrderError` (or the registry's render of it —
whichever the fold makes redundant) is deleted; `bindings.rs`'s
`GatewayOrderError` re-pins to the folded type. Additive first (both
surfaces green), dedup second (one concept).
Verify: BUILD; `just gen-check` (byte-tie re-pin, deliberate diff);
`wit-check`; `FaultsTests` + `SchemaLangTests` green; the
unification's negative control — a fault row and a schema variant
disagreeing on a case payload fails elaboration.
Done-when: one fault concept per failure mode; the world's err types
are registry-folded; `just breaking` clean (the variant is unchanged
byte-wise or remedied).

### W10.2 The WIT error channel + the adapter fold `[std]`
Depends: W10.1. A `@[schema_fn]` whose ret is `.result ok errTy` (errTy
= the folded fault variant) lowers end-to-end: the world renders
`result<ok, order-error>`; the backend's return-path adapter gains the
result shape (folded from the ret type — `adapterShape?`'s hand rows
are replaced by the fold, per-shape lowerings stay as the closed
function's arms); `flatTyOf`'s `.result` arm is exercised (the
flat-form test pins it); the duel manifest grows err-path rows (the
impl returns `Value.err`, the host lifts `Result::Err`).
Verify: BUILD wasm-backend; `just wasm-compile` (validate + the
observability byte-tie); the duel err rows green under wasmtime + the
scalar subset under wasmi; `wit-check`.
Done-when: a guest fault crosses as a typed `Result::Err` — the first
`result<T, fault>` in the committed world.

### W10.3 The host causal-tree mapping + the report `[senior]`
Depends: W10.2. The new `@[host_fault]` row (`guestFault { export,
code }`-shape — registry data, so the mapping is spec); fast-observe
gains `FrameKind::Remote` (upstream, we own the crate — see §8 risk
R5; the 0.x minor bump) OR the v1 fallback reuses `FrameKind::Wrap`
behind a feature flag, stated in the order's jj description BEFORE
merge (the `[senior]` protocol). The mapping fn (lifted guest err →
child `Frame`, §2.3's field table) is GENERATED into
`host_faults_generated.rs`'s module family (one writer). Report goldens
(text + schema-2 JSON) pin the both-sides render; the fault-injection
suite grows the corrupt-err-value classes (a wrong-case discriminant
on the wire = a lift failure or a registry miss — structured, never a
panic).
Verify: BUILD; the report golden tests; `cargo nextest` fault-injection
extension; `just gates`.
Done-when: a guest fault's report renders host frames above the guest
frame, E-codes resolved via `lookup_error` from BOTH registries; a
corrupt wire fault is a structured `Err`.

### W10.4 The policy rows: the fault policy machine `[senior]`
Depends: W10.1 (registry shape). `PolicySpec` (maxAttempts + the
backoff shape mirroring `Backoff`'s ctors) joins `FailureModeItem`
(additive, defaulted); the category/policy coherence gate at
registration (transient ⇒ retryable row; a content/invariant/fault
with a retry row is a named elaboration error); stateful policies are
`Machines.Machine` instances with the `Convergent` certificate —
`terminates`/`run_length_bound` cited at the registration (the
`checkCitation?` gate resolves them; a policy machine without a
convergence story does not elaborate). The generated retry config
(byte-tied artifact, the `host_faults_generated.rs` family) feeds
guestlang-host's `retry_with_policy`/`retry_with_backoff` call sites —
the schedule is Lean's row, the mechanism is fast-observe's.
Verify: BUILD; axiom gate (the convergence citations are kernel-checked
or the build is red); the config artifact's byte-tie; the duel/fixture
rows: a transient fault retries exactly maxAttempts (attempts merged as
`FrameKind::Attempt` children), a content fault NEVER retries
(negative control), a policy machine that could loop fails elaboration
(control: plant a non-decreasing variant).
Done-when: retry behavior is spec data; the canon's retry row consumes
this doc as its realization.

### W10.5 The coverage laws + the registration obligation `[std]`
Depends: W10.2. Two obligation rows land: (a) the span-coverage law as
the observability emitter's `Emitter.law` (SPANS ≡ world exports —
stated over the shared fold, discharged by construction; the
`codesNodupLaw` template); (b) the registration-completeness
obligation: every E-code in the byte-tied fault artifacts resolves via
`lookup_error` after the init calls — the check is GENERATED
(tier `generatedCheck`), the workspace test links both registries
(the `load_component.rs` pattern promoted), the planted-missing-init
negative control fails it.
Verify: BUILD; `just gen-check`; `just gates` (the new test rows in the
gates composition); the negative controls red-when-sabotaged.
Done-when: a second span table or a skipped `init_guest` is a CI
failure, not a review catch.

### W10.6 The guest-side policy flip (conditional) `[senior]`
Depends: W10.4, and a NAMED consumer (the anti-museum rule: no
consumer, no flip). The policy machine's step function guest-marked
(`@[guest_std]`), compiled via the wasm backend (the W9.6 lane's
surface); the verdict crosses as a command value (the W8.6 effect row);
the host executes the mechanism; the oracle duel pins guest verdict ≡
host execution. Constraints restated in the module header: enum +
u64 state only; Nat-scrutinee dispatch and any time/IO are banned.
Verify: BUILD wasm-backend; the duel rows; GATES.
Done-when: a policy decision computed in the guest agrees with the
host's execution of the same proved table, under wasmtime AND wasmi.

### W10.7 The template dogfood + the inventory pin `[std]`
Depends: W10.1–W10.5. A `template/` instantiation (the reuse-map
checklist) declares a fault + a policy and consumes the whole chain
end-to-end; `notes/reuse-map.md`'s faults row and this doc's §5
inventory are updated in the same commit; the hand-written residue
(§5's list) is pinned there as the honest remainder.
Verify: `just gates` for the new project; the chain's artifacts all
byte-tied.
Done-when: the second project's fault plane required ONLY the
checklist's step 1–2 authorship.

## 7. Risks — the honest ones

- **R1 — fast-observe 0.x + nightly gates.** The crate requires
  nightly (`error_generic_member_access`, `error_iter`,
  `backtrace_frames`) — every CONSUMER of the fault plane inherits the
  nightly requirement (our workspace already carries
  `#![feature(error_generic_member_access)]` in `src/lib.rs`).
  Upstream stabilization (issue 99301) moves the boundary; until then,
  the risk is pinned toolchains, not correctness. The 0.x version
  range (`fast-observe = "0.1"` in our Cargo.toml) means minor bumps
  can break the generated `error!` block — the byte-tie catches drift,
  the pin (a workspace-path or exact-version dep during W10) catches
  semver drift.
- **R2 — wasm panic=abort.** The README's caveat: hook panic
  containment (`catch_unwind`) cannot contain under wasm's default
  `panic = "abort"`. Our GUESTS never run fast-observe (the fault plane
  is host-side machinery), so the exposure is a hypothetical
  fast-observe-in-guest consumer, not this lane. Stated so nobody
  "fixes" it by shipping fast-observe into the sandbox.
- **R3 — the linkme-wasm hole.** On wasm the registry is populated
  ONLY by `register_statics` calls; a composition root that forgets
  one gets SILENTLY empty lookups (first-match-wins on a partial
  registry, no error). Mitigations are structural (W10.5): the init fn
  is generated, the completeness obligation is a generated test, and
  native builds (the tests) use the link-time slice so a missing
  registration fails the test binary, not production.
- **R4 — causal-tree expressiveness across the ABI.** A WIT result err
  is a flat variant: ONE frame per crossing (§2.3). The guest's
  internal fault structure (if a guestlang fn faults through three
  internal steps) does not survive the wire — the schema variant's
  payload is the only channel. The flip condition: a consumer needing
  guest-side nesting gets a wire-encoded frame list (a `list` payload
  of case+payload pairs — expressible in `Ty` TODAY) + a W10.3-followup
  that expands N frames under the remote edge. Not built v1: no
  consumer, and size-on-wire discipline (the witness lane's §7.2
  precedent) applies.
- **R5 — `FrameKind` is a closed enum upstream.** Adding `Remote`
  breaks every exhaustive match in fast-observe (report labels, tests)
  — small (we own the crate), but it is an upstream-semver event for
  any other consumer of 0.1. The v1 fallback (`Wrap`) is named in
  W10.3 so the order can land either way; the jj description states
  which.
- **R6 — code allocation stability vs registry growth.** Codes derive
  from POSITION; the byte-tie + `FaultsTests`' allocation controls pin
  them, but a mid-list insert reallocates every later code (the
  "codes are forever" rule). The discipline is already landed
  (append-only, the stale-pin negative control); the risk is a new
  contributor not knowing it — the canon row + the emitter header
  carry it.
- **R7 — the policy machine's tier honesty.** A circuit breaker's
  deadline logic is wall-clock at runtime but the MACHINE is tick/u64
  in Lean (the Scheduling row: "never a separate time system"). The
  coherence gate must not let a `PolicySpec` claim proven convergence
  for what is actually an oracle-swept timing property — the tier
  assignment (§3) is per-piece, and a timing-dependent circuit row
  gets `oracleSwept` for the timing half, `proved` for the
  state-machine half. W10.4's elaboration gate encodes the split.

## 8. Decisions the owner must confirm

1. **One fault concept: the registry IS the wire variant's SSOT**
   (W10.1's unification; the duplicated `OrderError` dies).
   Recommendation: YES — the hand-paired seam is the last drift
   surface in the lane, and the registry carries strictly more
   (codes/categories/advice) than the variant can.
2. **The WIT error channel is `result<T, registered-variant>`, codes
   derived host-side, nothing extra on the wire.** Recommendation:
   YES — the mechanism the schema lane already designed for
   (`FuncSig`: "errors are `.result` constructors"), the ABI already
   flattens it, and code-on-the-wire would be a second allocation
   copy to skew.
3. **Guest fault = ONE remote frame per crossing; `FrameKind::Remote`
   lands upstream (we own fast-observe), v1 fallback `Wrap`.**
   Recommendation: YES to `Remote` — the edge kind is the report's
   semantic ("this cause crossed the sandbox boundary"), the closed
   enum exists exactly for this, and the 0.x bump cost is ours to
   pay once.
4. **Policy v1 executes host-side; the guest-side flip is conditional
   on a named consumer (W10.6).** Recommendation: YES — the mechanism
   (sleep/clock/abort) is host-only by the guest ban's construction,
   and one policy execution (the host's) keeps the trace/report
   coherent; compiling the DECISION early buys no consumer value.
5. **Registration completeness + span coverage become generated
   obligations (tier `generatedCheck`), not review discipline.**
   Recommendation: YES — the linkme-wasm hole is silent by
   construction (R3), so the check must be generated, linked, and
   sabotage-controlled; the `Emitter.law` costs one line where the
   pattern already exists (`codesNodupLaw`).

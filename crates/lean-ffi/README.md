# lean-ffi

Safe Lean-FFI layer over [`lean-sys-v433`](../lean-sys-v433) (pinned
**leanprover/lean4 v4.33.0**). Pattern: cedar-lean-ffi's `lean_object.rs`
(evidence: `notes/studies/cedar-study.md` "The interop verdict"). Work
order: `notes/runbook-2026-09-15.md` W6.2.

## Crate layout

| Path | Contents |
|---|---|
| `src/runtime.rs` | `LeanRuntime` — process-global init (`OnceLock` + `LEAN_INIT_MUTEX`): `lean_setup_args` → `lean_initialize_runtime_module` → `initialize_<Module>(builtin=1)` → `lean_io_mark_end_initialization` → `lean_set_exit_on_panic(true)`. `ThreadGuard` — `lean_initialize_thread` on new, `lean_finalize_thread` on Drop (`!Send`). |
| `src/object.rs` | `OwnedLeanObject` (Drop→`lean_dec`, Clone→`lean_inc`), borrowed `LeanObject<'a>` (`PhantomData<&'a lean_object>`), `LeanCtorObject<'a>` tag-checked ctor access, `LeanObjectError` (thiserror: unexpected-tag, index-out-of-bounds, not-string/not-bytearray, utf8). |
| `src/marshal.rs` | `sarray_from_bytes` / `bytes_from_sarray` / `string_from` / `to_string` / `call_export` over the lean-sys sarray + string APIs. |
| `tests/lean/Echo.lean` | Fixture: `reverseBytes : ByteArray → ByteArray`, `mkPair : ByteArray → ByteArray × ByteArray`; compiled by `build.rs` (`lean -c`, mirrors lean-sys-v433's pattern; module-init symbol asserted at build time). |
| `tests/roundtrip.rs` | Smoke/property tests — see below. |

## The ownership contract

1. **`OwnedLeanObject` owns exactly one reference count.** `Clone` does
   `lean_inc`; `Drop` does `lean_dec`. Scalars are handled inside the sys
   `lean_inc`/`lean_dec` (low-bit check, no deref).
2. **`LeanObject<'a>` borrows** — no RC traffic, cannot outlive its owner.
   Field access via `LeanCtorObject::get` returns another borrow (the ctor
   owns its fields).
3. **Lean steals arguments; Rust owns returns.** `call_export` hands the
   argument over with `into_raw` (`mem::forget`, no dec) and wraps the
   return in `OwnedLeanObject`.
4. **Runtime init is once-per-process.** `LeanRuntime::init` is idempotent
   for the same module init fn and rejects a different one
   (`InitError::MismatchedModule`). The init thread is registered as a side
   effect; every other thread touching Lean objects must hold a
   `ThreadGuard` (`thread_guard()` returns `None` on the init thread to
   prevent double registration).
5. **No `Send`/`Sync` on object types.** Single-threaded Lean objects carry
   a non-atomic refcount; cross-thread sharing requires `lean_mark_mt`,
   deliberately not automated here.
6. **Failure domain: loud abort.** `lean_set_exit_on_panic(true)` — a Lean
   panic/OOM kills the host process rather than corrupting state (cedar's
   accepted trade-off).

## What is allowed to cross

- Scalars (unboxed by the Lean ABI itself).
- `ByteArray` ↔ `&[u8]` / `Vec<u8>` (sarray, element size 1, checked).
- `String` ↔ `&str` / `String` (UTF-8 validated on the way out, not assumed).
- **Nothing else.** No structure-field reads off-Lean beyond tag-checked
  ctor access (`LeanCtorObject`, for io_result/Except-shaped checks).
  Payloads ride inside byte arrays in our codec's wire format.

## Build note (paid once, do not re-pay)

`cargo:rustc-link-lib`/`rustc-link-search` propagate from lean-sys-v433's
`links` build script to dependents, but `cargo:rustc-link-arg` does NOT —
so this crate's `build.rs` emits its own `-Wl,-rpath,<toolchain>/lib`.
Without it, test binaries link fine but fail at load:
`libunwind.so.1: cannot open shared object file`.

## Test evidence

`cargo test -p lean-ffi` (build/test env: `devenv shell --profile wasm`):

- `reverse_echo_roundtrip` — `call_export` on empty, 1-byte, ascii, the
  256-byte boundary (every byte value), and a 300-byte case; asserts exact
  reversal.
- `string_round_trip` — UTF-8 both directions.
- `ctor_tag_checks` — field reads off a tag-0 pair ctor, plus negative
  controls: index-out-of-bounds, wrong-tag, string-as-ctor, and marshaling
  kind mismatches.
- `refcount_churn` — 10k create/clone/drop cycles. Best-effort: no leak
  detector wired in; the test exists to crash loudly under the runtime's own
  allocator if the Drop/Clone discipline breaks.
- `init_idempotent_and_mismatch_guard` — repeated init is a no-op; a
  conflicting module init fn is rejected.

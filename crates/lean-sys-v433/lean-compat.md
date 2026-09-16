# lean-compat.md — the lean.h interface surface consumed by this crate

Pinned toolchain: **leanprover/lean4 v4.33.0**
(`~/.elan/toolchains/leanprover--lean4---v4.33.0`).

**Rule: a toolchain bump ⇒ re-diff `include/lean/lean.h` against this file and
re-audit every extern below against `nm -g --defined-only lib/lean/*.a`.**
This is the byte-tie philosophy applied to the C ABI (W6.1; see
notes/studies/cedar-study.md "The interop verdict").

## Drift fixes applied on top of upstream lean-sys 0.0.9 (4.23)

| Site | 4.23 (upstream) | 4.33 (this fork) | Evidence |
|---|---|---|---|
| `src/primitive/st.rs` | externs `lean_st_mk_ref_get/set/reset/swap` (2-3 args, world token) | `lean_st_mk_ref`, `lean_st_ref_get/set/reset/swap` (no world arg) | lean.h:2972-2976. The `mk_ref_*` names never existed in any shipped lib (`nm` audit). |
| `src/io.rs` | `lean_io_result_mk_ok/mk_error` built 2-field ctors (value + world) | 1-field ctors | lean.h:2933-2942: `lean_alloc_ctor(0, 1, 0)`. Accessors only read field 0 — unchanged. |
| `src/lib.rs` | externs `lean_alloc_small` / `lean_free_small` / `lean_small_mem_size`; `small_allocator` + `mimalloc` cargo features | removed; allocation inlines are the header's `LEAN_MIMALLOC` arms, unconditional | config.h `#define LEAN_MIMALLOC`; symbols absent from `libleanrt.a` (upstream lean-sys issue #16). `mi_malloc_small`/`mi_free` are `T` in `libleanrt.a`. |
| `src/primitive/uint64.rs` | extern `lean_uint64_mix_hash` | ported `static inline` (murmur finalizer, m=0xc6a4a7935bd1e995, r=47) | lean.h:2036 marks it `static inline`. (The symbol still happens to be exported at 4.33; the header is the contract.) |
| `src/primitive/usize_.rs` | extern `lean_usize_mix_hash` | inline wrapper over `lean_uint64_mix_hash` | name absent from lean.h at 4.33 |
| module-init ABI | `initialize_X(builtin, world)` world-token shape | `lean_object* initialize_X(uint8_t builtin)`; phase-split `runtime_initialize_*` / `meta_initialize_*` emitted under the module system, legacy `initialize_*` chains both | toolchain `src/lean/Lean/Compiler/LCNF/EmitC.lean` (`emitInitFn`, `emitLegacyInitFn`, `getModInitFn`), `NameMangling.mkModuleInitializationFunctionName`; generated `lean/proofkit/.lake/build/ir/Proofkit.c`. Result is an `io_result` — check `lean_io_result_is_error`, then `lean_dec_ref`. |
| `src/init.rs` | — | added `lean_setup_args` extern + `LeanModuleInitFn` | `lean_setup_args`/`lean_initialize_runtime_module` are NOT declared in the shipped lean.h (live in `runtime/init.h` upstream) but are `T` in `libleanrt.a` at 4.33. |

## Known trap carried from the audit

`lean_st_ref_reset` is DECLARED in lean.h:2975 but DEFINED in no shipped
library (static archives and `libleanshared.so` audited). The extern is kept
to match the header; calling it is a link error. Do not use it.

## Interface surface consumed (extern blocks)

- `libleanrt.a`: object/RC/panic intrinsics, `lean_alloc_object`,
  `lean_free_object`, `lean_object_byte_size`, `lean_object_data_byte_size`,
  `lean_dec_ref_cold`, `lean_mark_mt`, `lean_mark_persistent`,
  `lean_inc_heartbeat`, task/thread init (`lean_init_task_manager*`,
  `lean_initialize_thread`, `lean_finalize_thread`), ST refs
  (`lean_st_mk_ref`, `lean_st_ref_get/set/swap`), runtime init
  (`lean_initialize_runtime_module`, `lean_setup_args`,
  `lean_io_mark_end_initialization`), mimalloc (`mi_malloc_small`, `mi_free`).
- `libleancpp.a`: `lean_initialize` (full compiler API — heavy; avoid unless
  the consumer genuinely needs the compiler stack).
- `libInit.a` (+ transitive): IO error ctors (`lean_mk_io_error_*`,
  `lean_mk_io_user_error`, `lean_io_error_to_string`), string/array/scalar
  primitives exported from compiled Init modules.
- `libgmp.a`, `libuv.a` (toolchain `lib/`): big-nat and IO-event-loop deps of
  the runtime.
- `libc++.so`/`libc++abi.so` (toolchain `lib/`, dynamic + rpath): the C++
  runtime the Lean archives were built against.

## Build/link contract (build.rs)

Discovery: `LEAN_SYS_ROOT` → `lean --print-prefix` → elan
`leanprover--lean4---v4.33.*` scan. Static link: start-group over
`Lean Init Std leancpp leanrt`, plus static `gmp`, `uv`; dynamic `c++`,
`c++abi`, `m`, `dl`, `pthread`; rpath set to the toolchain lib dir.

Smoke proof: `tests/lean/Smoke.lean` (two `@[export]` fns) → `lean -c` →
cc → `tests/smoke.rs` initializes the runtime and asserts scalar + heap-string
round-trips and the 1-field io_result ctors.

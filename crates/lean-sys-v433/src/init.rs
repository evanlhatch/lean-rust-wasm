/*!
Utilities for initializing Lean's runtime

4.33 module-init ABI (verified against the toolchain's
`src/lean/Lean/Compiler/LCNF/EmitC.lean` and the generated `.lake/build/ir`
C files):

```c
lean_object* initialize_<MangledModule>(uint8_t builtin);
```

- The world token argument is GONE (pre-4.32 signature took a trailing
  `lean_obj_arg` world).
- The result is an `io_result`: check with `lean_io_result_is_error`, then
  `lean_dec_ref` it.
- Under the module system the emitter also produces phase-split
  `runtime_initialize_*` / `meta_initialize_*` entry points; the legacy
  `initialize_*` chains both (`EmitC.emitLegacyInitFn`).
- Call order (the verified-ledger pattern):
  `lean_setup_args` → `lean_initialize_runtime_module` →
  `initialize_<Module>(1 = builtin)` → `lean_io_mark_end_initialization`.

`lean_setup_args` is not declared in the shipped `lean/lean.h` (it lives in
`runtime/init.h` upstream); the symbol is present in `libleanrt.a` at 4.33.
*/
use core::ffi::*;
use parking_lot::Mutex;

/// A convenience mutex, since [`lean_initialize_runtime_module`] and [`lean_initialize`] are *not* thread-safe.
///
/// It is convention to hold this when initializing Lean's runtime, or Lean modules, to make sure only one thread at a time is doing so.
/// This is used in this library to safely implement tests, but it is the user's responsibility to uphold thread-safety when using this API.
///
/// # Examples
/// ```rust
/// # use lean_sys_v433::*;
/// unsafe {
///     let guard = LEAN_INIT_MUTEX.lock();
///     lean_initialize_runtime_module();
///     // LEAN_INIT_MUTEX is unlocked here when `guard` goes out of scope
/// }
/// let big_nat = unsafe { lean_uint64_to_nat(u64::MAX) };
/// assert!(!lean_is_scalar(big_nat));
/// ```
pub static LEAN_INIT_MUTEX: Mutex<()> = Mutex::new(());

/// A helper function to call [`lean_initialize_runtime_module`] while holding the [`LEAN_INIT_MUTEX`].
///
/// This is equivalent to writing
/// ```rust
/// # use lean_sys_v433::*;
/// unsafe {
///     let guard = LEAN_INIT_MUTEX.lock();
///     lean_initialize_runtime_module();
/// }
/// ```
//TODO: is this safe?
pub unsafe fn lean_initialize_runtime_module_locked() {
    let _guard = LEAN_INIT_MUTEX.lock();
    lean_initialize_runtime_module();
}

/// A helper function to call [`lean_initialize`] while holding the [`LEAN_INIT_MUTEX`].
///
/// NOTE: `lean_initialize` initializes the full Lean *compiler* API and lives
/// in `libleancpp.a`; linking it pulls the compiler stack. Runtime-only
/// consumers should use [`lean_initialize_runtime_module_locked`].
//TODO: is this safe?
pub unsafe fn lean_initialize_locked() {
    let _guard = LEAN_INIT_MUTEX.lock();
    lean_initialize();
}

/// The 4.33 signature of a generated module initializer
/// (`initialize_<MangledModule>` / `runtime_initialize_*` /
/// `meta_initialize_*`).
pub type LeanModuleInitFn = unsafe extern "C" fn(builtin: u8) -> *mut crate::lean_object;

extern "C" {
    /// Set Lean's `g_argv` before initializing the runtime. Not in the
    /// shipped lean.h; symbol verified in `libleanrt.a` at 4.33.
    pub fn lean_setup_args(argc: c_int, argv: *mut *mut c_char) -> *mut *mut c_char;
    pub fn lean_initialize_runtime_module();
    /// Full compiler-API initialization (`libleancpp.a`); see
    /// [`lean_initialize_locked`].
    pub fn lean_initialize();
}

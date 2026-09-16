//! Process-global Lean runtime initialization + per-thread registration.
//!
//! Call order (the verified-ledger pattern, per lean-sys-v433's `init.rs`):
//! `lean_setup_args` → `lean_initialize_runtime_module` →
//! `initialize_<Module>(builtin = 1)` → `lean_io_mark_end_initialization` →
//! `lean_set_exit_on_panic(true)`.
//!
//! The thread that runs [`LeanRuntime::init`] is registered with the runtime
//! as a side effect; every OTHER thread that touches Lean objects must hold
//! a [`ThreadGuard`] (`lean_initialize_thread` on creation,
//! `lean_finalize_thread` on drop). [`LeanRuntime::thread_guard`] returns
//! `None` on the initializing thread to avoid double registration.

use std::marker::PhantomData;
use std::sync::OnceLock;
use std::thread::ThreadId;

use lean_sys_v433::{
    lean_dec_ref, lean_inc, lean_initialize_runtime_module, lean_initialize_thread, lean_finalize_thread,
    lean_io_error_to_string, lean_io_mark_end_initialization, lean_io_result_get_error,
    lean_io_result_is_error, lean_set_exit_on_panic, lean_setup_args, LeanModuleInitFn,
    LEAN_INIT_MUTEX,
};
use std::ffi::c_char;

use crate::marshal::to_string;
use crate::object::OwnedLeanObject;

/// Errors from [`LeanRuntime::init`].
#[derive(Debug, Clone, thiserror::Error)]
pub enum InitError {
    /// The generated module initializer returned an `io_result` error.
    #[error("lean module initialization failed: {0}")]
    ModuleInit(String),
    /// [`LeanRuntime::init`] was called with a different module init
    /// function than the one that actually initialized the process.
    #[error("lean runtime already initialized with a different module init fn")]
    MismatchedModule,
}

struct RuntimeState {
    /// The module init fn that ran, as a raw pointer for identity checks.
    init_fn: usize,
    /// The thread that ran init (already registered with the runtime).
    init_thread: ThreadId,
    /// `Err(msg)` if the module initializer returned an io_result error.
    result: Result<(), String>,
}

static STATE: OnceLock<RuntimeState> = OnceLock::new();

/// Proof token that the Lean runtime is initialized in this process.
///
/// Obtained from [`LeanRuntime::init`]. Copy-able and stateless — all global
/// state lives in the process-wide `OnceLock`.
#[derive(Debug, Clone, Copy)]
pub struct LeanRuntime {
    _private: (),
}

impl LeanRuntime {
    /// Initialize the Lean runtime and the given compiled module, once per
    /// process. Subsequent calls are cheap no-ops returning the token, or
    /// [`InitError::MismatchedModule`] if a different module init fn is
    /// passed after initialization.
    ///
    /// # Errors
    /// - [`InitError::ModuleInit`] if `initialize_<Module>` returns an
    ///   `io_result` error (message extracted via `lean_io_error_to_string`).
    /// - [`InitError::MismatchedModule`] on a conflicting second init.
    pub fn init(module_init: LeanModuleInitFn) -> Result<Self, InitError> {
        let state = STATE.get_or_init(|| RuntimeState {
            init_fn: module_init as usize,
            init_thread: std::thread::current().id(),
            // SAFETY: runs exactly once per process, under LEAN_INIT_MUTEX,
            // before any other Lean call in this crate (all object traffic
            // requires a LeanRuntime token).
            result: unsafe { initialize(module_init) },
        });
        if state.init_fn != module_init as usize {
            return Err(InitError::MismatchedModule);
        }
        match &state.result {
            Ok(()) => Ok(Self { _private: () }),
            Err(msg) => Err(InitError::ModuleInit(msg.clone())),
        }
    }

    /// Register the CURRENT thread with the Lean runtime. Returns `None` on
    /// the thread that ran [`LeanRuntime::init`] — it is already registered
    /// and must not be registered twice.
    ///
    /// The guard finalizes the thread on drop. `!Send`: drop it on the
    /// thread that created it.
    #[must_use]
    pub fn thread_guard(&self) -> Option<ThreadGuard> {
        let state = STATE.get()?;
        if state.init_thread == std::thread::current().id() {
            return None;
        }
        Some(ThreadGuard::new())
    }
}

/// Actual init sequence. Callers: the `OnceLock` closure only.
///
/// # Safety
/// Must run at most once per process, before any other Lean runtime use.
unsafe fn initialize(module_init: LeanModuleInitFn) -> Result<(), String> {
    let _guard = LEAN_INIT_MUTEX.lock();
    let mut argv: [*mut c_char; 1] = [c"lean-ffi".as_ptr().cast_mut()];
    // SAFETY: argv outlives the call; lean_setup_args only reads it here.
    unsafe { lean_setup_args(1, argv.as_mut_ptr()) };
    // SAFETY: under LEAN_INIT_MUTEX, once per process.
    unsafe { lean_initialize_runtime_module() };
    // SAFETY: 4.33 init ABI — `lean_object* initialize_X(uint8_t builtin)`.
    let res = unsafe { module_init(1 /* builtin */) };
    // SAFETY: res is an io_result owned by us.
    if unsafe { lean_io_result_is_error(res) } {
        // SAFETY: get_error borrows field 0; inc makes it ours before the
        // ctor is dec'd. lean_io_error_to_string consumes its argument.
        let err = unsafe { lean_io_result_get_error(res) };
        unsafe { lean_inc(err) };
        unsafe { lean_dec_ref(res) };
        // SAFETY: err is an owned IO error object.
        let msg_obj = unsafe { OwnedLeanObject::from_raw(lean_io_error_to_string(err)) };
        return Err(
            to_string(msg_obj.borrow()).unwrap_or_else(|_| "<unprintable lean io error>".into()),
        );
    }
    // SAFETY: ok io_result, owned by us.
    unsafe { lean_dec_ref(res) };
    // SAFETY: after all module initializers, once per process.
    unsafe { lean_io_mark_end_initialization() };
    // SAFETY: global flag; failure domain is loud-abort by design.
    unsafe { lean_set_exit_on_panic(true) };
    Ok(())
}

/// RAII registration of one OS thread with the Lean runtime.
///
/// `lean_initialize_thread` on creation, `lean_finalize_thread` on drop.
/// `!Send`/`!Sync` via `PhantomData<*mut ()>`: finalizing a different thread
/// than the one registered is a runtime error.
#[derive(Debug)]
pub struct ThreadGuard {
    _not_send_sync: PhantomData<*mut ()>,
}

impl ThreadGuard {
    fn new() -> Self {
        // SAFETY: called once per thread by construction (LeanRuntime::
        // thread_guard filters the already-registered init thread; each
        // guard registers its own current thread exactly once).
        unsafe { lean_initialize_thread() };
        Self {
            _not_send_sync: PhantomData,
        }
    }
}

impl Drop for ThreadGuard {
    fn drop(&mut self) {
        // SAFETY: balances the lean_initialize_thread in Self::new on this
        // same thread (!Send guarantees same-thread drop).
        unsafe { lean_finalize_thread() };
    }
}

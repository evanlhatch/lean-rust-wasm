//! Smoke test (W6.1): initialize the Lean 4.33 runtime in-process, run the
//! generated module initializer for `tests/lean/Smoke.lean` under the 4.33
//! init ABI (`lean_object* initialize_X(uint8_t builtin)` — no world token),
//! then call `@[export]`ed Lean functions over the C ABI.
//!
//! Fixture C is compiled by this crate's build.rs into `liblean_sys_v433_smoke.a`.
#![allow(non_snake_case)]

use lean_sys_v433::*;
use std::ffi::{c_char, CStr};
use std::sync::Once;

extern "C" {
    /// 4.33 module-init ABI: `lean_object* initialize_X(uint8_t builtin)`.
    /// `lean -c tests/lean/Smoke.lean` derives the module name from the file
    /// path, hence `tests.lean.Smoke` → `initialize_tests_lean_Smoke`.
    fn initialize_tests_lean_Smoke(builtin: u8) -> *mut lean_object;
    fn lean_sys_smoke_add40(n: u64) -> u64;
    fn lean_sys_smoke_greet(name: *mut lean_object) -> *mut lean_object;
}

static INIT: Once = Once::new();

fn lean_runtime_init() {
    INIT.call_once(|| unsafe {
        let _guard = LEAN_INIT_MUTEX.lock();
        let mut argv: [*mut c_char; 1] = [c"lean-sys-v433-smoke".as_ptr() as *mut c_char];
        lean_setup_args(1, argv.as_mut_ptr());
        lean_initialize_runtime_module();
        let res = initialize_tests_lean_Smoke(1 /* builtin */);
        assert!(
            !lean_io_result_is_error(res),
            "initialize_tests_lean_Smoke failed under the 4.33 init ABI"
        );
        lean_dec_ref(res);
        lean_io_mark_end_initialization();
    });
}

#[test]
fn scalar_round_trip() {
    lean_runtime_init();
    assert_eq!(unsafe { lean_sys_smoke_add40(2) }, 42);
    assert_eq!(unsafe { lean_sys_smoke_add40(u64::MAX) }, 39); // wraps: max + 40
}

#[test]
fn string_round_trip() {
    lean_runtime_init();
    unsafe {
        let arg = lean_mk_string(c"host".as_ptr() as *const u8);
        let res = lean_sys_smoke_greet(arg); // Lean consumes arg's RC
        assert!(lean_is_string(res));
        let cstr = CStr::from_ptr(lean_string_cstr(res) as *const c_char);
        assert_eq!(cstr.to_str().unwrap(), "hello from lean, host");
        lean_dec(res); // we own the result
    }
}

/// io_result ctors are 1-field at 4.33 — exercise the Rust-side port.
#[test]
fn io_result_one_field_ctors() {
    lean_runtime_init();
    unsafe {
        let ok = lean_io_result_mk_ok(lean_box(7));
        assert!(lean_io_result_is_ok(ok));
        assert_eq!(lean_unbox(lean_io_result_get_value(ok)), 7);
        lean_dec(ok);

        let err = lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(
            c"boom".as_ptr() as *const u8,
        )));
        assert!(lean_io_result_is_error(err));
        // get_error is borrowed; dec'ing the ctor consumes its field.
        assert!(lean_is_string(lean_io_result_get_error(err)) || lean_is_ctor(lean_io_result_get_error(err)));
        lean_dec(err);
    }
}

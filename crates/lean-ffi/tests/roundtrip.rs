//! Round-trip tests (W6.2): init the Lean 4.33 runtime via `LeanRuntime`,
//! call the `tests/lean/Echo.lean` exports through `call_export`, and
//! exercise the RAII/tag-check machinery. Fixture C is compiled by this
//! crate's build.rs into `liblean_ffi_echo_fixture.a`.
//!
//! All Lean-object traffic runs on spawned threads holding a `ThreadGuard`:
//! cargo's test threads are NOT registered with the Lean runtime, and
//! unregistered threads touching Lean objects is UB territory we stay out of
//! by construction.
#![allow(non_snake_case)]

use lean_ffi::{
    bytes_from_sarray, call_export, sarray_from_bytes, string_from, LeanObjectError, LeanRuntime,
};
use lean_sys_v433::lean_object;

extern "C" {
    /// 4.33 module-init ABI: `lean_object* initialize_X(uint8_t builtin)`.
    /// Module name derived from the fixture path (see build.rs).
    fn initialize_tests_lean_Echo(builtin: u8) -> *mut lean_object;
    fn lean_ffi_echo_reverse(bs: *mut lean_object) -> *mut lean_object;
    fn lean_ffi_mk_pair(bs: *mut lean_object) -> *mut lean_object;
}

fn runtime() -> LeanRuntime {
    LeanRuntime::init(initialize_tests_lean_Echo).expect("lean runtime init failed")
}

/// Run `f` on a freshly spawned thread registered with the Lean runtime.
fn on_lean_thread(f: impl FnOnce() + Send + 'static) {
    let rt = runtime();
    std::thread::spawn(move || {
        let _guard = rt.thread_guard();
        f();
    })
    .join()
    .expect("lean worker thread panicked");
}

#[test]
fn reverse_echo_roundtrip() {
    on_lean_thread(|| {
        let cases: Vec<Vec<u8>> = vec![
            vec![],                        // empty
            vec![0x00],                    // single byte
            b"hello lean".to_vec(),        // ascii
            (0u8..=255).collect(),         // 256-byte boundary, every value
            (0..300u32).map(|i| (i * 7 % 251) as u8).collect(), // past the boundary
        ];
        for input in cases {
            let mut expected = input.clone();
            expected.reverse();
            let out = call_export(lean_ffi_echo_reverse, &input).expect("reverse export failed");
            assert_eq!(out, expected, "reverse mismatch for len {}", input.len());
        }
    });
}

#[test]
fn string_round_trip() {
    on_lean_thread(|| {
        let s = string_from("héllo λαν — utf8 ✓");
        let back = lean_ffi::to_string(s.borrow()).expect("to_string failed");
        assert_eq!(back, "héllo λαν — utf8 ✓");
    });
}

#[test]
fn ctor_tag_checks() {
    on_lean_thread(|| {
        // mk_pair returns a tag-0 ctor with two object fields.
        let arg = sarray_from_bytes(b"ab");
        // SAFETY: exported pure Lean fn; arg reference stolen via into_raw.
        let res = unsafe { lean_ffi_mk_pair(arg.into_raw()) };
        // SAFETY: we own the returned reference.
        let res = unsafe { lean_ffi::OwnedLeanObject::from_raw(res) };

        let ctor = res.borrow().as_ctor(0).expect("pair should be tag 0");
        assert_eq!(ctor.num_fields(), 2);
        let f0 = ctor.get(0).expect("field 0 in bounds");
        assert_eq!(bytes_from_sarray(f0).expect("field 0 is a byte array"), b"ab");
        let f1 = ctor.get(1).expect("field 1 in bounds");
        assert_eq!(bytes_from_sarray(f1).expect("field 1 is a byte array"), b"ba");

        // Index out of bounds.
        assert!(matches!(
            ctor.get(2),
            Err(LeanObjectError::FieldIndexOutOfBounds {
                index: 2,
                num_fields: 2
            })
        ));

        // Wrong expected tag.
        assert!(matches!(
            res.borrow().as_ctor(1),
            Err(LeanObjectError::UnexpectedTag {
                expected: 1,
                actual: 0
            })
        ));

        // A string is not a ctor: tag byte is LeanString (245-ish), so the
        // tag check rejects it without ever touching field accessors.
        let s = string_from("x");
        assert!(matches!(
            s.borrow().as_ctor(0),
            Err(LeanObjectError::UnexpectedTag { expected: 0, .. })
        ));

        // Marshaling type checks reject wrong kinds.
        assert!(matches!(
            bytes_from_sarray(s.borrow()),
            Err(LeanObjectError::NotByteArray { .. })
        ));
        assert!(matches!(
            lean_ffi::to_string(res.borrow()),
            Err(LeanObjectError::NotString { .. })
        ));
    });
}

/// Best-effort refcount sanity: 10k create/clone/drop cycles. There is no
/// leak detector wired in here — the discipline (Drop→dec, Clone→inc,
/// steal-on-export) is what makes this safe; this test's job is to crash
/// loudly (double-dec / use-after-free under the runtime's own allocator)
/// if that discipline breaks.
#[test]
fn refcount_churn() {
    on_lean_thread(|| {
        let payload = [0xABu8; 64];
        for _ in 0..10_000 {
            let o = sarray_from_bytes(&payload);
            let c1 = o.clone();
            let c2 = c1.clone();
            drop(c1);
            drop(o);
            let bytes = bytes_from_sarray(c2.borrow()).expect("churn readback failed");
            assert_eq!(bytes, payload);
            drop(c2);
        }
    });
}

/// Second init with the SAME module is a cheap no-op; a DIFFERENT module
/// init fn is rejected.
#[test]
fn init_idempotent_and_mismatch_guard() {
    extern "C" fn other_module(builtin: u8) -> *mut lean_object {
        unsafe { initialize_tests_lean_Echo(builtin) } // distinct fn pointer, same body
    }
    runtime(); // same fn: ok, cheap no-op
    assert!(matches!(
        LeanRuntime::init(other_module),
        Err(lean_ffi::InitError::MismatchedModule)
    ));
}

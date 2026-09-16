/*!
Rust bindings to [Lean 4](https://github.com/leanprover/lean4)'s C API

Functions and comments manually translated from those in the [`lean.h` header](https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h) provided with Lean 4
*/
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(clippy::missing_safety_doc)]
#![no_std]

use core::ffi::*;
use core::sync::atomic::{AtomicI32, AtomicI64, AtomicU32, Ordering};
use memoffset::raw_field;
use static_assertions::const_assert;

pub mod alloc;
pub mod array;
pub mod closure;
pub mod constructor;
pub mod dbg;
pub mod external;
pub mod init;
pub mod int;
pub mod io;
pub mod libuv;
pub mod nat;
pub mod panic;
pub mod primitive;
pub mod sarray;
pub mod share_common;
pub mod string;
pub mod task;
pub mod thread;
pub mod thunk;

pub use array::*;
pub use closure::*;
pub use constructor::*;
pub use dbg::*;
pub use external::*;
pub use init::*;
pub use int::*;
pub use io::*;
pub use libuv::*;
pub use nat::*;
pub use primitive::*;
pub use sarray::*;
pub use share_common::*;
pub use string::*;
pub use task::*;
pub use thread::*;
pub use thunk::*;

// 4.33: the small allocator and its exports (`lean_alloc_small`,
// `lean_free_small`, `lean_small_mem_size`) were REMOVED; `LEAN_MIMALLOC` is
// unconditionally defined (include/lean/config.h) and the mimalloc symbols
// (`mi_malloc_small`, `mi_free`) ship inside `libleanrt.a`. The allocation
// inlines below are therefore the header's `#ifdef LEAN_MIMALLOC` arms,
// unconditional. See lean-compat.md.
pub const LEAN_CLOSURE_MAX_ARGS: u32 = 16;
pub const LEAN_OBJECT_SIZE_DELTA: usize = 8;
pub const LEAN_MAX_SMALL_OBJECT_SIZE: u32 = 4096;
pub const LeanMaxCtorTag: u8 = 243;
pub const LeanPromise: u8 = 244;
pub const LeanClosure: u8 = 245;
pub const LeanArray: u8 = 246;
pub const LeanStructArray: u8 = 247;
pub const LeanScalarArray: u8 = 248;
pub const LeanString: u8 = 249;
pub const LeanMPZ: u8 = 250;
pub const LeanThunk: u8 = 251;
pub const LeanTask: u8 = 252;
pub const LeanRef: u8 = 253;
pub const LeanExternal: u8 = 254;
pub const LeanReserved: u8 = 255;
pub const LEAN_MAX_CTOR_FIELDS: u32 = 256;
pub const LEAN_MAX_CTOR_SCALARS_SIZE: u32 = 1024;

const_assert! {
    layout_compat::<c_int, i32>() ||
    layout_compat::<c_int, i64>()
}

#[inline(always)]
pub const fn layout_compat<A, B>() -> bool {
    size_of::<A>() == size_of::<B>() && align_of::<A>() == align_of::<B>()
}

#[inline(always)]
pub unsafe fn c_int_load(p: *const c_int, order: Ordering) -> c_int {
    match c_int::BITS {
        32 => (*(p as *const AtomicI32)).load(order) as c_int,
        64 => (*(p as *const AtomicI64)).load(order) as c_int,
        _ => unreachable!(),
    }
}

mod types;
pub use types::*;

#[inline]
pub fn lean_is_big_object_tag(tag: u8) -> bool {
    matches!(
        tag,
        LeanArray | LeanStructArray | LeanScalarArray | LeanString
    )
}

/// Whether this lean object is a scalar
///
/// # Examples
/// ```rust
/// # use lean_sys_v433::*;
/// unsafe { lean_initialize_runtime_module(); }
/// let arr = unsafe { lean_mk_empty_array() };
/// assert!(lean_is_scalar(lean_box(5)));
/// assert!(!lean_is_scalar(arr));
/// ```
#[inline(always)]
pub fn lean_is_scalar(obj: *const lean_object) -> bool {
    (obj as usize & 1) == 1
}

/// Box a `usize` into a `lean_object`
///
/// # Examples
/// ```rust
/// # use lean_sys_v433::*;
/// for i in [0, 5, 658948, 1 << (usize::BITS - 2)] {
///     assert_eq!(lean_unbox(lean_box(i)), i);
/// }
/// ```
#[inline(always)]
pub const fn lean_box(n: usize) -> *mut lean_object {
    ((n << 1) | 1) as *mut lean_object
}

/// Unbox a `lean_object` into a `usize`
///
/// See [`lean_box`] for usage examples.
#[inline(always)]
pub fn lean_unbox(o: *const lean_object) -> usize {
    o as usize >> 1
}

#[inline]
pub const fn lean_align(v: usize, a: usize) -> usize {
    (v / a).wrapping_mul(a) + a.wrapping_mul(!v.is_multiple_of(a) as usize)
}

#[inline]
pub fn lean_get_slot_idx(sz: c_uint) -> c_uint {
    debug_assert_ne!(sz, 0);
    debug_assert_eq!(lean_align(sz as usize, LEAN_OBJECT_SIZE_DELTA), sz as usize);
    sz / (LEAN_OBJECT_SIZE_DELTA as c_uint) - 1
}

extern "C" {
    // mimalloc entry points used by the header's allocation inlines; exported
    // from `libleanrt.a` at 4.33.
    fn mi_malloc_small(sz: usize) -> *mut c_void;
    fn mi_free(p: *mut c_void);
}

#[inline]
pub unsafe fn lean_alloc_small_object(sz: c_uint) -> *mut lean_object {
    lean_inc_heartbeat();
    // HACK: emulate behavior of small allocator to avoid `leangz` breakage for now
    let sz = lean_align(sz as usize, LEAN_OBJECT_SIZE_DELTA) as c_uint;
    let mem = mi_malloc_small(sz as usize);
    if mem.is_null() {
        lean_internal_panic_out_of_memory()
    }
    let o = mem.cast::<lean_object>();
    (*o).m_cs_sz = sz as u16;
    o
}

#[inline]
pub unsafe fn lean_alloc_ctor_memory(sz: c_uint) -> *mut lean_object {
    let sz1 = lean_align(sz as usize, LEAN_OBJECT_SIZE_DELTA) as c_uint;
    // NB: the header passes the UNALIGNED `sz` here (re-aligned inside).
    let r = lean_alloc_small_object(sz);
    if sz1 > sz {
        /* Initialize last word.
        In our runtime `lean_object_byte_size` is always
        a multiple of the machine word size for constructors.

        By setting the last word to 0, we make sure the sharing
        maximizer procedures at `maxsharing.cpp` and `compact.cpp` are
        not affected by uninitialized data at the (sz1 - sz) last bytes.
        Otherwise, we may mistakenly assume to structurally equal
        objects are not identical because of this uninitialized memory. */
        *r.byte_add(sz1 as usize).cast::<usize>().sub(1) = 0;
    }
    r
}

#[inline(always)]
pub unsafe fn lean_small_object_size(o: *mut lean_object) -> c_uint {
    (*o).m_cs_sz as c_uint
}

#[inline(always)]
pub unsafe fn lean_free_small_object(o: *mut lean_object) {
    // 4.33 header: "We must NOT use `m_cs_sz` here as it is repurposed for
    // the deletion list" — plain `mi_free`.
    mi_free(o.cast())
}

#[inline(always)]
pub unsafe fn lean_ptr_tag(o: *const lean_object) -> u8 {
    *raw_field!(o, lean_object, m_tag)
}

#[inline(always)]
pub unsafe fn lean_ptr_other(o: *const lean_object) -> c_uint {
    *raw_field!(o, lean_object, m_other) as c_uint
}

/// Whether an object is multi-threaded
#[inline(always)]
pub unsafe fn lean_is_mt(o: *const lean_object) -> bool {
    relaxed_rc_load(o) < 0
}

/// Whether an object is single-threaded
#[inline(always)]
pub unsafe fn lean_is_st(o: *const lean_object) -> bool {
    relaxed_rc_load(o) > 0
}

/// Perform a relaxed load of the reference counter of `o`, which must be a pointer into a valid [`lean_object`]
#[inline(always)]
pub unsafe fn relaxed_rc_load(o: *const lean_object) -> c_int {
    c_int_load(lean_get_rc_mt_addr(o as *mut _), Ordering::Relaxed)
}

/* We never update the reference counter of objects stored in compact regions and allocated at initialization time. */
#[inline(always)]
pub unsafe fn lean_is_persistent(o: *const lean_object) -> bool {
    relaxed_rc_load(o) == 0
}

/// Whether an object is reference counted
#[inline(always)]
pub unsafe fn lean_has_rc(o: *const lean_object) -> bool {
    relaxed_rc_load(o) != 0
}

#[inline(always)]
pub unsafe fn lean_get_rc_mt_addr(o: *mut lean_object) -> *mut c_int {
    raw_field!(o, lean_object, m_rc) as *mut c_int
}

#[inline]
pub unsafe fn lean_inc_ref_n(o: *mut lean_object, n: usize) {
    if lean_is_st(o) {
        *(raw_field!(o, lean_object, m_rc) as *mut c_int) += n as c_int
    } else if *raw_field!(o, lean_object, m_rc) != 0 {
        (*lean_get_rc_mt_addr(o).cast::<AtomicU32>()).fetch_sub(n as c_uint, Ordering::Relaxed);
    }
}

#[inline]
pub unsafe fn lean_inc_ref(o: *mut lean_object) {
    lean_inc_ref_n(o, 1)
}

#[inline]
pub unsafe fn lean_dec_ref(o: *mut lean_object) {
    if relaxed_rc_load(o) > 1 {
        *(raw_field!(o, lean_object, m_rc) as *mut c_int) -= 1
    } else if *raw_field!(o, lean_object, m_rc) != 0 {
        lean_dec_ref_cold(o)
    }
}

#[inline]
pub unsafe fn lean_inc(o: *mut lean_object) {
    if !lean_is_scalar(o) {
        lean_inc_ref(o)
    }
}

#[inline]
pub unsafe fn lean_inc_n(o: *mut lean_object, n: usize) {
    if !lean_is_scalar(o) {
        lean_inc_ref_n(o, n)
    }
}

#[inline]
pub unsafe fn lean_dec(o: *mut lean_object) {
    if !lean_is_scalar(o) {
        lean_dec_ref(o)
    }
}

#[inline(always)]
pub unsafe fn lean_is_ctor(o: *const lean_object) -> bool {
    lean_ptr_tag(o) <= LeanMaxCtorTag
}

#[inline(always)]
pub unsafe fn lean_is_closure(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanClosure
}

#[inline(always)]
pub unsafe fn lean_is_array(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanArray
}

#[inline(always)]
pub unsafe fn lean_is_sarray(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanScalarArray
}

#[inline(always)]
pub unsafe fn lean_is_string(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanString
}

#[inline(always)]
pub unsafe fn lean_is_mpz(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanMPZ
}

#[inline(always)]
pub unsafe fn lean_is_thunk(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanThunk
}

#[inline(always)]
pub unsafe fn lean_is_task(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanTask
}

#[inline(always)]
pub unsafe fn lean_is_promise(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanPromise
}

#[inline(always)]
pub unsafe fn lean_is_external(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanExternal
}

#[inline(always)]
pub unsafe fn lean_is_ref(o: *const lean_object) -> bool {
    lean_ptr_tag(o) == LeanRef
}

#[inline(always)]
pub unsafe fn lean_obj_tag(o: *const lean_object) -> c_uint {
    if lean_is_scalar(o) {
        lean_unbox(o) as c_uint
    } else {
        lean_ptr_tag(o) as c_uint
    }
}

#[inline(always)]
pub unsafe fn lean_to_ctor(o: *mut lean_object) -> *mut lean_ctor_object {
    debug_assert!(lean_is_ctor(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_closure(o: *mut lean_object) -> *mut lean_closure_object {
    debug_assert!(lean_is_closure(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_array(o: *mut lean_object) -> *mut lean_array_object {
    debug_assert!(lean_is_array(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_sarray(o: *mut lean_object) -> *mut lean_sarray_object {
    debug_assert!(lean_is_sarray(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_string(o: *mut lean_object) -> *mut lean_string_object {
    debug_assert!(lean_is_string(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_thunk(o: *mut lean_object) -> *mut lean_thunk_object {
    debug_assert!(lean_is_thunk(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_task(o: *mut lean_object) -> *mut lean_task_object {
    debug_assert!(lean_is_task(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_promise(o: *mut lean_object) -> *mut lean_promise_object {
    debug_assert!(lean_is_promise(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_ref(o: *mut lean_object) -> *mut lean_ref_object {
    debug_assert!(lean_is_ref(o));
    o.cast()
}

#[inline(always)]
pub unsafe fn lean_to_external(o: *mut lean_object) -> *mut lean_external_object {
    debug_assert!(lean_is_external(o));
    o.cast()
}

#[inline]
pub unsafe fn lean_is_exclusive(o: *mut lean_object) -> bool {
    //TODO: likely... or, why not just relaxed_rc_load(o) == 1?
    if lean_is_st(o) {
        *raw_field!(o, lean_object, m_rc) == 1
    } else {
        false
    }
}

#[inline]
pub unsafe fn lean_is_exclusive_obj(o: *mut lean_object) -> u8 {
    lean_is_exclusive(o) as u8
}

#[inline]
pub unsafe fn lean_is_shared(o: *mut lean_object) -> bool {
    //TODO: likely... or, why not just relaxed_rc_load(o) > 1?
    if lean_is_st(o) {
        *raw_field!(o, lean_object, m_rc) > 1
    } else {
        false
    }
}

#[inline]
pub unsafe fn lean_set_st_header(o: *mut lean_object, tag: c_uint, other: c_uint) {
    *lean_get_rc_mt_addr(o) = 1;
    (raw_field!(o, lean_object, m_other) as *mut u8).write(other as u8);
    (raw_field!(o, lean_object, m_tag) as *mut u8).write(tag as u8);
    // 4.33: `m_cs_sz` already initialized by `lean_alloc_small_object`
    // (mimalloc is unconditional), so the header does not touch it here.
}

/** Remark: we don't need a reference counter for objects that are not stored in the heap.
Thus, we use the area to store the object size for small objects. */
#[inline]
pub unsafe fn lean_set_non_heap_header(o: *mut lean_object, sz: usize, tag: c_uint, other: c_uint) {
    debug_assert!(sz > 0);
    debug_assert!(sz < (1 << 16));
    debug_assert!(sz == 1 || !lean_is_big_object_tag(tag as u8));
    *lean_get_rc_mt_addr(o) = 0;
    (raw_field!(o, lean_object, m_cs_sz) as *mut u16).write(sz as u16);
    (raw_field!(o, lean_object, m_other) as *mut u8).write(other as u8);
    (raw_field!(o, lean_object, m_tag) as *mut u8).write(tag as u8);
}

/** `lean_set_non_heap_header` for (potentially) big objects such as arrays and strings. */
#[inline(always)]
pub unsafe fn lean_set_non_heap_header_for_big(o: *mut lean_object, tag: c_uint, other: c_uint) {
    lean_set_non_heap_header(o, 1, tag, other)
}

extern "C" {
    pub fn lean_set_exit_on_panic(flag: bool);
    /// Enable/disable panic messages
    pub fn lean_set_panic_messages(flag: bool);
    pub fn lean_panic(msg: *const u8, force_stderr: bool);
    pub fn lean_panic_fn(default_val: *mut lean_object, msg: *mut lean_object);
    pub fn lean_internal_panic(msg: *const u8) -> !;
    pub fn lean_internal_panic_out_of_memory() -> !;
    pub fn lean_internal_panic_unreachable() -> !;
    pub fn lean_internal_panic_rc_overflow() -> !;
    // REMOVED at 4.33 (upstream lean-sys#16): lean_alloc_small, lean_free_small,
    // lean_small_mem_size — symbols absent from libleanrt.a and lean.h.
    pub fn lean_inc_heartbeat();
    pub fn lean_alloc_object(sz: usize) -> *mut lean_object;
    pub fn lean_free_object(o: *mut lean_object);
    /** The object size may be slightly bigger for constructor objects.
    The runtime does not track the size of the scalar size area.
    All constructor objects are "small", and allocated into pages.
    We retrieve their size by accessing the page header. The size of
    small objects is a multiple of `LEAN_OBJECT_SIZE_DELTA` */
    pub fn lean_object_byte_size(o: *mut lean_object) -> usize;
    /** Returns the size of the salient part of an object's storage,
    i.e. the parts that contribute to the value representation;
    padding or unused capacity is excluded. Operations that read
    from an object's storage must only access these parts, since
    the non-salient parts may not be initialized. */
    pub fn lean_object_data_byte_size(o: *mut lean_object) -> usize;
    #[cold]
    pub fn lean_dec_ref_cold(o: *mut lean_object);
    pub fn lean_mark_mt(o: *mut lean_object);
    pub fn lean_mark_persistent(o: *mut lean_object);
}

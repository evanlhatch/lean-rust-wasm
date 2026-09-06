//! Implementation for WASI Preview 3.
//!
//! Added by the wasmtron spike patch (see workspace `[patch.crates-io]`
//! and notes/otto-spike.md): upstream 0.3.4 has backends only for
//! preview 1/2. Binding style copied verbatim from getrandom 0.4.3's
//! `wasi_p2_3.rs` — manual externs instead of the `wasip3` crate to
//! avoid a new lock entry.
use crate::Error;
use core::{mem::MaybeUninit, ptr::copy_nonoverlapping};

#[link(wasm_import_module = "wasi:random/random@0.3.0")]
unsafe extern "C" {
    #[link_name = "get-random-u64"]
    safe fn get_random_u64() -> u64;
}

#[inline]
pub fn inner_u32() -> Result<u32, Error> {
    let val = get_random_u64();
    Ok(crate::util::truncate(val))
}

#[inline]
pub fn inner_u64() -> Result<u64, Error> {
    Ok(get_random_u64())
}

#[inline]
pub fn fill_inner(dest: &mut [MaybeUninit<u8>]) -> Result<(), Error> {
    let (prefix, chunks, suffix) = unsafe { dest.align_to_mut::<MaybeUninit<u64>>() };

    if !prefix.is_empty() {
        let val = get_random_u64();
        let src = (&val as *const u64).cast();
        unsafe {
            copy_nonoverlapping(src, prefix.as_mut_ptr(), prefix.len());
        }
    }

    for dst in chunks {
        dst.write(get_random_u64());
    }

    if !suffix.is_empty() {
        let val = get_random_u64();
        let src = (&val as *const u64).cast();
        unsafe {
            copy_nonoverlapping(src, suffix.as_mut_ptr(), suffix.len());
        }
    }

    Ok(())
}

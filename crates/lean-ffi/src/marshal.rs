//! Marshaling: the ONLY things that cross the boundary are scalars, byte
//! arrays, and strings (cedar's dumb-by-design channel; payloads ride inside
//! the byte arrays in our codec's wire format). No structure-field reads
//! off-Lean beyond [`crate::object::LeanCtorObject`] tag checks.

use lean_sys_v433::{
    lean_alloc_sarray, lean_mk_string_from_bytes, lean_object, lean_sarray_cptr,
    lean_sarray_elem_size, lean_sarray_size, lean_string_cstr, lean_string_size,
};

use crate::object::{LeanObject, LeanObjectError, OwnedLeanObject};

/// `&[u8]` → Lean `ByteArray` (an owned sarray with element size 1).
pub fn sarray_from_bytes(bytes: &[u8]) -> OwnedLeanObject {
    // SAFETY: fresh sarray with size == capacity == len; cptr points at
    // len writable bytes; from_raw takes the fresh reference.
    unsafe {
        let o = lean_alloc_sarray(1, bytes.len(), bytes.len());
        if !bytes.is_empty() {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), lean_sarray_cptr(o), bytes.len());
        }
        OwnedLeanObject::from_raw(o)
    }
}

/// Lean `ByteArray` → owned `Vec<u8>` (copies out of the Lean heap).
///
/// # Errors
/// [`LeanObjectError::NotByteArray`] if `obj` is not a scalar array with
/// element size 1.
pub fn bytes_from_sarray(obj: LeanObject<'_>) -> Result<Vec<u8>, LeanObjectError> {
    if !obj.is_sarray() {
        return Err(LeanObjectError::NotByteArray { actual: obj.tag() });
    }
    // SAFETY: is_sarray verified; elem_size reads the header.
    if unsafe { lean_sarray_elem_size(obj.as_ptr()) } != 1 {
        return Err(LeanObjectError::NotByteArray { actual: obj.tag() });
    }
    // SAFETY: sarray of u8 with size n; cptr valid for n bytes while the
    // borrow lives; to_vec copies before the borrow can end.
    unsafe {
        let n = lean_sarray_size(obj.as_ptr());
        let ptr = lean_sarray_cptr(obj.as_ptr());
        Ok(std::slice::from_raw_parts(ptr, n).to_vec())
    }
}

/// `&str` → Lean `String` (owned; `lean_mk_string_from_bytes` copies and
/// computes the character length).
pub fn string_from(s: &str) -> OwnedLeanObject {
    // SAFETY: from_raw takes the fresh reference. Input is &str, so the
    // checked (UTF-8-validating) constructor cannot fail.
    unsafe { OwnedLeanObject::from_raw(lean_mk_string_from_bytes(s.as_ptr(), s.len())) }
}

/// Lean `String` → owned Rust `String` (copies; validates UTF-8 rather than
/// assuming it).
///
/// # Errors
/// - [`LeanObjectError::NotString`] if `obj` is not a string object.
/// - [`LeanObjectError::Utf8`] if the bytes fail validation (unreachable
///   for Lean-built strings; checked anyway).
pub fn to_string(obj: LeanObject<'_>) -> Result<String, LeanObjectError> {
    if !obj.is_string() {
        return Err(LeanObjectError::NotString { actual: obj.tag() });
    }
    // SAFETY: is_string verified. m_size counts bytes INCLUDING the NUL
    // terminator, hence - 1.
    unsafe {
        let n = lean_string_size(obj.as_ptr()) - 1;
        let bytes = std::slice::from_raw_parts(lean_string_cstr(obj.as_ptr()), n);
        Ok(std::str::from_utf8(bytes)?.to_owned())
    }
}

/// C ABI of a pure exported `ByteArray → ByteArray` Lean function
/// (`@[export] def f (bs : ByteArray) : ByteArray`).
pub type ByteArrayExport = unsafe extern "C" fn(*mut lean_object) -> *mut lean_object;

/// Call a `ByteArray → ByteArray` export. Ownership: Lean steals the
/// argument reference (`into_raw` — no dec); Rust owns the return.
///
/// # Errors
/// [`LeanObjectError::NotByteArray`] if the export returns something that
/// is not a byte array (an export-signature drift — loud, not silent).
pub fn call_export(f: ByteArrayExport, input: &[u8]) -> Result<Vec<u8>, LeanObjectError> {
    let arg = sarray_from_bytes(input);
    // SAFETY: f is an exported pure Lean function of one ByteArray; arg's
    // reference is transferred (into_raw forgets without dec'ing).
    let res = unsafe { f(arg.into_raw()) };
    // SAFETY: the export's return reference belongs to the caller.
    let res = unsafe { OwnedLeanObject::from_raw(res) };
    bytes_from_sarray(res.borrow())
}

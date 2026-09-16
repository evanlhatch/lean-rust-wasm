//! RAII ownership over `lean_object*` (the cedar-lean-ffi `lean_object.rs`
//! pattern):
//!
//! - [`OwnedLeanObject`]: owns one reference count. `Drop` → `lean_dec`,
//!   `Clone` → `lean_inc`.
//! - [`LeanObject<'a>`]: borrowed reference with a `PhantomData` lifetime —
//!   no RC traffic, tied to the owner's borrow.
//! - [`LeanCtorObject<'a>`]: tag-checked constructor view over a borrowed
//!   object; the ONLY structure-field access this crate performs off-Lean
//!   (io_result/Except-shaped tag checks and fixture verification).
//!
//! Deliberately NO `Send`/`Sync` impls: single-threaded Lean objects carry a
//! non-atomic refcount; cross-thread sharing requires `lean_mark_mt` and is
//! out of scope here.

use std::marker::PhantomData;

use lean_sys_v433::{
    lean_ctor_get, lean_ctor_num_objs, lean_dec, lean_inc, lean_is_ctor, lean_is_sarray,
    lean_is_scalar, lean_is_string, lean_obj_tag, lean_object,
};

/// Errors from tag-checked object access and marshaling.
#[derive(Debug, Clone, thiserror::Error)]
pub enum LeanObjectError {
    /// Constructor tag mismatch (`lean_obj_tag` is scalar-safe: a boxed
    /// fieldless ctor reports its scalar value as the tag).
    #[error("unexpected ctor tag: expected {expected}, got {actual}")]
    UnexpectedTag {
        /// Tag the caller required.
        expected: u32,
        /// Tag the object actually carries.
        actual: u32,
    },
    /// Ctor field read past the object-field count.
    #[error("ctor field index {index} out of bounds ({num_fields} object fields)")]
    FieldIndexOutOfBounds {
        /// Index the caller asked for.
        index: u32,
        /// Number of object fields the ctor actually has.
        num_fields: u32,
    },
    /// `to_string` on a non-string object.
    #[error("expected a lean string object, got tag {actual}")]
    NotString {
        /// Tag the object actually carries.
        actual: u32,
    },
    /// `bytes_from_sarray` on a non-ByteArray object (a ByteArray is a
    /// scalar array with element size 1).
    #[error("expected a lean byte array (sarray, elem size 1), got tag {actual}")]
    NotByteArray {
        /// Tag the object actually carries.
        actual: u32,
    },
    /// Lean string bytes failed UTF-8 validation (should be unreachable —
    /// Lean strings are UTF-8 by construction — but checked, not assumed).
    #[error("lean string bytes are not valid utf-8: {0}")]
    Utf8(#[from] std::str::Utf8Error),
}

/// An owned Lean object: Rust holds one reference count.
///
/// Construct via [`crate::marshal`] helpers or
/// [`OwnedLeanObject::from_raw`]; drop decs, clone incs.
#[derive(Debug)]
pub struct OwnedLeanObject {
    ptr: *mut lean_object,
}

impl OwnedLeanObject {
    /// Take ownership of one existing reference on `ptr`.
    ///
    /// # Safety
    /// `ptr` must be a valid `lean_object*` (or Lean scalar) with a
    /// reference the caller is transferring; no other owner may dec that
    /// same reference.
    pub unsafe fn from_raw(ptr: *mut lean_object) -> Self {
        debug_assert!(!ptr.is_null());
        Self { ptr }
    }

    /// The raw pointer. The borrow it came from bounds its validity.
    pub fn as_ptr(&self) -> *mut lean_object {
        self.ptr
    }

    /// Borrow without RC traffic.
    pub fn borrow(&self) -> LeanObject<'_> {
        LeanObject {
            ptr: self.ptr,
            _marker: PhantomData,
        }
    }

    /// Relinquish ownership WITHOUT dec'ing (e.g. passing an argument to a
    /// Lean export, which steals the reference).
    pub fn into_raw(self) -> *mut lean_object {
        let ptr = self.ptr;
        std::mem::forget(self);
        ptr
    }
}

impl Clone for OwnedLeanObject {
    fn clone(&self) -> Self {
        // SAFETY: ptr is valid while self lives; inc adds the reference the
        // new owner will dec.
        unsafe { lean_inc(self.ptr) };
        Self { ptr: self.ptr }
    }
}

impl Drop for OwnedLeanObject {
    fn drop(&mut self) {
        // SAFETY: we own exactly one reference; lean_dec handles scalars
        // (no-op) and heap objects (dec + free at 0).
        unsafe { lean_dec(self.ptr) };
    }
}

/// A borrowed Lean object: no RC traffic, lifetime-bound to its owner.
#[derive(Debug, Clone, Copy)]
pub struct LeanObject<'a> {
    ptr: *mut lean_object,
    _marker: PhantomData<&'a lean_object>,
}

impl<'a> LeanObject<'a> {
    /// Wrap a borrowed pointer.
    ///
    /// # Safety
    /// `ptr` must be a valid `lean_object*` (or Lean scalar) that outlives
    /// `'a` under someone else's reference.
    pub unsafe fn from_borrowed(ptr: *mut lean_object) -> Self {
        debug_assert!(!ptr.is_null());
        Self {
            ptr,
            _marker: PhantomData,
        }
    }

    /// The raw pointer.
    pub fn as_ptr(&self) -> *mut lean_object {
        self.ptr
    }

    /// The object's ctor tag. Scalar-safe (a scalar's tag is its unboxed
    /// value, matching `lean_obj_tag` semantics).
    pub fn tag(&self) -> u32 {
        // SAFETY: ptr valid for 'a; lean_obj_tag checks is_scalar first.
        unsafe { lean_obj_tag(self.ptr) }
    }

    /// Whether this is a boxed scalar (no heap object behind it).
    pub fn is_scalar(&self) -> bool {
        lean_is_scalar(self.ptr)
    }

    /// Whether this is a heap string object.
    pub fn is_string(&self) -> bool {
        // SAFETY: scalar check first — lean_is_string derefs the header.
        !self.is_scalar() && unsafe { lean_is_string(self.ptr) }
    }

    /// Whether this is a heap scalar-array object (any element size).
    pub fn is_sarray(&self) -> bool {
        // SAFETY: scalar check first — lean_is_sarray derefs the header.
        !self.is_scalar() && unsafe { lean_is_sarray(self.ptr) }
    }

    /// Whether this is a heap constructor object.
    pub fn is_ctor(&self) -> bool {
        // SAFETY: scalar check first — lean_is_ctor derefs the header.
        !self.is_scalar() && unsafe { lean_is_ctor(self.ptr) }
    }

    /// Tag-checked constructor view.
    ///
    /// # Errors
    /// [`LeanObjectError::UnexpectedTag`] if the object's tag differs.
    pub fn as_ctor(&self, expected_tag: u32) -> Result<LeanCtorObject<'a>, LeanObjectError> {
        LeanCtorObject::new(*self, expected_tag)
    }
}

/// Tag-checked borrowed view of a constructor object. The only sanctioned
/// structure-field read off-Lean (io_result/Except tag checks; everything
/// else crosses as bytes).
#[derive(Debug, Clone, Copy)]
pub struct LeanCtorObject<'a> {
    obj: LeanObject<'a>,
}

impl<'a> LeanCtorObject<'a> {
    /// Check `obj`'s tag against `expected_tag`.
    ///
    /// # Errors
    /// [`LeanObjectError::UnexpectedTag`] on mismatch (including strings,
    /// sarrays, and other non-ctor heap objects — their tag byte simply
    /// won't match a ctor tag ≤ 240 by construction of the Lean tag space).
    pub fn new(obj: LeanObject<'a>, expected_tag: u32) -> Result<Self, LeanObjectError> {
        let actual = obj.tag();
        if actual != expected_tag {
            return Err(LeanObjectError::UnexpectedTag {
                expected: expected_tag,
                actual,
            });
        }
        Ok(Self { obj })
    }

    /// The checked tag.
    pub fn tag(&self) -> u32 {
        self.obj.tag()
    }

    /// Number of object (pointer) fields. Scalars — fieldless ctors like
    /// `none` — report 0.
    pub fn num_fields(&self) -> u32 {
        if self.obj.is_scalar() {
            return 0;
        }
        // SAFETY: tag matched a ctor tag; non-scalar + ctor tag ⇒ ctor
        // object (Lean reserves tags > LeanMaxCtorTag for non-ctor kinds).
        unsafe { lean_ctor_num_objs(self.obj.as_ptr()) }
    }

    /// Borrow field `index`. No RC traffic — the field is owned by the
    /// ctor, which outlives `'a`.
    ///
    /// # Errors
    /// [`LeanObjectError::FieldIndexOutOfBounds`] if `index` is past the
    /// object-field count.
    pub fn get(&self, index: u32) -> Result<LeanObject<'a>, LeanObjectError> {
        let num_fields = self.num_fields();
        if index >= num_fields {
            return Err(LeanObjectError::FieldIndexOutOfBounds { index, num_fields });
        }
        // SAFETY: index < num_fields on a verified ctor object.
        let field = unsafe { lean_ctor_get(self.obj.as_ptr(), index) };
        // SAFETY: borrowed field of an object that outlives 'a.
        Ok(unsafe { LeanObject::from_borrowed(field) })
    }
}

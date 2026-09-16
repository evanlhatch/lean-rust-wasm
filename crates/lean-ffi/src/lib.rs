//! # lean-ffi — the safe Lean 4.33 FFI layer over `lean-sys-v433` (W6.2)
//!
//! Pattern: cedar-lean-ffi's `lean_object.rs` (see
//! `notes/studies/cedar-study.md` "The interop verdict").
//!
//! ## Ownership discipline
//!
//! - [`OwnedLeanObject`]: Rust owns one reference count.
//!   `Drop` → `lean_dec`, `Clone` → `lean_inc`.
//! - [`LeanObject<'a>`]: borrowed reference, `PhantomData<&'a lean_object>` —
//!   no RC traffic, cannot outlive the owner it was borrowed from.
//! - [`call_export`]: Lean **steals** argument references (`mem::forget`
//!   after the call); Rust **owns** returned references.
//! - No `Send`/`Sync` on object types: single-threaded Lean objects have a
//!   non-atomic refcount; sharing across threads requires `lean_mark_mt`,
//!   which this crate deliberately does not automate.
//!
//! ## What crosses the boundary
//!
//! ONLY scalars, byte arrays (`ByteArray` ↔ `&[u8]`/`Vec<u8>`), and strings
//! (`String` ↔ `&str`/`std::string::String`). No structure-field reads
//! off-Lean beyond tag-checked ctor access ([`LeanCtorObject`]) — payloads
//! use our codec's wire format inside the byte arrays.
//!
//! ## Failure domain
//!
//! Lean panic/OOM aborts the host process (`lean_set_exit_on_panic(true)` is
//! set by [`LeanRuntime::init`]) — loud over corrupt, accepted deliberately.

pub mod marshal;
pub mod object;
pub mod runtime;

pub use marshal::{bytes_from_sarray, call_export, sarray_from_bytes, string_from, to_string, ByteArrayExport};
pub use object::{LeanCtorObject, LeanObject, LeanObjectError, OwnedLeanObject};
pub use runtime::{InitError, LeanRuntime, ThreadGuard};

// Consumers need the raw types (e.g. `lean_object`, `LeanModuleInitFn`) to
// declare their own extern exports.
pub use lean_sys_v433;

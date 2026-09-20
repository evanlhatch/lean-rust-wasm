//! The workspace's ONE global-allocator policy.
//!
//! Rust requires `#[global_allocator]` at each final binary's crate root —
//! there is no workspace-wide mechanism — so this crate centralizes the
//! POLICY (which allocator + the exact item text) and leaves each binary
//! a single line:
//!
//! ```rust
//! workspace_alloc::init_global_alloc!();
//! ```
//!
//! Rules (enforced by this design, not by convention):
//! - Binary crates depend on `workspace-alloc`, never on `mimalloc`
//!   directly (the version lives in `[workspace.dependencies]`).
//! - Library crates never call the macro: an allocator is a property of
//!   the final artifact, and two carrier crates in one graph is a hard
//!   error.
//! - The allocator marked here is mimalloc (wasmtime's own recommendation
//!   for hosts replaying many small allocations — the differential-loop
//!   shape). The WASM guest (guest-demo) is exempt by construction:
//!   mimalloc-sys has no wasm32 build, and the guest's allocation is the
//!   spliced runtime.wat allocator's territory.

/// The allocator type, re-exported so binaries never import mimalloc
/// themselves — switching allocators is a one-file change.
pub use mimalloc::MiMalloc;

/// Declare mimalloc as the crate's global allocator. Invoke at the item
/// level of a BINARY crate's root, once:
///
/// ```rust
/// workspace_alloc::init_global_alloc!();
/// ```
#[macro_export]
macro_rules! init_global_alloc {
    () => {
        #[global_allocator]
        static GLOBAL_ALLOC: $crate::MiMalloc = $crate::MiMalloc;
    };
}

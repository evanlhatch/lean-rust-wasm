//! Guest demo — the first WASM component from the schema-lang pipeline.
//! Exports simple functions to prove the component ABI works.
//!
//! Export names must match the core-module names that `wasm-tools
//! component embed` expects for the world in `guest-demo.wit`: WIT
//! kebab-case (`get-version`) maps to a core export of the same spelling,
//! hence the explicit `export_name` on otherwise-snake Rust fns.

#[unsafe(no_mangle)]
pub extern "C" fn add(a: u64, b: u64) -> u64 {
    a + b
}

#[unsafe(export_name = "get-version")]
pub extern "C" fn get_version() -> u32 {
    1
}

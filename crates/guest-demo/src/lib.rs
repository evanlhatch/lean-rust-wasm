//! Guest demo — the first WASM component from the schema-lang pipeline.
//! Exports a simple function to prove the component ABI works.

#[unsafe(no_mangle)]
pub extern "C" fn add(a: u64, b: u64) -> u64 {
    a + b
}

#[unsafe(no_mangle)]
pub extern "C" fn get_version() -> u32 {
    1
}

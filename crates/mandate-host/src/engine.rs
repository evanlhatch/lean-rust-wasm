//! The engine half: instantiate the skew-checked module and run its
//! `answer` export to the golden.
//!
//! The seed runs CORE modules (the slice is a core wasm module, not a
//! component); wasmtime's features are trimmed accordingly (see
//! Cargo.toml). Every failure is a [`crate::HostError`] — no panics on
//! real error paths (12 §8); `wasmtime::Error` is stringified (its
//! Display carries the full cause chain, and it cannot sit in a
//! `#[source]` slot — the legacy host's finding, kept).

use std::path::Path;

use wasmtime::{Config, Engine, Instance, Module, Store};

use crate::HostError;
use crate::artifact::load_gen_slice;

/// The golden: the checked module's `answer` runs to `i64 42`. This is
/// the host's CONSUMPTION of the model's fact, not a re-derivation —
/// the wasmgen validator + the Lean gates own the meaning; the host
/// refuses to run anything that produces anything else.
pub const GOLDEN_ANSWER: i64 = 42;

/// The slice's export name.
const ANSWER_EXPORT: &str = "answer";

/// Runs the exported `answer : -> i64` over raw (already
/// skew-checked) bytes and checks the golden.
pub fn run_answer(wasm: &[u8]) -> Result<i64, HostError> {
    let engine =
        Engine::new(&Config::new()).map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let module = Module::from_binary(&engine, wasm)
        .map_err(|e| HostError::Engine(format!("module compile: {e:?}")))?;

    let mut store = Store::new(&engine, ());
    let linker = wasmtime::Linker::<()>::new(&engine);
    let instance: Instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| HostError::Engine(format!("instantiate: {e:?}")))?;

    let func = instance
        .get_func(&mut store, ANSWER_EXPORT)
        .ok_or_else(|| HostError::MissingExport(ANSWER_EXPORT.to_string()))?;
    // The typed lift IS the signature check: an `answer` with any
    // other type fails here (the engine's typed refusal), not
    // mid-call.
    let typed = func.typed::<(), i64>(&store).map_err(|_| HostError::Signature)?;
    let got = typed
        .call(&mut store, ())
        .map_err(|e| HostError::Engine(format!("call {ANSWER_EXPORT}: {e:?}")))?;
    if got != GOLDEN_ANSWER {
        return Err(HostError::AnswerMismatch { got });
    }
    Ok(got)
}

/// The full startup: load the artifact set (the skew teeth fire
/// BEFORE the engine sees any bytes), then run to the golden.
pub fn run_slice(gen_dir: &Path) -> Result<i64, HostError> {
    let slice = load_gen_slice(gen_dir)?;
    run_answer(&slice.wasm)
}

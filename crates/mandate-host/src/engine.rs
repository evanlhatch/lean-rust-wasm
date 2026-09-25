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

use wasmtime::component::{Component, Instance as ComponentInstance};
use wasmtime::{Config, Engine, Instance, Module, Store};

use crate::HostError;
use crate::artifact::load_gen_slice;

// ---------------------------------------------------------------------------
// The engine skeleton (the ONE instantiation walk per lane — every
// consumer composes it, no site re-walks Engine → compile → Linker →
// instantiate by hand: the drift class the dedup wave closed)
// ---------------------------------------------------------------------------

/// The CORE lane's skeleton: the default engine, the module compiled,
/// instantiated over an empty store. A compile refusal is the typed
/// [`HostError::EngineRefused`] (the module is the consumer's
/// artifact; the engine's compiler is its second validator).
pub(crate) fn instantiate_core_module(
    wasm: &[u8],
) -> Result<(Engine, Store<()>, Instance), HostError> {
    let engine =
        Engine::new(&Config::new()).map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let module = Module::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("module compile: {e:?}")))?;
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::Linker::<()>::new(&engine);
    let instance: Instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| HostError::Engine(format!("instantiate: {e:?}")))?;
    Ok((engine, store, instance))
}

/// The COMPONENT lane's skeleton: the component-model engine, the
/// component compiled, instantiated over an empty store. A compile
/// refusal is the typed [`HostError::EngineRefused`]. Returns the
/// whole triple the consumers keep (the lifecycle holds all four
/// faces; the runners keep the engine alive for the store).
pub(crate) fn instantiate_component_module(
    wasm: &[u8],
) -> Result<(Engine, Component, Store<()>, ComponentInstance), HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine =
        Engine::new(&config).map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::component::Linker::<()>::new(&engine);
    let instance = linker
        .instantiate(&mut store, &component)
        .map_err(|e| HostError::Engine(format!("component instantiate: {e:?}")))?;
    Ok((engine, component, store, instance))
}

/// The export lookup + typed lift for a `() -> i64` core export (the
/// typed lift IS the signature check — a drifted export refuses here,
/// not mid-call).
pub(crate) fn export_i64(
    store: &mut Store<()>,
    instance: &Instance,
    name: &str,
) -> Result<wasmtime::TypedFunc<(), i64>, HostError> {
    let func = instance
        .get_func(&mut *store, name)
        .ok_or_else(|| HostError::MissingExport(name.to_string()))?;
    func.typed::<(), i64>(store).map_err(|_| HostError::Signature)
}

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
    let (_engine, mut store, instance) = instantiate_core_module(wasm)?;
    let typed = export_i64(&mut store, &instance, ANSWER_EXPORT)?;
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

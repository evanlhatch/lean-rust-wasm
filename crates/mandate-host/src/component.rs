//! The component half: the committed COMPONENT loads (the artifact
//! set skew-checked) and its guest export is called with TYPED values.
//!
//! The seed runs the component-model path (the `component-model`
//! feature): `gen/component-slice.wasm` is the component binary the
//! `componentgen` writer emitted (the LCNF-compiled guest function
//! wrapped through the canonical-ABI scalar fragment), and
//! `gen/component-slice.wit` is its world — the contract side. The
//! world is the SSOT (notes/v3/13-interfaces.md, the WIT worlds row):
//! the host checks the surface's presence + the world's export line,
//! then lets the ENGINE's typed lift carry the signature teeth — a
//! component whose export signature drifts from the world's
//! `(u64, u64) -> u64` refuses here, not mid-call.
//!
//! Every failure is a [`crate::HostError`] — no panics on real error
//! paths (12 §8); `wasmtime::Error` is stringified (its Display
//! carries the full cause chain, and it cannot sit in a `#[source]`
//! slot — the legacy host's finding, kept).

use std::path::Path;

use wasmtime::component::{Component, Linker};
use wasmtime::{Config, Engine, Store};

use crate::HostError;
use crate::artifact::bytes_hash;

/// The component binary's artifact name.
pub const COMPONENT_WASM: &str = "component-slice.wasm";

/// The world text's artifact name.
pub const COMPONENT_WIT: &str = "component-slice.wit";

/// The guest export's name (the world's contract — the fixture's
/// `add64`, the canonical-ABI scalar fragment: u64 × u64 → u64).
pub const GUEST_EXPORT: &str = "add64";

/// The string lane's artifacts (`component-string-slice.*` — the
/// canonical-ABI string lift's committed component: the world's
/// `length : func(s: string) -> u64` over the adapter-face core
/// module — the exported linear memory + the ABI realloc).
pub const STRING_WASM: &str = "component-string-slice.wasm";
pub const STRING_WIT: &str = "component-string-slice.wit";
pub const STRING_GUEST_EXPORT: &str = "length";

/// The string lane's golden: the guest's `length("hello")` answers
/// `5` — the host's CONSUMPTION of the seeded fact (the boundary
/// marshals the UTF-8 buffer; the host never runs free).
pub const STRING_GOLDEN_INPUT: &str = "hello";
pub const STRING_GOLDEN: u64 = 5;

/// The golden: the guest's `add64(2, 3)` answers `5`. This is the
/// host's CONSUMPTION of the model's fact, not a re-derivation — the
/// guest's compiled body owns the meaning; the host refuses to run
/// anything that produces anything else.
pub const GUEST_GOLDEN: u64 = 5;

/// Loads the committed component's artifact set from `gen_dir`:
///
/// 1. `component-slice.wasm` — read.
/// 2. `component-slice.wasm.hdr` — read; its `content hash <n>` must
///    equal `bytes_hash` of the component's bytes (the hash tie —
///    the SAME recurrence the toolchain's sidecar was written with).
/// 3. `component-slice.wit` — read; it must be a GENERATED artifact
///    carrying the package line, a `world` block, and the guest
///    export's contract line (the presence-level skew check; the
///    world's own byte-tie stays test-pinned in the Lean tree).
pub fn load_component(gen_dir: &Path) -> Result<Vec<u8>, HostError> {
    read_hashed_artifact(gen_dir, COMPONENT_WASM)
        .and_then(|wasm| {
            let wit = std::fs::read_to_string(gen_dir.join(COMPONENT_WIT)).map_err(|source| {
                HostError::Io { what: "component-slice.wit", source }
            })?;
            check_world_surface(&wit)?;
            Ok(wasm)
        })
}

/// The shared load skeleton: the wasm bytes + the sidecar's hash tie
/// (steps 1-2 of the discipline; the surface check is per-lane).
fn read_hashed_artifact(gen_dir: &Path, name: &str) -> Result<Vec<u8>, HostError> {
    // 1. The component bytes.
    let wasm_path = gen_dir.join(name);
    let wasm = std::fs::read(&wasm_path)
        .map_err(|source| HostError::Io { what: "component-slice.wasm", source })?;

    // 2. The sidecar — the hash tie.
    let sidecar_path = gen_dir.join(format!("{name}.hdr"));
    let sidecar = std::fs::read_to_string(&sidecar_path).map_err(|source| HostError::Io {
        what: "component-slice.wasm.hdr",
        source,
    })?;
    let declared = crate::artifact::sidecar_hash(&sidecar).ok_or(HostError::SidecarMalformed(
        "no `content hash <n>` field in the GENERATED header",
    ))?;
    let computed = bytes_hash(&wasm);
    if computed != declared {
        return Err(HostError::ContentHashMismatch { declared, computed });
    }
    Ok(wasm)
}

/// The string lane's load: the same discipline over the string
/// slice's artifact set (the hash tie + the string surface check).
pub fn load_string_component(gen_dir: &Path) -> Result<Vec<u8>, HostError> {
    read_hashed_artifact(gen_dir, STRING_WASM).and_then(|wasm| {
        let wit = std::fs::read_to_string(gen_dir.join(STRING_WIT))
            .map_err(|source| HostError::Io { what: "component-string-slice.wit", source })?;
        check_string_surface(&wit)?;
        Ok(wasm)
    })
}

/// The world surface's presence-level skew check: the GENERATED
/// header, the package line, a world block, and the guest export's
/// contract line. Each refusal is typed (`WorldSkew`), never silent.
fn check_world_surface(wit: &str) -> Result<(), HostError> {
    if !wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED")) {
        return Err(HostError::WorldSkew(
            "component-slice.wit: not a GENERATED artifact",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;")) {
        return Err(HostError::WorldSkew(
            "component-slice.wit: no `package <org>:guest;` declaration",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("world ") && l.contains('{')) {
        return Err(HostError::WorldSkew(
            "component-slice.wit: no `world <name> {` block",
        ));
    }
    if !wit
        .lines()
        .any(|l| l.contains(&format!("export {GUEST_EXPORT}: func(")))
    {
        return Err(HostError::WorldSkew(
            "component-slice.wit: no `export add64: func(` contract line",
        ));
    }
    Ok(())
}

/// The string lane's surface check: the same shape over the string
/// slice's contract — the world must carry the string export's FULL
/// line (the load-time skew check covers the composite types: a
/// surface declaring `length` with any other signature refuses
/// here, before the engine starts).
fn check_string_surface(wit: &str) -> Result<(), HostError> {
    if !wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED")) {
        return Err(HostError::WorldSkew(
            "component-string-slice.wit: not a GENERATED artifact",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;")) {
        return Err(HostError::WorldSkew(
            "component-string-slice.wit: no `package <org>:guest;` declaration",
        ));
    }
    let contract = format!("export {STRING_GUEST_EXPORT}: func(s: string) -> u64;");
    if !wit.lines().any(|l| l.contains(&contract)) {
        return Err(HostError::WorldSkew(
            "component-string-slice.wit: no `export length: func(s: string) -> u64;` contract line",
        ));
    }
    Ok(())
}

/// Runs the exported `add64 : (u64, u64) -> u64` over raw (already
/// skew-checked) component bytes with TYPED values and checks the
/// golden.
pub fn run_component(wasm: &[u8], a: u64, b: u64) -> Result<u64, HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config)
        .map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;

    let mut store = Store::new(&engine, ());
    let linker = Linker::<()>::new(&engine);
    let instance = linker
        .instantiate(&mut store, &component)
        .map_err(|e| HostError::Engine(format!("component instantiate: {e:?}")))?;

    let func = instance
        .get_func(&mut store, GUEST_EXPORT)
        .ok_or_else(|| HostError::MissingExport(GUEST_EXPORT.to_string()))?;
    // The typed lift IS the signature check: an `add64` with any other
    // component signature fails here (the engine's typed refusal), not
    // mid-call.
    let typed = func
        .typed::<(u64, u64), (u64,)>(&store)
        .map_err(|_| HostError::ComponentSignature("add64 : (u64, u64) -> u64"))?;
    let (got,) = typed
        .call(&mut store, (a, b))
        .map_err(|e| HostError::Engine(format!("call {GUEST_EXPORT}: {e:?}")))?;
    // (post-return is subsumed in this wasmtime version — the call's
    // cleanup is internal; the deprecated explicit call is not used.)
    if got != GUEST_GOLDEN {
        return Err(HostError::ComponentAnswerMismatch {
            got,
            expected: GUEST_GOLDEN,
        });
    }
    Ok(got)
}

/// Runs the string lane's committed component: the exported `length :
/// func(s: string) -> u64` over raw (already skew-checked) bytes with
/// the TYPED string call — the canonical-ABI `(ptr, len)` lowering is
/// the ENGINE's (the host lowers the UTF-8 buffer through the guest's
/// realloc + memory, the lift passes the pair to the core func), and
/// the typed lift carries the signature teeth for the composite
/// signature. The host runs to the seeded golden (`length("hello")` =
/// 5); it never runs free.
pub fn run_string_component(wasm: &[u8]) -> Result<u64, HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config)
        .map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;

    let mut store = Store::new(&engine, ());
    let linker = Linker::<()>::new(&engine);
    let instance = linker
        .instantiate(&mut store, &component)
        .map_err(|e| HostError::Engine(format!("component instantiate: {e:?}")))?;

    let func = instance
        .get_func(&mut store, STRING_GUEST_EXPORT)
        .ok_or_else(|| HostError::MissingExport(STRING_GUEST_EXPORT.to_string()))?;
    let typed = func
        .typed::<(&str,), (u64,)>(&store)
        .map_err(|_| HostError::ComponentSignature("length : func(s: string) -> u64"))?;
    let (got,) = typed
        .call(&mut store, (STRING_GOLDEN_INPUT,))
        .map_err(|e| HostError::Engine(format!("call {STRING_GUEST_EXPORT}: {e:?}")))?;
    if got != STRING_GOLDEN {
        return Err(HostError::ComponentAnswerMismatch {
            got,
            expected: STRING_GOLDEN,
        });
    }
    Ok(got)
}

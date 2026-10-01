//! The IMPORT lane: the host PROVIDES the guest's imported function —
//! the externs' OTHER half (the declared trust boundary's far side).
//!
//! The committed component (`gen/component-import-slice.wasm`) carries
//! the world's import row (`import host-add: func(a: u64, b: u64) ->
//! u64;` — the Lean SSOT's `ComponentTests.ImportFixture.importWorld`)
//! and the guest's `add64` calls it. The host's provision is the
//! LINKER's root `func_wrap` (a root-level bare func import — the
//! component-model's func import face), and the value crosses: the
//! guest's compiled call rides the canon LOWER into the core module's
//! import, the provision answers, the result rides the canon LIFT out.
//!
//! The teeth (the skew discipline's import face — three points where a
//! drift refuses):
//! 1. the import SURFACE, read from the component TYPE pre-
//!    instantiation (ground truth, never an embedded claim — the
//!    surface discipline's import face): a component importing what
//!    the provision set does not cover refuses with
//!    [`HostError::ImportUnprovisioned`] before any instantiation;
//! 2. the provision's SIGNATURE, checked by the wasmtime LINKER's
//!    typecheck at instantiate (a provision of the wrong type refuses
//!    there, never mid-call) — surfaced as
//!    [`HostError::ImportSignatureSkew`];
//! 3. the typed LIFT of the guest export (the same per-call teeth the
//!    other lanes carry).
//!
//! The MODEL side (the Lean executor's provision row — `Import.impl`,
//! the closed op the model's host answers with) is
//! `ComponentTests.ImportFixture`'s: the three-way evidence is the
//! model run ≡ the component's execution ≡ THIS wasmtime run, all to
//! the same golden.
//!
//! Every failure is a [`crate::HostError`] — no panics on real error
//! paths (12 §8).

use std::path::Path;

use wasmtime::component::{Component, Linker};
use wasmtime::{Config, Engine, Store};

use crate::HostError;

/// The import lane's artifacts (`component-import-slice.*` — the
/// import discipline's committed component: the world's
/// `import host-add: func(a: u64, b: u64) -> u64;` over the guest
/// whose `add64` calls it).
pub const IMPORT_WASM: &str = "component-import-slice.wasm";
/// The import lane's world text (the contract side).
pub const IMPORT_WIT: &str = "component-import-slice.wit";
/// The guest export's name (the world's contract).
pub const IMPORT_GUEST_EXPORT: &str = "add64";
/// THE IMPORT's name (the world's import row + the core import's ONE
/// name — the provision's key).
pub const IMPORT_NAME: &str = "host-add";

/// The import lane's golden: the guest's `add64(2, 3)` calls the
/// import; the provision answers `2 + 3`; the value crosses — the
/// host's CONSUMPTION of the model's fact (`ComponentTests.
/// ImportFixture.modelRun` is the Lean leg of the same evidence).
pub const IMPORT_GOLDEN: u64 = 5;

/// The import lane's committed call surface (the export's flat arity —
/// two u64 slots; the IMPORT's row is the provide face, checked
/// separately).
pub const EXPECTED_IMPORT_SURFACE: &str = "add64/2";

/// The import lane's committed PROVIDE surface: the component's
/// imports (name + flat arity), in declaration order — the provision
/// set must cover exactly this.
pub const EXPECTED_IMPORT_PROVIDE: &[(&str, usize)] = &[(IMPORT_NAME, 2)];

/// Loads the import lane's committed artifact set from `gen_dir` —
/// the same discipline as [`crate::component::load_component`]: the
/// wasm bytes + the sidecar's hash tie + the world text's contract
/// line (the import row's presence).
pub fn load_import_component(gen_dir: &Path) -> Result<Vec<u8>, HostError> {
    let wasm = crate::component::read_hashed_artifact(gen_dir, IMPORT_WASM)?;
    let wit =
        std::fs::read_to_string(gen_dir.join(IMPORT_WIT)).map_err(|source| HostError::Io {
            what: "component-import-slice.wit",
            source,
        })?;
    check_import_world(&wit)?;
    Ok(wasm)
}

/// The import world's presence-level skew check: the GENERATED header,
/// the package line, and BOTH contract lines (the import row + the
/// export row — the boundary's two-sided contract).
fn check_import_world(wit: &str) -> Result<(), HostError> {
    if !wit
        .lines()
        .next()
        .is_some_and(|l| l.starts_with("// GENERATED"))
    {
        return Err(HostError::WorldSkew(
            "component-import-slice.wit: not a GENERATED artifact",
        ));
    }
    if !wit
        .lines()
        .any(|l| l.starts_with("package ") && l.contains(":guest;"))
    {
        return Err(HostError::WorldSkew(
            "component-import-slice.wit: no `package <org>:guest;` declaration",
        ));
    }
    let import_row = format!("import {IMPORT_NAME}: func(a: u64, b: u64) -> u64;");
    if !wit.lines().any(|l| l.contains(&import_row)) {
        return Err(HostError::WorldSkew(
            "component-import-slice.wit: no `import host-add: func(...)` contract line",
        ));
    }
    let export_row = format!("export {IMPORT_GUEST_EXPORT}: func(a: u64, b: u64) -> u64;");
    if !wit.lines().any(|l| l.contains(&export_row)) {
        return Err(HostError::WorldSkew(
            "component-import-slice.wit: no `export add64: func(...)` contract line",
        ));
    }
    Ok(())
}

/// The import lane's PROVIDE-surface check (the fail-fast, pre-
/// instantiation — the schema-skew discipline's import face): the
/// component TYPE's imports are ground truth (`Component::
/// component_type`, read BEFORE any instantiation — a skew is never
/// run). Each expected import must be present as a FUNC whose flat
/// arity matches; an uncovered import refuses
/// ([`HostError::ImportUnprovisioned`]), a skewed arity refuses
/// ([`HostError::ImportSignatureSkew`]). Extra guest imports are out
/// of the provision contract (the wasi lane's valves are theirs).
pub fn verify_import_provision(wasm: &[u8]) -> Result<(), HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine =
        Engine::new(&config).map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;
    let ty = component.component_type();
    for (name, want_arity) in EXPECTED_IMPORT_PROVIDE {
        let mut found: Option<usize> = None;
        for (iname, item) in ty.imports(&engine) {
            if iname != *name {
                continue;
            }
            match item.ty {
                wasmtime::component::types::ComponentItem::ComponentFunc(f) => {
                    let arity: usize = f.params().map(|(_, t)| flat_arity(&t)).sum();
                    found = Some(arity);
                }
                _ => found = None,
            }
            break;
        }
        match found {
            None => {
                return Err(HostError::ImportUnprovisioned(name.to_string()));
            }
            Some(arity) if arity != *want_arity => {
                return Err(HostError::ImportSignatureSkew {
                    name: name.to_string(),
                    want: format!("{name}/{want_arity}"),
                    got: format!("{name}/{arity}"),
                });
            }
            Some(_) => {}
        }
    }
    Ok(())
}

/// The flat-arg arity of one component-ABI type (the convention: a
/// record arg rides its FIELD VALUES flat, a variant arg as
/// [discr, payload]; every leaf is one slot).
fn flat_arity(ty: &wasmtime::component::Type) -> usize {
    use wasmtime::component::Type;
    match ty {
        Type::Record(r) => r.fields().count(),
        Type::Variant(_) => 2,
        _ => 1,
    }
}

/// The honest engine: component-model on, an empty linker — the
/// UNPROVISIONED instantiate (the negative control's face).
fn engine_and_component(wasm: &[u8]) -> Result<(Engine, Component), HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine =
        Engine::new(&config).map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;
    Ok((engine, component))
}

/// Runs the import lane's committed component: the provision answers
/// `host-add` with `a + b` (the linker's root `func_wrap` — the
/// component-model's root-level bare func import), the guest's
/// `add64` calls it, and the value crosses back through the typed
/// lift. The instantiate is where the wasmtime LINKER typechecks the
/// provision's signature against the world's import row — a skewed
/// provision refuses THERE, mapped to
/// [`HostError::ImportSignatureSkew`]; a missing provision (an empty
/// linker) refuses as [`HostError::ImportUnprovisioned`]. The run
/// checks the golden — the host never runs free.
pub fn run_import_component(wasm: &[u8], a: u64, b: u64) -> Result<u64, HostError> {
    let (engine, component) = engine_and_component(wasm)?;
    let mut store = Store::new(&engine, ());
    let mut linker = Linker::<()>::new(&engine);
    // THE PROVISION (the root's func_wrap — the host's promise, the
    // same semantics the model's provision row `i64add` carries).
    linker
        .root()
        .func_wrap(
            IMPORT_NAME,
            |_s: wasmtime::StoreContextMut<'_, ()>, (x, y): (u64, u64)| {
                Ok::<_, wasmtime::Error>((x.wrapping_add(y),))
            },
        )
        .map_err(|e| HostError::Engine(format!("provision {IMPORT_NAME}: {e:?}")))?;
    let instance = linker.instantiate(&mut store, &component).map_err(|e| {
        let msg = format!("{e:?}");
        if msg.contains(IMPORT_NAME) && msg.contains("type mismatch") {
            HostError::ImportSignatureSkew {
                name: IMPORT_NAME.to_string(),
                want: format!("{IMPORT_NAME}: func(a: u64, b: u64) -> u64"),
                got: "the provision's wired signature".to_string(),
            }
        } else if msg.contains(IMPORT_NAME) || msg.contains("missing import") {
            HostError::ImportUnprovisioned(IMPORT_NAME.to_string())
        } else {
            HostError::Engine(format!("component instantiate: {msg}"))
        }
    })?;
    let func = instance
        .get_func(&mut store, IMPORT_GUEST_EXPORT)
        .ok_or_else(|| HostError::MissingExport(IMPORT_GUEST_EXPORT.to_string()))?;
    let typed = func
        .typed::<(u64, u64), (u64,)>(&store)
        .map_err(|_| HostError::ComponentSignature("add64 : (u64, u64) -> u64"))?;
    let (got,) = typed
        .call(&mut store, (a, b))
        .map_err(|e| HostError::Engine(format!("call {IMPORT_GUEST_EXPORT}: {e:?}")))?;
    if got != IMPORT_GOLDEN {
        return Err(HostError::ComponentAnswerMismatch {
            got,
            expected: IMPORT_GOLDEN,
        });
    }
    Ok(got)
}

/// THE UNPROVISIONED INSTANTIATE (the negative control's honest face):
/// an EMPTY linker — the component's import has no provider, and the
/// wasmtime instantiate REFUSES. The refusal surfaces as the TYPED
/// error [`HostError::ImportUnprovisioned`], never a panic, never a
/// silent skip; an instantiate that somehow SUCCEEDS is the engine
/// error (the tooth is gone — the tests pin the distinction).
pub fn run_import_component_unprovisioned(wasm: &[u8]) -> Result<(), HostError> {
    let (engine, component) = engine_and_component(wasm)?;
    let mut store = Store::new(&engine, ());
    let linker = Linker::<()>::new(&engine);
    match linker.instantiate(&mut store, &component) {
        Err(e) => {
            let msg = format!("{e:?}");
            if msg.contains(IMPORT_NAME) || msg.contains("import") {
                Err(HostError::ImportUnprovisioned(IMPORT_NAME.to_string()))
            } else {
                Err(HostError::Engine(format!("component instantiate: {msg}")))
            }
        }
        Ok(_) => Err(HostError::Engine(
            "the UNPROVISIONED instantiate succeeded — the import tooth is gone".to_string(),
        )),
    }
}

/// THE SKEWED PROVISION (the negative control's other face): the
/// linker provides `host-add` with the WRONG signature (`u64 ->
/// u64` — one slot, not two) — the wasmtime LINKER's typecheck
/// refuses at instantiate, mapped to
/// [`HostError::ImportSignatureSkew`].
pub fn run_import_component_skewed(wasm: &[u8]) -> Result<(), HostError> {
    let (engine, component) = engine_and_component(wasm)?;
    let mut store = Store::new(&engine, ());
    let mut linker = Linker::<()>::new(&engine);
    linker
        .root()
        .func_wrap(
            IMPORT_NAME,
            |_s: wasmtime::StoreContextMut<'_, ()>, (x,): (u64,)| Ok::<_, wasmtime::Error>((x,)),
        )
        .map_err(|e| HostError::Engine(format!("provision {IMPORT_NAME}: {e:?}")))?;
    match linker.instantiate(&mut store, &component) {
        Err(e) => {
            let msg = format!("{e:?}");
            if msg.contains("type mismatch") || msg.contains(IMPORT_NAME) {
                Err(HostError::ImportSignatureSkew {
                    name: IMPORT_NAME.to_string(),
                    want: format!("{IMPORT_NAME}: func(a: u64, b: u64) -> u64"),
                    got: format!("{IMPORT_NAME}: func(a: u64) -> u64"),
                })
            } else {
                Err(HostError::Engine(format!("component instantiate: {msg}")))
            }
        }
        Ok(_) => Err(HostError::Engine(
            "the SKEWED provision's instantiate succeeded — the skew tooth is gone".to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn committed() -> Vec<u8> {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../gen");
        std::fs::read(dir.join(IMPORT_WASM)).expect("the committed import slice")
    }

    #[test]
    fn provision_surface_checks() {
        let wasm = committed();
        verify_import_provision(&wasm).expect("the provision covers the imports");
    }

    #[test]
    fn golden_crosses() {
        let wasm = committed();
        let got = run_import_component(&wasm, 2, 3).expect("the golden");
        assert_eq!(got, IMPORT_GOLDEN);
    }
}

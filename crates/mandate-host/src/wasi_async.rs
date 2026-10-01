//! THE WASI ASYNC LANE (D4's named remainder — the async-lift protocol
//! as a session, `Machines.AsyncSession`; the runtime face this module
//! enforces).
//!
//! THE OPEN CHECK, RESOLVED (the vendored wasmtime 47.0.4 source):
//! the async-lift's task intrinsics — `[task-return]`, the
//! waitable-set faces, `context.{get,set}` — are RUNTIME-PROVIDED,
//! never Linker-provided. The component's canonical declarations
//! (`canon task-return` &c.) compile to TRAMPOLINES synthesized by
//! wasmtime's own compiler
//! (`wasmtime-internal-cranelift/src/compiler/component.rs`:
//! `Trampoline::TaskReturn`, `WaitableSet*`, `ContextGet/Set`), and
//! instantiation wires them DIRECTLY onto the component instance —
//! `runtime/component/instance.rs` `Instantiator::run`'s
//! `env_component.unsafe_intrinsics` loop calls `set_intrinsic` with
//! the compiled pointers before any initializer runs. No host linker
//! entry exists for them and none is consulted; the host provides only
//! the component TYPE's WIT-level imports (the valve's ground truth).
//! The minimal probe below (`the async export runs`) is the executable
//! half of the evidence: a guest whose core module imports
//! `[task-return]` from a `canon task-return` declaration
//! instantiates with an EMPTY linker and delivers its value.
//!
//! THE SESSION/RUNTIME AGREEMENT (the honest claim — `Machines.
//! AsyncSession` is the model, this module is the enforcement face):
//! the fixture's async export (`async func() -> u64`) delivers the
//! flat result 42 through its task-return import, then returns —
//! exactly `guestAsyncExport`'s tape (send `taskReturn 42`, send
//! `taskHandle 0`, done), whose dual the host plays by awaiting the
//! concurrent call. What the test pins: the VALUE 42 crosses the wire
//! and lands typed in the host (`TypedFunc<(), u64>`'s lift). What it
//! does NOT claim: a compiled-body ↔ session correspondence theorem —
//! the agreement is pinned at the fixture (the guest body IS the
//! tape's face), the same honesty the component lane's parity
//! discipline uses.
//!
//! THE LANE SHAPE: a SEPARATE path from the sync lane
//! (`crate::wasi::instantiate_wasi_component` — unchanged). Same valve
//! discipline (the derivation + `check_valve` fire BEFORE
//! instantiation, the load tooth), same default-deny `WasiCtx`
//! wiring, same p3 linker — the crossings differ only in CONCURRENCY:
//! `Linker::instantiate_async` + the `run_concurrent`/`Accessor`
//! discipline (the store's event loop; the concurrent call is the
//! derived dual's runtime face). `wasmtime`'s `component-model-async`
//! feature is the engine edge (it pulls `async` + the fiber
//! substrate); `Config::concurrency_support` is the runtime edge.
//!
//! No unsafe; every failure is a [`crate::HostError`] — no panics on
//! real error paths (12 §8).

use wasmtime::component::{Component, Instance as ComponentInstance};
use wasmtime::{Config, Engine, Store};

use crate::HostError;
use crate::wasi::{EffectAtom, HostWasiState, check_valve, component_imports, derive_row};

/// THE ASYNC COMPONENT LANE (the p3 face's concurrent walk): the same
/// load discipline as the sync lane — the row derived from the
/// component TYPE, the valve checked BEFORE instantiation — then the
/// `instantiate_async` entry (the async-lift's substrate: the guest's
/// async exports run as tasks on the store's event loop). The sync
/// lane is untouched; this path never enters it.
pub async fn instantiate_wasi_component_async(
    wasm: &[u8],
    allowed: &[EffectAtom],
) -> Result<(Engine, Component, Store<HostWasiState>, ComponentInstance), HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    // THE ENGINE EDGE (the p3 dep's flip, now explicit): the async
    // component-model feature — the streams/futures/task-return
    // substrate.
    config.wasm_component_model_async(true);
    // THE RUNTIME EDGE: `run_concurrent`/`call_concurrent` refuse
    // without it (wasmtime's concurrency_support check).
    config.concurrency_support(true);
    let engine =
        Engine::new(&config).map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;

    // THE VALVE — IDENTICAL to the sync lane's (the load tooth): the
    // same derivation, the same sub-row order, the same named
    // refusals. The async path adds no grant.
    let imports = component_imports(&engine, &component);
    let _required = derive_row(&imports)?;
    check_valve(&imports, allowed)?;

    // THE DEFAULT-DENY WIRING: byte-identical discipline to the sync
    // lane (the closed box; the read-only clamp; hostIO inherits
    // stdio).
    let mut wasi = crate::wasi::wasi_ctx_builder(allowed)?;

    let state = HostWasiState {
        table: wasmtime::component::ResourceTable::new(),
        wasi: wasi.build(),
    };
    let mut store = Store::new(&engine, state);
    let mut linker = wasmtime::component::Linker::<HostWasiState>::new(&engine);
    wasmtime_wasi::p3::add_to_linker(&mut linker)
        .map_err(|e| HostError::Engine(format!("wasi p3 linker: {e:?}")))?;
    let instance = linker
        .instantiate_async(&mut store, &component)
        .await
        .map_err(|e| HostError::Engine(format!("component instantiate_async: {e:?}")))?;
    Ok((engine, component, store, instance))
}

/// THE CONCURRENT CALL (the host's derived dual, at runtime): the
/// typed export called INSIDE the store's event loop —
/// `run_concurrent`'s `Accessor` discipline. The typed call's
/// evidence: the flat result the guest delivered through task-return
/// lifts to the host's `u64`.
pub async fn call_async_u64(
    mut store: Store<HostWasiState>,
    instance: &ComponentInstance,
    name: &str,
) -> Result<u64, HostError> {
    // The single-value return rides the one-tuple (the ComponentNamedList
    // bound's shape — primitives alone are not a param/result LIST).
    let f = instance
        .get_typed_func::<(), (u64,)>(&mut store, name)
        .map_err(|e| HostError::Engine(format!("export {name}: {e:?}")))?;
    // run_concurrent: Result<Result<(u64,), wasmtime::Error>, wasmtime::Error>
    // — the outer layer is the event loop's, the inner the call's.
    let value: (u64,) = store
        .run_concurrent(async |accessor| f.call_concurrent(accessor, ()).await)
        .await
        .map_err(|e| HostError::Engine(format!("concurrent call: {e:?}")))?
        .map_err(|e| HostError::Engine(format!("call_concurrent: {e:?}")))?;
    Ok(value.0)
}

//! The component runtime: store + linker + instance, capability-gated
//! WASI 0.3, fuel-bounded and epoch-interrupted execution.

use std::time::Duration;

use wasmtime::{
    Engine, Store,
    component::{Instance, Linker, ResourceTable, Type, Val},
};
use wasmtime_wasi::{DirPerms, FilePerms, WasiCtxBuilder, p3};

use crate::engine::SteelEngine;
use crate::valves::{HostFault, MissingExport, UnsupportedResult};
use crate::{CapabilitySet, HostState};

/// Errors flow as fast-observe faults over [`HostFault`].
pub type SteelResult<T> = Result<T, fast_observe::exn::Fault<HostFault>>;

/// Default fuel budget per runtime — generous, but finite.
const DEFAULT_FUEL: u64 = 10_000_000;

/// Default epoch tick — one epoch increment per tick.
const DEFAULT_EPOCH_TICK: Duration = Duration::from_millis(10);

/// Epoch interruption thread: increments the engine epoch every `interval`.
/// Daemon — never joined, dies with the process.
pub fn start_epoch_thread(engine: &Engine, interval: Duration) {
    let engine = engine.clone();
    std::thread::spawn(move || {
        loop {
            std::thread::sleep(interval);
            engine.increment_epoch();
        }
    });
}

/// A loaded, capability-scoped component runtime.
pub struct ComponentRuntime {
    engine: SteelEngine,
    store: Store<HostState>,
    linker: Linker<HostState>,
    instance: Option<Instance>,
    epoch_tick: Duration,
}

impl ComponentRuntime {
    /// Build a runtime with WASI wired according to `caps` (default-deny:
    /// [`CapabilitySet::NONE`] yields a closed box — no stdio, no fs).
    pub async fn new(engine: SteelEngine, caps: CapabilitySet) -> SteelResult<Self> {
        let mut wasi = WasiCtxBuilder::new();
        if caps.stdio() {
            wasi.inherit_stdio();
        }
        // Preopen the host root as guest `/` — read-only unless FS_WRITE.
        if caps.fs_read() {
            wasi.preopened_dir(
                ".",
                "/",
                if caps.fs_write() {
                    DirPerms::MUTATE
                } else {
                    DirPerms::READ
                },
                if caps.fs_write() {
                    FilePerms::WRITE
                } else {
                    FilePerms::READ
                },
            )
            .map_err(fault)?;
        }

        let state = HostState {
            table: ResourceTable::new(),
            wasi: wasi.build(),
            capabilities: caps,
        };
        let mut store = Store::new(engine.engine(), state);
        store.set_fuel(DEFAULT_FUEL).map_err(fault)?;

        let mut linker = Linker::new(engine.engine());
        p3::add_to_linker(&mut linker).map_err(fault)?;

        // Bounded wall-clock: trap when execution outlives one tick past
        // "now". Set before instantiation so runaway instantiation dies too.
        store.set_epoch_deadline(1);

        Ok(Self {
            engine,
            store,
            linker,
            instance: None,
            epoch_tick: DEFAULT_EPOCH_TICK,
        })
    }

    /// Instantiate: link WASI + run the component's start (if any).
    pub async fn instantiate(
        &mut self,
        component: &wasmtime::component::Component,
    ) -> SteelResult<()> {
        // One daemon epoch thread per runtime — engine-wide increments are
        // harmless to other runtimes (their deadlines are relative).
        start_epoch_thread(self.engine.engine(), self.epoch_tick);
        let instance = self
            .linker
            .instantiate_async(&mut self.store, component)
            .await
            .map_err(fault)?;
        self.instance = Some(instance);
        Ok(())
    }

    /// Call an export by name. Arguments/results flow as untyped component
    /// [`Val`]s — typed bindings come with generated worlds later.
    pub async fn call(&mut self, func: &str, args: &[Val]) -> SteelResult<Vec<Val>> {
        let Some(instance) = self.instance else {
            return Err(HostFault::NotInstantiated.into());
        };
        let Some(f) = instance.get_func(&mut self.store, func) else {
            return Err(HostFault::MissingExport(MissingExport {
                name: func.to_string(),
            })
            .into());
        };
        let mut results: Vec<Val> = f
            .ty(&self.store)
            .results()
            .map(default_val)
            .collect::<SteelResult<Vec<Val>>>()?;
        f.call_async(&mut self.store, args, &mut results)
            .await
            .map_err(fault)?;
        Ok(results)
    }

    /// Fuel remaining — burn-rate observability.
    pub fn fuel_left(&self) -> SteelResult<u64> {
        self.store.get_fuel().map_err(fault)
    }

    /// Pre-instantiate for typed (bindgen-generated) callers: the generated
    /// `XxxPre::new(store, &pre)` + `Xxx::new` path. The untyped [`call`]
    /// stays the default; this is the typed escape hatch.
    pub fn instantiate_pre(
        &mut self,
        component: &wasmtime::component::Component,
    ) -> SteelResult<wasmtime::component::InstancePre<HostState>> {
        self.linker.instantiate_pre(component).map_err(fault)
    }

    /// The store — typed callers pass it alongside the instance.
    pub fn store_mut(&mut self) -> &mut Store<HostState> {
        &mut self.store
    }
}

/// wasmtime::Error → fault. String, not `wasmtime::Error`: that type
/// deliberately does not implement `core::error::Error` (so it can't sit
/// in a `#[source]` slot), and its Display prints the full cause chain.
fn fault(e: wasmtime::Error) -> fast_observe::exn::Fault<HostFault> {
    HostFault::Engine(crate::valves::Engine {
        message: format!("{e:?}"),
    })
    .into()
}

/// Pre-fill a result slot from its component type — `call_async` wants
/// correctly-typed placeholders to lift into.
fn default_val(ty: Type) -> SteelResult<Val> {
    Ok(match ty {
        Type::Bool => Val::Bool(false),
        Type::S8 => Val::S8(0),
        Type::U8 => Val::U8(0),
        Type::S16 => Val::S16(0),
        Type::U16 => Val::U16(0),
        Type::S32 => Val::S32(0),
        Type::U32 => Val::U32(0),
        Type::S64 => Val::S64(0),
        Type::U64 => Val::U64(0),
        Type::Float32 => Val::Float32(0.0),
        Type::Float64 => Val::Float64(0.0),
        Type::Char => Val::Char('\0'),
        Type::String => Val::String(String::new()),
        other => {
            return Err(HostFault::UnsupportedResult(UnsupportedResult {
                ty: format!("{other:?}"),
            })
            .into());
        }
    })
}

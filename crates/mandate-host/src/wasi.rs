//! THE WASI P3 HOST LANE + THE CAPABILITY VALVES AS EFFECT ROWS (D3 —
//! notes/design-wave-30.md; 10 Phase 7's acceptance: "the WIT
//! capability set = the join of export rows").
//!
//! THE VALVE DISCIPLINE: the legacy `CapabilitySet` bitflags DIE here —
//! the component's required capabilities are an EFFECT ROW (the closed
//! lattice's atoms, `Effects.Basic`), derived as the FOLD JOIN over the
//! component TYPE's imports (the ground truth, read pre-instantiation —
//! the skew fail-fast's introspection face). The host's allowance is
//! itself a row; the valve is the sub-effect check (`Row.le`'s
//! decided shape): DEFAULT-DENY is the empty allowance, and a component
//! whose required row is not a sub-row of the allowance refuses at LOAD
//! — before instantiation — with the first deficient import named and
//! its missing atoms listed. An import absent from the interface table
//! (an undeclared capability) cannot even be NAMED: the derivation
//! refuses. The Lean SSOT of this shape is `Effects.Capability` (the
//! table, the fold's law `mem_deriveRow`, the valve's law
//! `valve_below`); THIS module is the Rust enforcement face, and the
//! two share the same fixtures (the mirror pins in `tests/wasi.rs`) —
//! the rendered-table lane (one emitted artifact both sides read) is
//! the named follow-up.
//!
//! THE WASI LANE: wasi 0.3 through `wasmtime_wasi::p3::add_to_linker`
//! (the linker's p3 face: cli, clocks, filesystem, random, sockets);
//! the `WasiCtx` is wired DEFAULT-DENY from the ALLOWED row (the
//! closed box is empty: no stdio, no preopens), and even an allowed
//! filesystem read lands as a READ-ONLY preopen (DirPerms/FilePerms
//! clamp — defense-in-depth under the valve, the legacy discipline
//! kept). SYNC-FIRST: the sync `Linker::instantiate` serves the sync
//! wasi interfaces (`wasi:cli/environment`'s funcs are not
//! `async func`); the async-lift's full protocol (streams/futures/
//! task-return) is the named next step. No unsafe; every failure is a
//! [`crate::HostError`] — no panics on real error paths (12 §8).

use wasmtime::component::{Component, Instance as ComponentInstance, ResourceTable};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::{DirPerms, FilePerms, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView, p3};

use crate::HostError;

// ---------------------------------------------------------------------------
// The closed atoms (the row's elements — the Rust mirror of `Effects.Effect`)
// ---------------------------------------------------------------------------

/// The closed effect atom (the Rust mirror of `Effects.Effect` — the
/// eight ctors, closed like the Lean universe: a new atom is a doctrine
/// act there and a mirror here, never a local flag).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectAtom {
    /// reads the shared state (the filesystem read face)
    Read,
    /// writes the shared state (the filesystem/stdio write face)
    Write,
    /// exercises a guest capability (the random source's nondeterminism)
    GuestCap,
    /// may report a typed failure (the exit face)
    Fail,
    /// consumes a resource (the usage accounting is the resource split's)
    Consume,
    /// reads the logical/global clock (the clocks' faces)
    Clock,
    /// crosses the host boundary (EVERY wasi interface's crossing)
    HostIo,
    /// emits an observation (the observer surface)
    Observe,
}

impl EffectAtom {
    /// The Lean ctor's spelling (the error messages name the atoms in
    /// the SSOT's vocabulary).
    pub fn render(self) -> &'static str {
        match self {
            EffectAtom::Read => "read",
            EffectAtom::Write => "write",
            EffectAtom::GuestCap => "guestCap",
            EffectAtom::Fail => "fail",
            EffectAtom::Consume => "consume",
            EffectAtom::Clock => "clock",
            EffectAtom::HostIo => "hostIO",
            EffectAtom::Observe => "observe",
        }
    }
}

/// The effect row: the finite set of atoms, as a list (the Rust mirror
/// of `Effects.Row` — the SEMANTICS is membership; duplicates inert).
pub type EffectRow = Vec<EffectAtom>;

// ---------------------------------------------------------------------------
// The interface table (the Rust mirror of `Effects.Capability.wasiRow`)
// ---------------------------------------------------------------------------

/// The WASI interface-id → effect-row mapping (the closed table's
/// mirror; the SSOT is `Effects.wasiRow` — this face ENFORCES it). An
/// interface absent from the table is `None`: not derivable, the valve
/// refuses (an unrecognized import can never be waved through by a
/// default).
pub fn wasi_row(id: &str) -> Option<EffectRow> {
    let row: &[EffectAtom] = match id {
        "wasi:cli/environment@0.3.0" => &[EffectAtom::HostIo],
        "wasi:cli/exit@0.3.0" => &[EffectAtom::Fail],
        "wasi:cli/stdin@0.3.0" => &[EffectAtom::Read, EffectAtom::HostIo],
        "wasi:cli/stdout@0.3.0" => &[EffectAtom::Write, EffectAtom::HostIo],
        "wasi:cli/stderr@0.3.0" => &[EffectAtom::Write, EffectAtom::HostIo],
        "wasi:cli/terminal-stdin@0.3.0" => &[EffectAtom::Read, EffectAtom::HostIo],
        "wasi:cli/terminal-stdout@0.3.0" => &[EffectAtom::Write, EffectAtom::HostIo],
        "wasi:cli/terminal-stderr@0.3.0" => &[EffectAtom::Write, EffectAtom::HostIo],
        "wasi:clocks/monotonic-clock@0.3.0" => &[EffectAtom::Clock, EffectAtom::HostIo],
        "wasi:clocks/system-clock@0.3.0" => &[EffectAtom::Clock, EffectAtom::HostIo],
        "wasi:clocks/timezone@0.3.0" => &[EffectAtom::Clock, EffectAtom::HostIo],
        "wasi:filesystem/types@0.3.0" => {
            &[EffectAtom::Read, EffectAtom::Write, EffectAtom::HostIo]
        }
        "wasi:filesystem/preopens@0.3.0" => &[EffectAtom::Read, EffectAtom::HostIo],
        "wasi:random/random@0.3.0" => &[EffectAtom::GuestCap, EffectAtom::HostIo],
        "wasi:random/insecure@0.3.0" => &[EffectAtom::GuestCap, EffectAtom::HostIo],
        "wasi:random/insecure-seed@0.3.0" => &[EffectAtom::GuestCap, EffectAtom::HostIo],
        "wasi:sockets/instance-network@0.3.0" => &[EffectAtom::HostIo],
        "wasi:sockets/tcp@0.3.0" => &[EffectAtom::HostIo],
        "wasi:sockets/udp@0.3.0" => &[EffectAtom::HostIo],
        "wasi:sockets/ip-name-lookup@0.3.0" => &[EffectAtom::HostIo],
        _ => return None,
    };
    Some(row.to_vec())
}

/// THE DERIVATION: the required capability row as the FOLD JOIN over
/// the world's import list (the join discipline — the set IS the
/// rows' join, `Effects.mem_deriveRow`). An import outside the table
/// refuses: the valve's undeclared-capability tooth.
pub fn derive_row(imports: &[String]) -> Result<EffectRow, HostError> {
    let mut row: EffectRow = Vec::new();
    for id in imports {
        let atoms = wasi_row(id)
            .ok_or_else(|| HostError::CapabilityUndeclared(id.clone()))?;
        for a in atoms {
            if !row.contains(&a) {
                row.push(a);
            }
        }
    }
    Ok(row)
}

/// The sub-effect check (the valve's decided order — `Row.le`'s face):
/// the allowance permits everything the required row does.
pub fn row_le(required: &[EffectAtom], allowed: &[EffectAtom]) -> bool {
    required.iter().all(|a| allowed.contains(a))
}

/// The component TYPE's import names (the ground truth, read
/// pre-instantiation — no instantiation, no run).
pub fn component_imports(engine: &Engine, component: &Component) -> Vec<String> {
    component
        .component_type()
        .imports(engine)
        .map(|(name, _)| name.to_string())
        .collect()
}

/// THE VALVE (the load tooth): every import's row must be a sub-row of
/// the allowance — the FIRST deficient import is named with its missing
/// atoms, and the component never reaches instantiation. The
/// derivation's undeclared tooth has already fired (an unknown import
/// is a [`HostError::CapabilityUndeclared`], not a silent skip).
fn check_valve(imports: &[String], allowed: &[EffectAtom]) -> Result<(), HostError> {
    for id in imports {
        let atoms =
            wasi_row(id).ok_or_else(|| HostError::CapabilityUndeclared(id.clone()))?;
        let missing: Vec<&str> = atoms
            .iter()
            .filter(|a| !allowed.contains(a))
            .map(|a| a.render())
            .collect();
        if !missing.is_empty() {
            return Err(HostError::CapabilityDenied {
                import: id.clone(),
                missing: missing.join(","),
            });
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The WASI lane (the p3 face; the sync-first discipline)
// ---------------------------------------------------------------------------

/// The WASI store's state: the resource table + the capability-scoped
/// ctx (the p3 host's `WasiView` — `p3::add_to_linker`'s bound).
pub struct HostWasiState {
    /// The host's resource table (the p3 face's resources ride it).
    pub table: ResourceTable,
    /// The capability-scoped WASI context (default-deny wiring below).
    pub wasi: WasiCtx,
}

impl WasiView for HostWasiState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView { ctx: &mut self.wasi, table: &mut self.table }
    }
}

/// THE WASI COMPONENT LANE (the p3 face's skeleton): the component
/// compiled, its required capability row DERIVED from its type's
/// imports, the valve CHECKED against the allowance, then the
/// default-deny `WasiCtx` wired and the p3 linker served. A refused
/// capability never reaches instantiation (the load tooth); a granted
/// one rides the sync `Linker::instantiate` (the sync-first discipline).
pub fn instantiate_wasi_component(
    wasm: &[u8],
    allowed: &[EffectAtom],
) -> Result<(Engine, Component, Store<HostWasiState>, ComponentInstance), HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    // The p3 face's ENGINE edge: wasmtime-wasi's p3 feature flips
    // wasmtime's component-model-async (the streams/futures lift's
    // substrate). This lane's walk stays SYNC (the sync-first
    // discipline: `Linker::instantiate`, never `instantiate_async`) —
    // the async-lift's full protocol is the named next step.
    config.wasm_component_model_async(true);
    let engine =
        Engine::new(&config).map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;

    // THE VALVE: derive the required row from the component TYPE (the
    // ground truth), then check the allowance — BEFORE instantiation.
    let imports = component_imports(&engine, &component);
    let _required = derive_row(&imports)?;
    check_valve(&imports, allowed)?;

    // THE DEFAULT-DENY WIRING: the allowance shapes the ctx — the
    // closed box is empty (no stdio, no preopens); a filesystem read
    // lands READ-ONLY (the DirPerms/FilePerms clamp; write widens it —
    // defense-in-depth UNDER the valve, never instead of it).
    let mut wasi = WasiCtxBuilder::new();
    let read = allowed.contains(&EffectAtom::Read);
    let write = allowed.contains(&EffectAtom::Write);
    if read {
        wasi.preopened_dir(
            ".",
            "/",
            if write { DirPerms::MUTATE } else { DirPerms::READ },
            if write { FilePerms::WRITE } else { FilePerms::READ },
        )
        .map_err(|e| HostError::Engine(format!("wasi preopen: {e:?}")))?;
    }
    if allowed.contains(&EffectAtom::HostIo) {
        wasi.inherit_stdio();
    }

    let state = HostWasiState { table: ResourceTable::new(), wasi: wasi.build() };
    let mut store = Store::new(&engine, state);
    let mut linker = wasmtime::component::Linker::<HostWasiState>::new(&engine);
    p3::add_to_linker(&mut linker)
        .map_err(|e| HostError::Engine(format!("wasi p3 linker: {e:?}")))?;
    let instance = linker
        .instantiate(&mut store, &component)
        .map_err(|e| HostError::Engine(format!("component instantiate: {e:?}")))?;
    Ok((engine, component, store, instance))
}

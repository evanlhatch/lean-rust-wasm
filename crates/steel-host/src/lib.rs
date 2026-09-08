//! steel-host — the wasmtime component embedder.
//!
//! Loads WASM components, provides WASI 0.3 capabilities, runs them
//! with bounded resources (epoch interruption + fuel metering).
//!
//! WASI note: the wasip3 guest links `wasi:cli@0.3.0` (streams/futures),
//! which needs wasmtime-wasi's `p3` implementation (wasmtime 47+). The
//! wasmtime-28-era `WasiView` (separate `table`/`ctx` accessors) is gone —
//! wasmtime 47's `WasiView` is a single `ctx()` accessor yielding
//! [`wasmtime_wasi::WasiCtxView`].

// error! emits Error::provide — nightly-only (same gate as the root crate).
#![feature(error_generic_member_access)]

use wasmtime::component::ResourceTable;
use wasmtime_wasi::{WasiCtx, WasiCtxView, WasiView};

pub mod bindings;
pub mod engine;
pub mod runtime;
pub mod valves;

pub use engine::SteelEngine;
pub use runtime::{ComponentRuntime, SteelResult, start_epoch_thread};
pub use valves::HostFault;

/// The host state: WASI context + resource table + capability set.
pub struct HostState {
    table: ResourceTable,
    wasi: WasiCtx,
    capabilities: CapabilitySet,
}

// wasmtime 47 collapsed the old four-accessor WasiView into one method —
// ctx and table travel together in WasiCtxView.
impl WasiView for HostState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.wasi,
            table: &mut self.table,
        }
    }
}

impl HostState {
    /// Capability set this state was built with.
    pub fn capabilities(&self) -> &CapabilitySet {
        &self.capabilities
    }
}

/// Default-deny capability set (pico-host pattern).
///
/// Bits are powers of two so [`CapabilitySet::union`] composes and
/// [`CapabilitySet::contains`] tests subsets.
///
/// STDIO/FS gate what the [`WasiCtxBuilder`](wasmtime_wasi::WasiCtxBuilder)
/// actually wires up (no capability, no preopened dir, no inherited stdio).
/// CLOCK/RANDOM are recorded but the wasi 0.3 host currently provides both
/// unconditionally — the bits are the policy ledger until wasmtime-wasi
/// grows per-interface gating.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapabilitySet {
    bits: u64,
}

impl CapabilitySet {
    /// No capabilities — guest gets a closed box.
    pub const NONE: Self = Self { bits: 0 };
    /// Inherit stdin/stdout/stderr.
    pub const STDIO: Self = Self { bits: 1 };
    /// Read access to the preopened host root (guest path `/`).
    pub const FS_READ: Self = Self { bits: 2 };
    /// Mutate access to the preopened host root (implies read).
    pub const FS_WRITE: Self = Self { bits: 4 };
    /// `wasi:clocks` interfaces.
    pub const CLOCK: Self = Self { bits: 8 };
    /// `wasi:random` interfaces.
    pub const RANDOM: Self = Self { bits: 16 };

    /// All bits set.
    pub const ALL: Self = Self::STDIO
        .union(Self::FS_READ)
        .union(Self::FS_WRITE)
        .union(Self::CLOCK)
        .union(Self::RANDOM);

    /// Every bit in `other` is granted here.
    pub const fn contains(&self, other: Self) -> bool {
        self.bits & other.bits == other.bits
    }

    /// Grant union of both sets.
    pub const fn union(&self, other: Self) -> Self {
        Self {
            bits: self.bits | other.bits,
        }
    }

    /// Read preopened dir? (write implies read)
    pub fn fs_read(&self) -> bool {
        self.contains(Self::FS_READ) || self.contains(Self::FS_WRITE)
    }

    /// Mutate preopened dir?
    pub fn fs_write(&self) -> bool {
        self.contains(Self::FS_WRITE)
    }

    /// Inherit host stdio?
    pub fn stdio(&self) -> bool {
        self.contains(Self::STDIO)
    }
}

impl Default for CapabilitySet {
    fn default() -> Self {
        Self::NONE
    }
}

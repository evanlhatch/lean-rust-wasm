//! Engine construction: one [`SteelEngine`] per process, shared across
//! runtimes. Bounded resources live here (pooling allocator); per-execution
//! bounds (fuel, epoch) live in [`Store`](wasmtime::Store).

use std::path::Path;

use wasmtime::{Config, Engine, component::Component};

/// Compiled engine wrapper — pooling allocator, fuel + epoch interruption.
/// Component-model async is on by default in wasmtime 47 (`CM_ASYNC`).
pub struct SteelEngine {
    engine: Engine,
}

impl SteelEngine {
    /// Build the engine. Pooling allocator: fixed memory footprint per
    /// instance (16 MiB), ready for multi-tenant reuse.
    pub fn new() -> wasmtime::Result<Self> {
        let mut config = Config::new();
        config.epoch_interruption(true);
        // Fuel metering bounds total execution; epoch interruption bounds
        // wall-clock (fuel misses blocking host calls).
        config.consume_fuel(true);

        let mut pooling = wasmtime::PoolingAllocationConfig::new();
        pooling.total_memories(64);
        pooling.total_tables(64);
        pooling.total_stacks(64);
        pooling.total_component_instances(64);
        pooling.total_core_instances(64);
        pooling.max_memories_per_module(1);
        pooling.max_tables_per_module(1);
        pooling.max_memory_size(16 * 1024 * 1024); // 16 MiB per instance
        pooling.table_elements(10_000);
        config.allocation_strategy(wasmtime::InstanceAllocationStrategy::Pooling(pooling));

        let engine = Engine::new(&config)?;
        Ok(Self { engine })
    }

    /// Compile a component from disk.
    pub fn load_component(&self, path: &Path) -> wasmtime::Result<Component> {
        Component::from_file(&self.engine, path)
    }

    /// Compile a component from an in-memory binary (or WAT in tests).
    pub fn load_component_bytes(&self, bytes: &[u8]) -> wasmtime::Result<Component> {
        Component::new(&self.engine, bytes)
    }

    /// Underlying engine — for the epoch thread and typed linking.
    pub fn engine(&self) -> &Engine {
        &self.engine
    }
}

impl Clone for SteelEngine {
    fn clone(&self) -> Self {
        Self {
            engine: self.engine.clone(),
        }
    }
}

impl std::fmt::Debug for SteelEngine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SteelEngine")
    }
}

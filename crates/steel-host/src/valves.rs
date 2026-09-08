//! Capability-denial faults — fast-observe is the error tool; engine
//! plumbing errors flow through the boxed [`HostFault::Engine`] variant.

use fast_observe::error;

error! {
    /// A capability or export the host cannot grant/serve.
    pub enum HostFault {
        /// [`ComponentRuntime::call`](crate::ComponentRuntime::call) before
        /// [`instantiate`](crate::ComponentRuntime::instantiate).
        #[error("component not instantiated")]
        #[code = "E110", category = Invariant, advice = "call instantiate() before call()"]
        NotInstantiated,
        /// Export name not in the component's world.
        #[error("missing export: {name}")]
        #[code = "E111", category = Content, advice = "check the component world exports (wasm-tools component wit)"]
        MissingExport {
            /// The export name that wasn't there.
            name: String,
        },
        /// Component call returned a type `call()` cannot pre-fill.
        #[error("unsupported result type: {ty}")]
        #[code = "E112", category = Invariant, advice = "return a scalar or handle it via typed bindings"]
        UnsupportedResult {
            /// Debug spelling of the offending type.
            ty: String,
        },
        /// Engine plumbing failure (compile, instantiate, fuel, trap).
        /// String, not `wasmtime::Error`: that type deliberately does not
        /// implement `core::error::Error` (which `#[from]`/`#[source]`
        /// need), and its Display already prints the full cause chain.
        #[error("engine: {0}")]
        #[code = "E113", category = Transient, advice = "inspect the chained wasmtime error text"]
        Engine(String),
    }
}

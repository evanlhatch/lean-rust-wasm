//! Guest demo — the first WASM component from the schema-lang pipeline.
//! Exports simple functions to prove the component ABI works.
//!
//! Export names must match the core-module names that `wasm-tools
//! component embed` expects for the world in `guest-demo.wit`: WIT
//! kebab-case (`get-version`) maps to a core export of the same spelling,
//! hence the explicit `export_name` on otherwise-snake Rust fns.

#[unsafe(no_mangle)]
pub extern "C" fn add(a: u64, b: u64) -> u64 {
    a + b
}

#[unsafe(export_name = "get-version")]
pub extern "C" fn get_version() -> u32 {
    1
}

// ── Gateway world (GENERATED wit/gateway.wit — the schema SSOT) ─────
// Typed guest bindings: the export signatures come from the Lean-defined
// world, not hand-written glue. wit-bindgen lifts kebab `get-user` to
// `get_user` and embeds the component-type section into the core module.

wit_bindgen::generate!({
    path: "../../wit/gateway.wit",
    world: "gateway",
    // The WIT emitter emits `async func` for `Async.Future` returns (wasi 0.3
    // async ABI) — watch-orders binds as a plain Rust async fn. No filter
    // needed: async function TYPES are always lifted async.
});

use crate::demo::gateway::gateway_types::{OrderError, User};
use crate::exports::demo::gateway::gateway_exports::Guest;

struct GatewayGuest;

impl Guest for GatewayGuest {
    /// get-user: the schema's `getUser (_id : UInt64) : Option User`.
    /// Body is demo data — the SIGNATURE is the contract.
    fn get_user(id: u64) -> Option<User> {
        if id == 42 {
            Some(User {
                id: 42,
                name: "Ada".to_string(),
                email: "ada@example.com".to_string(),
                tags: vec!["admin".to_string()],
            })
        } else {
            None
        }
    }

    /// watch-orders: `watchOrders (_into : OrderError) : Async.Future (List User)`
    /// → WIT `async func(into: order-error) -> list<user>` — the wasi 0.3
    /// async ABI. wit-bindgen drives the task system; the value is returned
    /// when the host awaits the call.
    async fn watch_orders(_into: OrderError) -> Vec<User> {
        vec![User {
            id: 7,
            name: "Grace".to_string(),
            email: "grace@example.com".to_string(),
            tags: vec![],
        }]
    }
}

export!(GatewayGuest);

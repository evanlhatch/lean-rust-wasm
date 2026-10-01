//! THE WASI ASYNC LANE'S TEETH (D4's named remainder — the async-lift
//! protocol as a session, `Machines.AsyncSession`; the runtime face is
//! `mandate_host::wasi_async`).
//!
//! - THE VALUE-42 CROSSING: the fixture's async export
//!   (`async func() -> u64`) delivers the flat result 42 through its
//!   `[task-return]` import and returns — exactly `guestAsyncExport`'s
//!   tape (send `taskReturn 42`, send `taskHandle 0`, done). The host
//!   awaits the concurrent call (the derived dual) and the value lands
//!   TYPED (`TypedFunc<(), (u64,)>`'s lift). The honest claim: the
//!   session/runtime agreement is PINNED at this fixture (the guest
//!   body IS the tape's face; the same 42 the Lean fixture pins), not
//!   proved as a compiled-body correspondence theorem.
//! - THE ASYNCNESS-MISMATCH REFUSAL: `(async)` on a SYNC func type's
//!   lift refuses at COMPILE (wasmparser's `check_asyncness` — "the
//!   `async` canonical option requires an async function type"), never
//!   a silent sync lift.
//! - THE VALVE'S DEFAULT-DENY ON THE ASYNC PATH: the same derivation +
//!   `check_valve` fire BEFORE `instantiate_async` — a WASI import
//!   against the empty allowance refuses with the import + missing
//!   atoms named, and instantiation is never reached.
//! - THE INTRINSIC ANSWER (the open check, executable half): the
//!   fixture's core module imports `[export]$root`/`[task-return]f`
//!   and the component wires it to a `canon task.return` declaration —
//!   the RUNTIME provides the trampoline (wasmtime's synthesized
//!   libcall, wired by `set_intrinsic` at instantiation; the module
//!   doc in `wasi_async` carries the source evidence). NO linker entry
//!   exists or is consulted for it; the fixture instantiates against
//!   the EMPTY allowance (zero WIT-level imports).
//!
//! THE FIXTURE SHAPE mirrors wit-component's own async-export test
//! component (wit-component-0.258.0 tests/components/
//! link-lib-with-async-export): the canonical-lift WITH the callback
//! face (`[async-lift]f` body + `[callback][async-lift]f` = the
//! constant Exit 0 — the legacy recipe's (c); the callbackless lift is
//! the stackful feature, a different lane), the task-return delivered
//! as the flat u64 (one i64), the body returning 0 = done at the first
//! poll.

use mandate_host::{EffectAtom, HostError, call_async_u64, instantiate_wasi_component_async};
use wasmtime::{Config, Engine};

/// THE ASYNC FIXTURE (the session model's runtime face).
const ASYNC_FUTURE_COMPONENT: &str = r#"
(component
  (type $ft (func async (result u64)))
  (core func $tr (canon task.return (result u64)))
  (core module $m
    (type $ttr (func (param i64)))
    (type $tbody (func (result i32)))
    (type $tcb (func (param i32 i32 i32) (result i32)))
    (import "[export]$root" "[task-return]f" (func $task-return (type $ttr)))
    (func $body (type $tbody)
      (call $task-return (i64.const 42))
      (i32.const 0))
    (func $cb (type $tcb)
      (i32.const 0))
    (export "body" (func $body))
    (export "cb" (func $cb)))
  (core instance $root (export "[task-return]f" (func $tr)))
  (core instance $i (instantiate $m (with "[export]$root" (instance $root))))
  (alias core export $i "body" (core func $body))
  (alias core export $i "cb" (core func $cb))
  (func $f (type $ft) (canon lift (core func $body) async (callback $cb)))
  (export "f" (func $f))
)
"#;

/// THE ASYNCNESS-MISMATCH FIXTURE: the same shape, but the lifted func
/// type is SYNC (`func (result u64)`) while the lift carries the async
/// option — the canonical option requires an async function type (the
/// compile tooth).
const ASYNCNESS_MISMATCH_COMPONENT: &str = r#"
(component
  (type $ft (func (result u64)))
  (core func $tr (canon task.return (result u64)))
  (core module $m
    (type $ttr (func (param i64)))
    (type $tbody (func (result i32)))
    (type $tcb (func (param i32 i32 i32) (result i32)))
    (import "[export]$root" "[task-return]f" (func $task-return (type $ttr)))
    (func $body (type $tbody)
      (call $task-return (i64.const 42))
      (i32.const 0))
    (func $cb (type $tcb)
      (i32.const 0))
    (export "body" (func $body))
    (export "cb" (func $cb)))
  (core instance $root (export "[task-return]f" (func $tr)))
  (core instance $i (instantiate $m (with "[export]$root" (instance $root))))
  (alias core export $i "body" (core func $body))
  (alias core export $i "cb" (core func $cb))
  (func $f (type $ft) (canon lift (core func $body) async (callback $cb)))
  (export "f" (func $f))
)
"#;

/// THE VALVE FIXTURE (the async path): an async export PLUS a
/// `wasi:cli/environment@0.3.0` import — the valve's row is over the
/// WHOLE component type, async or sync.
const ASYNC_WASI_COMPONENT: &str = r#"
(component
  (import "wasi:cli/environment@0.3.0" (instance $env
    (export "get-environment" (func (result (list (tuple string string)))))
    (export "get-arguments" (func (result (list string))))
    (export "get-initial-cwd" (func (result (option string))))
  ))
  (type $ft (func async (result u64)))
  (core func $tr (canon task.return (result u64)))
  (core module $m
    (type $ttr (func (param i64)))
    (type $tbody (func (result i32)))
    (type $tcb (func (param i32 i32 i32) (result i32)))
    (import "[export]$root" "[task-return]f" (func $task-return (type $ttr)))
    (func $body (type $tbody)
      (call $task-return (i64.const 42))
      (i32.const 0))
    (func $cb (type $tcb)
      (i32.const 0))
    (export "body" (func $body))
    (export "cb" (func $cb)))
  (core instance $root (export "[task-return]f" (func $tr)))
  (core instance $i (instantiate $m (with "[export]$root" (instance $root))))
  (alias core export $i "body" (core func $body))
  (alias core export $i "cb" (core func $cb))
  (func $f (type $ft) (canon lift (core func $body) async (callback $cb)))
  (export "f" (func $f))
)
"#;

fn component_bytes(wat: &str) -> Vec<u8> {
    wat::parse_str(wat).expect("fixture wat parses")
}

// ---------------------------------------------------------------------------
// THE VALUE-42 CROSSING (the future face — the session/runtime agreement)
// ---------------------------------------------------------------------------

#[test]
fn async_future_value_crosses() {
    let wasm = component_bytes(ASYNC_FUTURE_COMPONENT);
    // The empty allowance: the fixture imports NOTHING at the WIT level
    // (the task intrinsics are runtime-provided — the open check's
    // executable half; instantiation succeeds against the closed box).
    let value = futures::executor::block_on(async {
        let (_engine, _component, store, instance) = instantiate_wasi_component_async(&wasm, &[])
            .await
            .expect("the async component instantiates");
        call_async_u64(store, &instance, "f")
            .await
            .expect("the concurrent call completes")
    });
    assert_eq!(
        value, 42,
        "the future's value crosses (the pinned 42 — \
        Machines.AsyncSession's taskReturn 42, the Lean fixture's hostGolden)"
    );
}

// ---------------------------------------------------------------------------
// THE ASYNCNESS-MISMATCH REFUSAL (the mis-shaped async export refuses)
// ---------------------------------------------------------------------------

#[test]
fn async_option_on_sync_func_type_refuses_at_compile() {
    let wasm = component_bytes(ASYNCNESS_MISMATCH_COMPONENT);
    let verdict = futures::executor::block_on(instantiate_wasi_component_async(&wasm, &[]));
    match verdict {
        Err(HostError::EngineRefused(why)) => {
            assert!(
                why.contains("async"),
                "the refusal must name the asyncness mismatch: {why}"
            );
        }
        Err(other) => panic!("expected EngineRefused, got {other:?}"),
        Ok(_) => panic!("expected a compile refusal, the component ran"),
    }
}

// ---------------------------------------------------------------------------
// THE VALVE'S DEFAULT-DENY ON THE ASYNC PATH (the load tooth holds)
// ---------------------------------------------------------------------------

#[test]
fn async_path_default_deny_refuses_at_load() {
    let wasm = component_bytes(ASYNC_WASI_COMPONENT);
    let verdict = futures::executor::block_on(instantiate_wasi_component_async(&wasm, &[]));
    match verdict {
        Err(HostError::CapabilityDenied { import, missing }) => {
            assert_eq!(import, "wasi:cli/environment@0.3.0");
            assert_eq!(missing, "hostIO");
        }
        Err(other) => panic!("expected CapabilityDenied, got {other:?}"),
        Ok(_) => panic!("expected a load refusal, the component ran"),
    }
}

/// The GRANTED face: the same component with `hostIO` allowed
/// instantiates through the async lane (the valve is the only gate —
/// the async path adds no grant and no refusal).
#[test]
fn async_path_granted_allowance_instantiates() {
    let wasm = component_bytes(ASYNC_WASI_COMPONENT);
    let (_e, _c, _s, _i) = futures::executor::block_on(instantiate_wasi_component_async(
        &wasm,
        &[EffectAtom::HostIo],
    ))
    .expect("the granted capability instantiates through the async lane");
}

// ---------------------------------------------------------------------------
// THE SYNC LANE'S REGRESSION PIN (the two lanes stay separate)
// ---------------------------------------------------------------------------

#[test]
fn sync_lane_untouched_by_the_async_edge() {
    // The sync lane's entry still compiles + runs against the SAME
    // engine config family (its own suite in tests/wasi.rs is the full
    // battery; this pin is the coexistence face inside THIS suite).
    let wasm = component_bytes(ASYNC_FUTURE_COMPONENT);
    let mut config = Config::new();
    config.wasm_component_model(true);
    config.wasm_component_model_async(true);
    let engine = Engine::new(&config).expect("engine");
    let component = wasmtime::component::Component::from_binary(&engine, &wasm)
        .expect("the async fixture compiles under the sync lane's config too");
    // The lift itself is load-time-valid under the sync config; the
    // lane boundary is the WALK (the sync lane never calls the async
    // export), not the compile.
    assert!(mandate_host::component_imports(&engine, &component).is_empty());
}

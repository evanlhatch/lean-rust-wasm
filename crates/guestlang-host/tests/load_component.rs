//! Loads the real guest component, instantiates, calls exports.
// tokio::test's generated harness calls Result::expect on Result-returning
// test bodies — the disallowed-method hit is macro codegen, not test code.
#![allow(
    clippy::disallowed_methods,
    reason = "tokio::test codegen, not our code"
)]

mod common;

use common::demo_component_path;
use common::gateway_component_path;
use common::guest_demo_component_path;
use common::instantiate;
use common::try_load;
use common::user_val;
use common::wasip3_guest_path;
use guestlang_host::CapabilitySet;
use guestlang_host::ComponentRuntime;
use guestlang_host::HostEngine;
use wasmtime::component::Val;

/// Inline WAT component: same world as the guest — proves the call
/// plumbing (lift + Val lift/lower) independent of the toolchain build.
const ADDER_WAT: &str = r#"
(component
  (core module $m
    (func (export "add") (param i64 i64) (result i64)
      (i64.add (local.get 0) (local.get 1))))
  (core instance $i (instantiate $m))
  (func (export "add") (param "a" u64) (param "b" u64) (result u64)
    (canon lift (core func $i "add"))))
"#;

#[tokio::test]
async fn wat_component_add_1_2_is_3() -> Result<(), Box<dyn std::error::Error>> {
    let engine = HostEngine::new()?;
    let component = engine.load_component_bytes(ADDER_WAT.as_bytes())?;

    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    let results = rt.call("add", &[Val::U64(1), Val::U64(2)]).await?;
    assert_eq!(results.len(), 1);
    let Val::U64(sum) = &results[0] else {
        panic!("expected u64 result, got {:?}", results[0]);
    };
    assert_eq!(*sum, 3);
    Ok(())
}

#[tokio::test]
async fn guest_demo_component_exports_call_through() -> Result<(), Box<dyn std::error::Error>> {
    let Some((engine, component)) = try_load(
        &guest_demo_component_path(),
        &format!(
            "skipping: run `just wasm-guest-component` to build {:?}",
            guest_demo_component_path()
        ),
    )?
    else {
        return Ok(());
    };

    // Guest touches no WASI — closed box must still instantiate.
    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    let results = rt.call("add", &[Val::U64(1), Val::U64(2)]).await?;
    assert_eq!(results, vec![Val::U64(3)]);

    let results = rt.call("get-version", &[]).await?;
    assert_eq!(results, vec![Val::U32(1)]);

    // Fuel was metered: some burned, most left.
    let left = rt.fuel_left()?;
    assert!(left > 0 && left < 10_000_000, "fuel: {left}");
    Ok(())
}

#[tokio::test]
async fn wasip3_artifact_instantiates_on_wasi_03_host() -> Result<(), Box<dyn std::error::Error>> {
    let Some((engine, component)) = try_load(
        &wasip3_guest_path(),
        &format!(
            "skipping: run `just wasm-guest` to build {:?}",
            wasip3_guest_path()
        ),
    )?
    else {
        return Ok(());
    };

    // The wasip3 std component imports wasi:cli/clocks/filesystem@0.3.0 —
    // instantiation proves the p3 host satisfies the world.
    let caps = CapabilitySet::STDIO.union(CapabilitySet::FS_READ);
    let mut rt = instantiate(&engine, &component, caps).await?;

    // Zero component-level exports on this artifact (core-only exports);
    // a missing export is a clean fault, not a trap.
    let err = rt
        .call("add", &[Val::U64(1), Val::U64(2)])
        .await
        .unwrap_err();
    assert!(err.to_string().contains("missing export: add"), "{err}");
    Ok(())
}

#[tokio::test]
async fn missing_export_faults_cleanly() -> Result<(), Box<dyn std::error::Error>> {
    let engine = HostEngine::new()?;
    let component = engine.load_component_bytes(ADDER_WAT.as_bytes())?;
    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    let err = rt.call("nope", &[]).await.unwrap_err();
    assert!(err.to_string().contains("missing export: nope"), "{err}");
    Ok(())
}

/// The gateway component (world `demo:gateway/gateway`, GENERATED
/// wit/gateway.wit), instantiated through the TYPED bindgen path —
/// `get-user` returns a structured `User`, not raw `Val`s. This is the
/// "Lean defines the ABI" proof: the host's API is generated from the
/// Lean-defined world.
#[tokio::test]
async fn gateway_typed_get_user_returns_structured_user() -> Result<(), Box<dyn std::error::Error>>
{
    use guestlang_host::bindings::GatewayPre;
    use guestlang_host::bindings::GatewayUser;

    let Some((engine, component)) = try_load(
        &gateway_component_path(),
        &format!(
            "skipping: build with `just wasm-guest-gateway` for {:?}",
            gateway_component_path()
        ),
    )?
    else {
        return Ok(());
    };

    let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
    let pre = rt.instantiate_pre(&component)?;
    let gw = GatewayPre::new(pre)?
        .instantiate_async(rt.store_mut())
        .await?;
    let iface = gw.demo_gateway_gateway_exports();

    // Miss: unknown id → none.
    let missing = iface.call_get_user(rt.store_mut(), 1)?;
    assert!(missing.is_none());

    // Hit: id 42 → the structured user from the guest, via the Lean schema.
    let user: GatewayUser = iface.call_get_user(rt.store_mut(), 42)?.expect("user 42");
    assert_eq!(user.id, 42);
    assert_eq!(user.name, "Ada");
    assert_eq!(user.tags, vec!["admin".to_string()]);
    Ok(())
}

/// THE VALIDATOR-AT-THE-BOUNDARY pattern: the host consults the schema's
/// COMPILED validator (`user-complete` — the Lean-authored invariant
/// over the user schema, shipped inside the guest) BEFORE the
/// processing call (`get-user`). The invalid record → the validator's
/// false → the host REFUSES to process (the processing call is never
/// made — the refusal is OBSERVED via the gate counter, not assumed);
/// the valid record → the gate passes → the processing call runs. The
/// validator is the SPEC's code: the host adds no policy, it only
/// enforces the gate the schema declares.
#[tokio::test]
async fn the_validator_gates_the_processing_call() -> Result<(), Box<dyn std::error::Error>> {
    let Some((engine, component)) = try_load(
        &demo_component_path(),
        &format!(
            "skipping: run `just wasm-compile` to build {:?}",
            demo_component_path()
        ),
    )?
    else {
        return Ok(());
    };
    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    // the record arg = the flat field values (the duel's convention:
    // the validator's subject crosses the boundary as the record)
    let mut processed = 0usize;
    let mut refused = 0usize;
    for (user, id) in [
        // the INVALID user: id 0 → the validator refuses → NO
        // processing call (the gate's else branch)
        (user_val(0, "zero", "0@g.dev", &["a"]), 0u64),
        // the VALID user: every gate passes → the processing call runs
        (user_val(5, "first", "5@g.dev", &["a", "b"]), 5),
    ] {
        let verdict = rt.call("user-complete", &[user]).await?;
        assert_eq!(verdict.len(), 1);
        let Val::Bool(gate) = &verdict[0] else {
            panic!("the validator must return a bool, got {:?}", verdict[0]);
        };
        if *gate {
            // the gate OPEN: the host proceeds to the processing call
            let r = rt.call("get-user", &[Val::U64(id)]).await?;
            assert!(
                matches!(&r[0], Val::Option(Some(_))),
                "the processed user came back"
            );
            processed += 1;
        } else {
            // the gate CLOSED: the processing call never fires — the
            // refusal is the OBSERVED control (a refused row that still
            // processed would double-count `processed`)
            refused += 1;
        }
    }
    assert_eq!(refused, 1, "the invalid user must be refused at the gate");
    assert_eq!(processed, 1, "only the valid user reaches processing");
    Ok(())
}

/// Stage C done-criteria: ONE E-code space across the boundary. The host's
/// generated registry (E104-E107, from Faults/Spec/Host.lean — host
/// codes start at 100 + the guest registry's length) and the guest's
/// (E100-E103, from Faults/Spec/Demo.lean) both resolve through
/// fast-observe's global lookup — the E-code means the same thing
/// regardless of which side reported it.
#[test]
fn fault_registry_resolves_host_and_guest_codes() {
    use fast_observe::lookup_error;

    // Host faults (generated host_faults_generated, registered at startup).
    guestlang_host::valves::register();
    let host = lookup_error("E104").expect("E104 registered");
    assert!(host.display.contains("not instantiated"), "{host:?}");
    assert!(lookup_error("E105").is_some(), "E105 registered");
    assert!(lookup_error("E107").is_some(), "E107 registered");

    // Guest faults (the framework crate registers faults_generated at init).
    lean_rust_wasm::faults_generated::init_guest();
    let guest = lookup_error("E100").expect("E100 registered");
    assert!(guest.display.contains("not found"), "{guest:?}");
    assert!(lookup_error("E103").is_some(), "E103 registered");
}

/// Stage B async: `watch-orders` is `async func` in the GENERATED WIT —
/// wasi 0.3 async ABI. wasmtime 47 binds the export as a Rust `async fn`
/// (inferred from the function TYPE — no bindgen! option needed; the
/// crate's `async` feature is on by default). The host awaits the guest's
/// future; the guest runs on wasmtime's async stack (epoch/fuel still
/// bound it).
#[tokio::test]
async fn gateway_typed_watch_orders_async_abi() -> Result<(), Box<dyn std::error::Error>> {
    use guestlang_host::bindings::GatewayOrderError;
    use guestlang_host::bindings::GatewayPre;

    let Some((engine, component)) = try_load(
        &gateway_component_path(),
        &format!(
            "skipping: build with `just wasm-guest-gateway` for {:?}",
            gateway_component_path()
        ),
    )?
    else {
        return Ok(());
    };

    let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
    let pre = rt.instantiate_pre(&component)?;
    let gw = GatewayPre::new(pre)?
        .instantiate_async(rt.store_mut())
        .await?;
    let iface = gw.demo_gateway_gateway_exports();

    // wasi 0.3 async ABI: the generated call takes an `Accessor` (wasmtime
    // 47's concurrent-call model) — run inside `run_concurrent`.
    let users = rt
        .store_mut()
        .run_concurrent(async |accessor| {
            iface
                .call_watch_orders(accessor, GatewayOrderError::EmptyCart)
                .await
        })
        .await??;
    assert_eq!(users.len(), 1);
    assert_eq!(users[0].id, 7);
    assert_eq!(users[0].name, "Grace");
    Ok(())
}

/// The COMPILED component: Lean logic → LCNF re-run → WAT → binary →
/// component embed/new (just wasm-compile). guestlang-host runs the backend's
/// output — the full guestlang pipeline, no wit-bindgen guest involved.
#[tokio::test]
async fn compiled_lean_component_runs() -> Result<(), Box<dyn std::error::Error>> {
    let Some((engine, component)) = try_load(
        &demo_component_path(),
        &format!(
            "skipping: run `just wasm-compile` to build {:?}",
            demo_component_path()
        ),
    )?
    else {
        return Ok(());
    };

    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    // double 21 = 42 — Lean logic, natively compiled to WASM.
    let r = rt.call("double", &[Val::U64(21)]).await?;
    assert_eq!(r, vec![Val::U64(42)]);
    // runPaps 5 = 8 — closures + pooled allocator inside the guest.
    let r = rt.call("run-paps", &[Val::U64(5)]).await?;
    assert_eq!(r, vec![Val::U64(8)]);
    // doubleArea 5 = 100 — ctor alloc → sproj read → Perceus dec → pool.
    let r = rt.call("double-area", &[Val::U64(5)]).await?;
    assert_eq!(r, vec![Val::U64(100)]);
    Ok(())
}

/// THE OBSERVABILITY SEAM'S CONTROL: the host's call path spans EXACTLY
/// what the schema declares (`observability_generated.rs` = the
/// schema-registry manifest, byte-tied). A registered call records a
/// span with the spec's name + the delivery tag; the span table's
/// COVERAGE = the registry by construction (an unregistered fn has no
/// span to open — the host cannot invent one).
#[tokio::test]
async fn the_span_manifest_governs_the_host_spans() -> Result<(), Box<dyn std::error::Error>> {
    let Some((engine, component)) = try_load(
        &demo_component_path(),
        &format!(
            "skipping: run `just wasm-compile` to build {:?}",
            demo_component_path()
        ),
    )?
    else {
        return Ok(());
    };
    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

    // the spec's table covers the world's exports (the schema's manifest
    // — the names = the kebab fn names; the delivery = the contract)
    for name in ["double", "watch-counts"] {
        assert!(
            guestlang_host::observability_generated::SPANS
                .iter()
                .any(|s| s.name == name),
            "the spec's span table must cover {name}"
        );
    }

    rt.call("double", &[Val::U64(21)]).await?;
    let spans = fast_observe::breakdown::drain_spans();
    let double_span = spans
        .iter()
        .find(|s| s.name == "double")
        .expect("the registered call must be spanned");
    assert_eq!(
        double_span.tag,
        Some("once"),
        "the delivery tag = the spec's"
    );

    // the stream fn's span carries the STREAM delivery tag (the
    // spec's contract, not the host's guess)
    let stream_spec = guestlang_host::observability_generated::SPANS
        .iter()
        .find(|s| s.name == "watch-counts")
        .expect("the stream's span spec");
    assert_eq!(stream_spec.delivery, "stream");
    Ok(())
}

//! Loads the real guest component, instantiates, calls exports.
// tokio::test's generated harness calls Result::expect on Result-returning
// test bodies — the disallowed-method hit is macro codegen, not test code.
#![allow(
    clippy::disallowed_methods,
    reason = "tokio::test codegen, not our code"
)]

use wasmtime::component::Val;

use steel_host::{CapabilitySet, ComponentRuntime, SteelEngine};

/// Component with lifted exports, produced by `just wasm-guest-component`
/// (wasm32-unknown-unknown core module + `wasm-tools component embed` +
/// `component new` for world `demo:guest/greeter`).
fn component_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/wasm32-unknown-unknown/debug/guest_demo.component.wasm")
}

/// The wasip3 artifact: std linked against wasi 0.3 component imports.
fn wasip3_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/wasm32-wasip3-local/debug/guest_demo.wasm")
}

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
    let engine = SteelEngine::new()?;
    let component = engine.load_component_bytes(ADDER_WAT.as_bytes())?;

    let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
    rt.instantiate(&component).await?;

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
    let path = component_path();
    let Ok(path) = std::fs::canonicalize(&path) else {
        eprintln!("skipping: run `just wasm-guest-component` to build {path:?}");
        return Ok(());
    };
    let engine = SteelEngine::new()?;
    let component = engine.load_component(&path)?;

    // Guest touches no WASI — closed box must still instantiate.
    let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
    rt.instantiate(&component).await?;

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
    let path = wasip3_path();
    if !path.exists() {
        eprintln!("skipping: run `just wasm-guest` to build {path:?}");
        return Ok(());
    }
    let engine = SteelEngine::new()?;
    let component = engine.load_component(&path)?;

    // The wasip3 std component imports wasi:cli/clocks/filesystem@0.3.0 —
    // instantiation proves the p3 host satisfies the world.
    let caps = CapabilitySet::STDIO.union(CapabilitySet::FS_READ);
    let mut rt = ComponentRuntime::new(engine.clone(), caps).await?;
    rt.instantiate(&component).await?;

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
    let engine = SteelEngine::new()?;
    let component = engine.load_component_bytes(ADDER_WAT.as_bytes())?;
    let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
    rt.instantiate(&component).await?;

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
    use steel_host::bindings::{GatewayPre, GatewayUser};

    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/wasm32-unknown-unknown/debug/guest_demo.gateway.component.wasm");
    let Ok(path) = std::fs::canonicalize(&path) else {
        eprintln!("skipping: build with `just wasm-guest-gateway` for {path:?}");
        return Ok(());
    };
    let engine = SteelEngine::new()?;
    let component = engine.load_component(&path)?;

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

/// Stage C done-criteria: ONE E-code space across the boundary. The host's
/// generated registry (E110-E113, from Faults/Spec/Host.lean) and the
/// guest's (E100-E103, from Faults/Spec/Demo.lean) both resolve through
/// fast-observe's global lookup — the E-code means the same thing
/// regardless of which side reported it.
#[test]
fn fault_registry_resolves_host_and_guest_codes() {
    use fast_observe::lookup_error;

    // Host faults (generated host_faults_generated, registered at startup).
    steel_host::valves::register();
    let host = lookup_error("E110").expect("E110 registered");
    assert!(host.display.contains("not instantiated"), "{host:?}");
    assert!(lookup_error("E111").is_some(), "E111 registered");
    assert!(lookup_error("E113").is_some(), "E113 registered");

    // Guest faults (the framework crate registers faults_generated at init).
    lean_rust_wasm::faults_generated::init_guest();
    let guest = lookup_error("E100").expect("E100 registered");
    assert!(guest.display.contains("not found"), "{guest:?}");
    assert!(lookup_error("E103").is_some(), "E103 registered");
}

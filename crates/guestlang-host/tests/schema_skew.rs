//! The VERSION-SKEW FAIL-FAST contract (schema.rs): the host refuses to
//! start against a guest whose export surface diverges from the
//! committed expectation — both schema hashes + the first differing
//! `fn/arity` named in the diagnostic.
//!
//! Pins: (a) the green path — the real demo component starts under the
//! committed expectation; (b) a guest with a perturbed surface is
//! refused; (c) a perturbed EXPECTATION is refused (the comparison
//! catches convention drift on EITHER side); (d) the triple agreement —
//! Lean's committed rendering (COVERAGE.md) == the host's compiled-in
//! constant == the surface derived from the built component.

#![allow(
    clippy::disallowed_methods,
    reason = "tokio::test codegen, not our code"
)]

use guestlang_host::schema::{self, EXPECTED_DEMO_SURFACE, StartError};
use guestlang_host::{CapabilitySet, ComponentRuntime, HostEngine};
use wasmtime::component::Val;

mod common;

use common::{canonicalize_or_skip, demo_component_path};

/// A guest with a PERTURBED surface: `double` takes two params (the
/// committed expectation says `double/1`). Everything else absent — the
/// first difference in canonical order is `double` itself.
const SKEWED_WAT: &str = r#"
(component
  (core module $m
    (func (export "double") (param i64 i64) (result i64)
      (i64.add (local.get 0) (local.get 1))))
  (core instance $i (instantiate $m))
  (func (export "double") (param "a" u64) (param "b" u64) (result u64)
    (canon lift (core func $i "double"))))
"#;

#[test]
fn the_hasher_matches_oracle_runner_and_coreutils() {
    // The schema hash is sha256 OF THE SURFACE STRING. This constant
    // was computed with coreutils sha256sum (a third, independent
    // hasher) — pinning it here locks guestlang-host's `schema_hash` and
    // oracle-runner's twin to the same digest.
    assert_eq!(
        schema::schema_hash(EXPECTED_DEMO_SURFACE),
        "d05c9a71f9bbda7615ed9482441cd68ce8efd164bc23251e69c78e3c7012fc10",
    );
}

/// (a) GREEN: the real guest matches the committed expectation — the
/// skew-checked startup instantiates and calls through.
#[tokio::test]
async fn matching_surface_starts() -> Result<(), Box<dyn std::error::Error>> {
    let Some(path) = canonicalize_or_skip(
        &demo_component_path(),
        "skipping: run `just wasm-compile` to build the demo component",
    ) else {
        return Ok(());
    };
    let engine = HostEngine::new()?;
    let component = engine.load_component(&path)?;

    schema::verify_surface(engine.engine(), &component, EXPECTED_DEMO_SURFACE)?;

    let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
    rt.instantiate_checked(&component, EXPECTED_DEMO_SURFACE).await?;
    let r = rt.call("double", &[Val::U64(21)]).await?;
    assert_eq!(r, vec![Val::U64(42)]);
    Ok(())
}

/// (b) the guest drifted: `double/2` where the host expects `double/1`
/// — startup is REFUSED, the diagnostic names both hashes + the first
/// differing fn/arity.
#[tokio::test]
async fn skewed_guest_refuses_to_start() -> Result<(), Box<dyn std::error::Error>> {
    let engine = HostEngine::new()?;
    let component = engine.load_component_bytes(SKEWED_WAT.as_bytes())?;

    let err = schema::verify_surface(engine.engine(), &component, EXPECTED_DEMO_SURFACE)
        .expect_err("a drifted guest surface must be refused");
    let msg = err.to_string();
    assert!(msg.contains("schema skew: refusing to start"), "{msg}");
    // both hashes named, and they are the hashes OF EACH SIDE:
    assert!(
        msg.contains(&format!(
            "expected sha256:{}",
            schema::schema_hash(EXPECTED_DEMO_SURFACE)
        )),
        "{msg}"
    );
    assert!(
        msg.contains(&format!("guest    sha256:{}", schema::schema_hash("double/2"))),
        "{msg}"
    );
    // the first difference names the fn + both arities:
    assert!(
        msg.contains("first difference: `double` — expected arity 1, guest arity 2"),
        "{msg}"
    );

    // the runtime seam refuses too — instantiation is never reached:
    let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
    let err = rt
        .instantiate_checked(&component, EXPECTED_DEMO_SURFACE)
        .await
        .expect_err("instantiate_checked must refuse a skewed guest");
    assert!(matches!(err, StartError::Skew(_)), "{err}");
    Ok(())
}

/// (c) the EXPECTATION drifted (a convention divergence on the host
/// side): the same comparison must catch it, naming the same first
/// difference from the other direction. Uses the real guest so only the
/// expectation is perturbed; falls back to the WAT adder when the
/// compiled component is absent (the first difference is `double`
/// either way).
#[tokio::test]
async fn skewed_expectation_refuses_to_start() -> Result<(), Box<dyn std::error::Error>> {
    // `double/1` → `double/2` in the committed string: the first entry
    // diverges.
    let perturbed = EXPECTED_DEMO_SURFACE.replacen("double/1", "double/2", 1);
    assert_ne!(perturbed, EXPECTED_DEMO_SURFACE);

    let engine = HostEngine::new()?;
    let component = match std::fs::canonicalize(demo_component_path()) {
        Ok(path) => engine.load_component(&path)?,
        Err(_) => {
            eprintln!("demo component absent — checking against the WAT fixture");
            engine.load_component_bytes(
                // `double/1` here: the perturbed expectation says /2.
                br#"
(component
  (core module $m
    (func (export "double") (param i64) (result i64)
      (i64.add (local.get 0) (local.get 0))))
  (core instance $i (instantiate $m))
  (func (export "double") (param "a" u64) (result u64)
    (canon lift (core func $i "double"))))
"#,
            )?
        }
    };

    let err = schema::verify_surface(engine.engine(), &component, &perturbed)
        .expect_err("a perturbed expectation must be refused");
    let msg = err.to_string();
    assert!(msg.contains("schema skew: refusing to start"), "{msg}");
    assert!(
        msg.contains(&format!("expected sha256:{}", schema::schema_hash(&perturbed))),
        "{msg}"
    );
    assert!(
        msg.contains("first difference: `double` — expected arity 2, guest arity 1"),
        "{msg}"
    );

    // a convention divergence need not be an arity: an expectation
    // naming an export the guest lacks is refused as MISSING.
    let unknown = format!("{EXPECTED_DEMO_SURFACE},tripler/1");
    let err = schema::verify_surface(engine.engine(), &component, &unknown)
        .expect_err("an unknown export in the expectation must be refused");
    assert!(
        err.to_string()
            .contains("guest missing export `tripler` (expected arity 1)"),
        "{err}"
    );
    Ok(())
}

/// (d) THE TRIPLE AGREEMENT: Lean's canonical string (its committed
/// rendering in the GENERATED lean/wasm-backend/COVERAGE.md) == the
/// host's compiled-in expectation == the surface derived from the built
/// guest component's TYPE. Any of the three drifting fails here.
#[tokio::test]
async fn lean_host_guest_surfaces_agree() -> Result<(), Box<dyn std::error::Error>> {
    // Leg 1 → 2: Lean's committed rendering (COVERAGE.md is GENERATED
    // by `lake exe oracle coverage` from Oracle.schemaSurface — do not
    // hand-edit) carries the surface in a backtick line under the
    // "Schema surface" header.
    let coverage = std::fs::read_to_string(common::coverage_md_path())?;
    let mut lines = coverage.lines();
    let lean_surface = loop {
        let Some(line) = lines.next() else {
            panic!("COVERAGE.md: schema surface line not found");
        };
        if line.starts_with("Schema surface") {
            let ticked = lines
                .find(|l| l.starts_with('`') && l.ends_with('`'))
                .expect("COVERAGE.md: backticked surface under the header");
            break ticked.trim_matches('`').to_string();
        }
    };
    assert_eq!(
        lean_surface, EXPECTED_DEMO_SURFACE,
        "Lean's committed schema surface drifted from the host's expectation"
    );

    // Leg 2 → 3: the built guest's component-TYPE surface, rendered
    // over the contract in canonical order, IS the expectation.
    let Some(path) = canonicalize_or_skip(
        &demo_component_path(),
        "skipping leg 3: run `just wasm-compile` to build the demo component",
    ) else {
        return Ok(());
    };
    let engine = HostEngine::new()?;
    let component = engine.load_component(&path)?;
    let got = schema::surface_of(engine.engine(), &component);
    let rendered = EXPECTED_DEMO_SURFACE
        .split(',')
        .map(|entry| {
            let f = entry.rsplit_once('/').expect("fn/arity").0;
            let (_, arity) = got
                .iter()
                .find(|(g, _)| g == f)
                .unwrap_or_else(|| panic!("guest missing export `{f}`"));
            format!("{f}/{arity}")
        })
        .collect::<Vec<_>>()
        .join(",");
    assert_eq!(
        rendered, EXPECTED_DEMO_SURFACE,
        "the guest component's surface drifted from the host's expectation"
    );
    Ok(())
}

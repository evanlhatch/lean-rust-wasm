//! The SPLICE-SMOKE run proof: the PASSTHROUGH-composed component
//! (`wac` splices a re-export layer onto the emitted component) still
//! RUNS in the host — the splicer didn't break the exports.
//!
//! Composition + validation alone (`just splice-smoke`) proves the WIT
//! is well-formed by an independent tool; this test proves the spliced
//! artifact is BEHAVIORALLY identical: the same exports, the same
//! answers, including the string return.

use steel_host::{CapabilitySet, ComponentRuntime, SteelEngine};
use wasmtime::component::Val;

fn spliced_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/wasm-backend/target/spliced.component.wasm")
}

#[tokio::test]
async fn the_spliced_component_still_runs() -> Result<(), Box<dyn std::error::Error>> {
    let engine = SteelEngine::new()?;
    let component = engine.load_component_bytes(&std::fs::read(spliced_path())?)?;
    let mut rt = ComponentRuntime::new(engine, CapabilitySet::NONE).await?;
    rt.instantiate(&component).await?;

    // scalars survive the splice
    let results = rt.call("double", &[Val::U64(21)]).await?;
    assert!(matches!(&results[0], Val::U64(42)), "spliced double broke");

    // the STRING return survives the splice (the canonical lift reads
    // the guest memory through the pass-through export)
    let results = rt.call("greet", &[Val::U64(1)]).await?;
    assert!(
        matches!(&results[0], Val::String(s) if s == "hello guest"),
        "spliced greet broke: {:?}",
        results[0]
    );
    Ok(())
}

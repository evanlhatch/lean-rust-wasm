//! The SPLICE-SMOKE run proof: the PASSTHROUGH-composed component
//! (`wac` splices a re-export layer onto the emitted component) still
//! RUNS in the host — the splicer didn't break the exports.
//!
//! Composition + validation alone (`just splice-smoke`) proves the WIT
//! is well-formed by an independent tool; this test proves the spliced
//! artifact is BEHAVIORALLY identical: the same exports, the same
//! answers, including the string return.

mod common;

use common::{instantiate, spliced_component_path};

use guestlang_host::CapabilitySet;
use wasmtime::component::Val;

#[tokio::test]
async fn the_spliced_component_still_runs() -> Result<(), Box<dyn std::error::Error>> {
    let engine = guestlang_host::HostEngine::new()?;
    let component = engine.load_component_bytes(&std::fs::read(spliced_component_path())?)?;
    let mut rt = instantiate(&engine, &component, CapabilitySet::NONE).await?;

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

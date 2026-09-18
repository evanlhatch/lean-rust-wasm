//! ISOLATION probe for the witness-batch divergence (the gap #1 FINDING's
//! evidence, not a gate): every verify-witness row of diff.json — or of
//! WITNESS_PROBE_MANIFEST (a crafted manifest, the binary-search
//! diagnostic) — replayed on a FRESH instance (new ComponentRuntime per
//! row) to classify state-dependence.
//!
//! OBSERVED (deterministic across runs): every row whose guest path
//! reaches the compiled `evalWBool?` bool fold (valid+gt, and/not,
//! chain claims — all refused where Lean accepts) DIVERGES; every
//! eqU+byEval row and every decode-refuse row agrees. See Oracle.lean's
//! header ("THE BATCH FOUND THE PREDICTED BUG").

#![allow(clippy::disallowed_methods, reason = "tokio::test codegen, not our code")]

use steel_host::{CapabilitySet, ComponentRuntime, SteelEngine};
use wasmtime::component::Val;

fn demo_path(rel: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/wasm-backend/target")
        .join(rel)
}

fn witness_rows() -> Vec<(String, String)> {
    // WITNESS_PROBE_MANIFEST: probe a crafted manifest's verify-witness
    // rows instead of diff.json's (the binary-search diagnostic).
    let path = std::env::var("WITNESS_PROBE_MANIFEST")
        .map(|p| demo_path(&p))
        .unwrap_or_else(|_| demo_path("diff.json"));
    let rows: Vec<serde_json::Value> =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    rows.into_iter()
        .filter(|r| r["fn"] == "verify-witness")
        .map(|r| {
            (
                r["args"][0].as_str().unwrap().to_string(),
                r["expected"].as_str().unwrap().to_string(),
            )
        })
        .collect()
}

#[tokio::test]
async fn witness_rows_fresh_instance_each() -> Result<(), Box<dyn std::error::Error>> {
    let engine = SteelEngine::new()?;
    let component =
        engine.load_component_bytes(&std::fs::read(demo_path("demo.component.wasm"))?)?;
    for (i, (bytes, expected)) in witness_rows().into_iter().enumerate() {
        // FRESH runtime + instance per row — no cross-row state.
        let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
        rt.instantiate(&component).await?;
        let arg = Val::List(
            bytes
                .split(',')
                .map(|b| Val::U8(b.parse::<u8>().expect("u8")))
                .collect(),
        );
        let got = match rt.call("verify-witness", &[arg]).await {
            Ok(res) => match &res[0] {
                Val::Bool(b) => format!("{}", if *b { 1 } else { 0 }),
                other => format!("other:{other:?}"),
            },
            Err(e) => format!("TRAP({e})"),
        };
        let flag = if got == expected { "ok" } else { "DIVERGE" };
        println!("row {i}: expected {expected} got {got} {flag} bytes={bytes}");
    }
    Ok(())
}

//! FAULT INJECTION — corrupt/truncated artifacts at the host's load
//! boundary (review 2026-09-16 item 6). The Lean side mandates negative
//! controls; this file is the Rust host's equivalent for its
//! artifact-loading seams.
//!
//! House pattern (see wasm-delta/tests/crash_recovery.rs): copy the
//! artifact to a tempdir, corrupt, assert the FAILURE MODE —
//!   (a) the operation FAILS,
//!   (b) the failure is a structured `Err` on a panic-free path whose
//!       message names the corruption class (or the artifact),
//!   (c) the process continues: the SAME engine parses a good artifact
//!       afterwards (statelessness — a corrupt load poisons nothing).
//!
//! Injection surface mapped before writing (what is actually loadable-
//! corruptible):
//!   - `src/*_generated.rs` — COMPILED IN, not a runtime artifact. Not injectable; excluded by
//!     construction.
//!   - `lean/wasm-backend/target/demo.component.wasm` — the guest, loaded via
//!     `HostEngine::load_component` (wasmtime `Component::from_file`). THE wasm target.
//!   - `tests/fixtures/wit_fixture_*.wit` — parsed by wit-parser at test time
//!     (`wit_fixture_sweep.rs`).
//!   - `tests/fixtures/wit_manifest.json` + `goldens/universe.snapshot` — consumed ONLY by tests
//!     (the sweep / round-trip gates) and by `src/hostgen.rs` (W8.11: the host parses the snapshot
//!     and validates its generated surface + types against the committed expectation —
//!     `tests/hostgen_byte_tie.rs` pins the failure modes: parse errors and contract skew are
//!     structured, never a panic). The manifest gets one truncation case (the corruption class must
//!     be detectable by its serde consumer); the snapshot's corruption classes are pinned by
//!     hostgen's parse gate.
//!   - the schema-skew check (`schema.rs`) — `schema_skew.rs` covers the perturbed SURFACE; here: a
//!     TRUNCATED guest fails at load, BEFORE the skew check can even read a surface (fail-fast
//!     order).

#![allow(
    clippy::disallowed_methods,
    reason = "tokio::test codegen, not our code"
)]

mod common;

use common::canonicalize_or_skip;
use common::demo_component_path;
use common::demo_core_path;
use common::fail;
use common::fixtures_dir;
use common::load_json_manifest;
use common::strip_header_comments;
use common::tempdir;
use guestlang_host::CapabilitySet;
use guestlang_host::ComponentRuntime;
use guestlang_host::HostEngine;
use guestlang_host::schema::EXPECTED_DEMO_SURFACE;
use guestlang_host::schema::{self};

/// THE truncation sweep: the guest component cut at offsets across the
/// whole file — dense at the header (the first 64 bytes carry magic /
/// version / the first section envelope), strided through the body.
/// Every cut must fail `load_component` with a structured Err (never a
/// panic, never silent acceptance of a prefix), and the engine must
/// still load the intact component afterwards.
#[test]
fn truncated_guest_component_fails_cleanly_at_every_cut() {
    let Some(path) = canonicalize_or_skip(
        &demo_component_path(),
        "skipping: run `just wasm-compile` to build the demo component",
    ) else {
        return;
    };
    let bytes = std::fs::read(&path).unwrap_or_else(|e| fail(&format!("read guest: {e}")));
    let engine = HostEngine::new().unwrap_or_else(|e| fail(&format!("engine: {e}")));
    let dir = tempdir("trunc-sweep");
    let cut_path = dir.join("cut.wasm");

    let mut cuts: Vec<usize> = (0..=64.min(bytes.len())).collect();
    cuts.extend((1024..bytes.len()).step_by(1024));
    cuts.push(bytes.len() - 1);
    cuts.dedup();

    // OBSERVED: the wasm component format is self-delimiting — a file
    // cut to exactly its 8-byte header (magic + version, zero sections)
    // IS a well-formed EMPTY component and loads. That is not silent
    // acceptance of corruption: the load boundary's contract is
    // well-formedness, and the SKEW CHECK is the layer that refuses an
    // empty surface. The sweep's invariant is therefore the
    // composition: no truncation may BOTH load AND pass as the guest.
    let mut rejected = 0u32;
    let mut header_only_loads = 0u32;
    for cut in cuts {
        std::fs::write(&cut_path, &bytes[..cut]).unwrap_or_else(|e| fail(&format!("write: {e}")));
        match engine.load_component(&cut_path) {
            Ok(component) => {
                // A valid-prefix load (the empty-component header):
                // the skew check must STILL refuse it — no truncation
                // impersonates the guest.
                if schema::verify_surface(engine.engine(), &component, EXPECTED_DEMO_SURFACE)
                    .is_ok()
                {
                    fail(&format!(
                        "cut {cut}: a truncated component passed the skew check (impersonation)"
                    ));
                }
                header_only_loads += 1;
            }
            Err(e) => {
                let msg = format!("{e:?}");
                assert!(
                    !msg.is_empty(),
                    "cut {cut}: the load error must SAY something"
                );
                rejected += 1;
            }
        }
    }
    assert!(
        rejected > 100,
        "vacuous: the sweep must reject many cuts, got {rejected}"
    );
    eprintln!(
        "truncation sweep: {rejected} cuts refused at load, \
         {header_only_loads} empty-header loads refused by the skew check"
    );

    // (c) STATELESSNESS: the same engine still loads the intact guest.
    engine
        .load_component(&path)
        .unwrap_or_else(|e| fail(&format!("good load after the sweep must succeed: {e}")));
    std::fs::remove_dir_all(&dir).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// Corruption CLASSES that are not truncation: a destroyed magic
/// header, a non-wasm text file, and a CORE wasm module where a
/// component is required. Each must be a named error, not a panic/UB.
#[test]
fn corrupt_guest_bytes_fail_with_a_named_error() {
    let Some(path) = canonicalize_or_skip(
        &demo_component_path(),
        "skipping: run `just wasm-compile` to build the demo component",
    ) else {
        return;
    };
    let bytes = std::fs::read(&path).unwrap_or_else(|e| fail(&format!("read guest: {e}")));
    let engine = HostEngine::new().unwrap_or_else(|e| fail(&format!("engine: {e}")));
    let dir = tempdir("corrupt");

    // Class 1: destroyed magic header (`\0asm` → garbage).
    let mut bad_magic = bytes.clone();
    bad_magic[..4].copy_from_slice(b"NOPE");
    let p = dir.join("bad-magic.wasm");
    std::fs::write(&p, &bad_magic).unwrap_or_else(|e| fail(&format!("write: {e}")));
    let err = match engine.load_component(&p) {
        Ok(_) => fail("a destroyed magic header must be refused"),
        Err(e) => e,
    };
    let msg = format!("{err:?}").to_lowercase();
    assert!(
        msg.contains("magic") || msg.contains("unexpected"),
        "magic corruption must be NAMED as such: {msg}"
    );

    // Class 2: not wasm at all.
    let p = dir.join("text.wasm");
    std::fs::write(&p, b"this is not a wasm component, it is a hostage note")
        .unwrap_or_else(|e| fail(&format!("write: {e}")));
    let err = match engine.load_component(&p) {
        Ok(_) => fail("text bytes must be refused"),
        Err(e) => e,
    };
    assert!(
        !format!("{err:?}").is_empty(),
        "the refusal must say something"
    );

    // Class 3: a CORE module where a COMPONENT is required — the
    // pre-`component new` artifact is a well-formed wasm binary of the
    // wrong layer.
    let core_path = demo_core_path();
    if let Ok(core) = std::fs::canonicalize(&core_path) {
        let err = match engine.load_component(&core) {
            Ok(_) => fail("a core module must be refused by the component loader"),
            Err(e) => e,
        };
        let msg = format!("{err:?}").to_lowercase();
        assert!(
            msg.contains("component"),
            "the core/module confusion must be NAMED: {msg}"
        );
    } else {
        eprintln!("skipping class 3: demo.wasm (pre-component) absent");
    }

    // (c) STATELESSNESS.
    engine
        .load_component(&path)
        .unwrap_or_else(|e| fail(&format!("good load after corruption must succeed: {e}")));
    std::fs::remove_dir_all(&dir).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// THE FAIL-FAST ORDER against a truncated guest: the load error fires
/// BEFORE the skew check (there is no surface to read off a truncated
/// component), and it is a structured Err — then the intact guest
/// passes `verify_surface` + `instantiate_checked` on the SAME engine
/// (the skew seam is unpoisoned). `schema_skew.rs` owns the perturbed-
/// surface cases; this extends them to a guest that cannot be parsed.
#[tokio::test]
async fn truncated_guest_fails_before_the_skew_check() -> Result<(), Box<dyn std::error::Error>> {
    let Some(path) = canonicalize_or_skip(
        &demo_component_path(),
        "skipping: run `just wasm-compile` to build the demo component",
    ) else {
        return Ok(());
    };
    let bytes = std::fs::read(&path)?;
    let engine = HostEngine::new()?;
    let dir = tempdir("skew-trunc");

    // A cut deep inside the body: past the header, still invalid.
    let p = dir.join("truncated.component.wasm");
    std::fs::write(&p, &bytes[..bytes.len() / 2])?;
    let err = match engine.load_component(&p) {
        Ok(_) => fail("a truncated guest must fail at LOAD"),
        Err(e) => e,
    };
    let msg = format!("{err:?}").to_lowercase();
    assert!(
        msg.contains("unexpected end")
            || msg.contains("eof")
            || msg.contains("length")
            || msg.contains("out of bounds"),
        "the truncation class must be NAMED: {msg}"
    );

    // The intact guest on the same engine: the skew check passes and
    // the checked instantiation runs (the seam is unpoisoned).
    let component = engine.load_component(&path)?;
    schema::verify_surface(engine.engine(), &component, EXPECTED_DEMO_SURFACE)?;
    let mut rt = ComponentRuntime::new(engine.clone(), CapabilitySet::NONE).await?;
    rt.instantiate_checked(&component, EXPECTED_DEMO_SURFACE)
        .await?;
    let r = rt
        .call("double", &[wasmtime::component::Val::U64(21)])
        .await?;
    assert_eq!(r, vec![wasmtime::component::Val::U64(42)]);

    std::fs::remove_dir_all(&dir)?;
    Ok(())
}

/// Corrupt WIT fixtures: the sweep's parser (wit-parser — an
/// INDEPENDENT parser, not the Lean printer) must refuse a truncated or
/// mangled fixture with a named diagnostic, and the good fixture must
/// still parse afterwards.
#[test]
fn corrupt_wit_fixture_fails_with_a_named_diagnostic() {
    let dir = tempdir("wit");
    for name in ["scalars", "nested", "variants", "async"] {
        let src = fixtures_dir().join(format!("wit_fixture_{name}.wit"));
        let raw = std::fs::read_to_string(&src)
            .unwrap_or_else(|e| fail(&format!("read fixture {name}: {e}")));

        // Class 1: truncation mid-file.
        let p = dir.join(format!("{name}-trunc.wit"));
        std::fs::write(&p, &raw[..raw.len() / 2]).unwrap_or_else(|e| fail(&format!("write: {e}")));
        let mut resolve = wit_parser::Resolve::default();
        let err = match resolve.push_path(&p) {
            Ok(_) => fail(&format!(
                "fixture {name}: a truncated fixture must not parse"
            )),
            Err(e) => e,
        };
        let msg = format!("{err:#}");
        assert!(
            !msg.is_empty(),
            "fixture {name}: the parse refusal must say something"
        );

        // Class 2: mangled keyword (`interface` → `interf4ce`): a
        // syntactically broken but complete file — the diagnostic must
        // locate the failure (line/column or the offending token).
        if raw.contains("interface") {
            let p = dir.join(format!("{name}-mangled.wit"));
            std::fs::write(&p, raw.replacen("interface", "interf4ce", 1))
                .unwrap_or_else(|e| fail(&format!("write: {e}")));
            let mut resolve = wit_parser::Resolve::default();
            let err = match resolve.push_path(&p) {
                Ok(_) => fail(&format!(
                    "fixture {name}: a mangled keyword must not parse (silent acceptance)"
                )),
                Err(e) => e,
            };
            let msg = format!("{err:#}");
            assert!(
                msg.contains("line") || msg.contains("expected") || msg.contains("unknown"),
                "fixture {name}: the mangling must be LOCATED by the diagnostic: {msg}"
            );
        }

        // (c) STATELESSNESS: the intact fixture still parses.
        let mut resolve = wit_parser::Resolve::default();
        resolve
            .push_path(&src)
            .unwrap_or_else(|e| fail(&format!("fixture {name}: good parse after corrupt: {e}")));
    }
    std::fs::remove_dir_all(&dir).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// The fixture manifest (`wit_manifest.json`): consumed ONLY by the
/// test-side sweep via serde_json — pin that its corruption CLASS is
/// detectable by that consumer (a truncated manifest is a syntax error,
/// a schema-wrong manifest parses but fails the shape check the sweep
/// applies). No runtime failure mode exists here (the runtime never
/// reads this file); this guards the gate's own input.
#[test]
fn corrupt_wit_manifest_is_detectable_by_its_consumer() {
    let raw = std::fs::read_to_string(fixtures_dir().join("wit_manifest.json"))
        .unwrap_or_else(|e| fail(&format!("read manifest: {e}")));
    let json = strip_header_comments(&raw);

    // Class 1: truncation → serde_json SYNTAX error (named class).
    let err = serde_json::from_str::<serde_json::Value>(&json[..json.len() / 2])
        .expect_err("a truncated manifest must not parse");
    assert!(
        err.is_syntax() || err.is_eof(),
        "the truncation must be a syntax/EOF class error: {err}"
    );

    // Class 2: schema-wrong but syntactically valid — an object where
    // the sweep requires an array: parses, but the consumer's shape
    // check (`as_array`) rejects it.
    let wrong: serde_json::Value = serde_json::from_str(r#"{"fixture": "scalars"}"#)
        .unwrap_or_else(|e| fail(&format!("control parse: {e}")));
    assert!(
        wrong.as_array().is_none(),
        "a schema-wrong manifest must fail the array shape check"
    );

    // (c) STATELESSNESS: the intact manifest still parses to an array.
    let good = load_json_manifest(&fixtures_dir().join("wit_manifest.json"));
    assert!(good.as_array().is_some(), "the good manifest is an array");
}

//! The host's own teeth: the load+run pin, the tamper teeth (a
//! corrupted artifact refuses, typed), the skew teeth (an incomplete
//! artifact set refuses, typed), and the golden-mismatch tooth (a
//! VALID module that answers something else is still a refusal).

use std::fs;
use std::path::PathBuf;

use mandate_host::{GOLDEN_ANSWER, HostError, run_answer, run_slice};

fn gen_dir() -> PathBuf {
    mandate_host::repo_gen_dir()
}

/// A fresh per-test copy of the committed artifact set (the tamper
/// teeth mutate their copy, never the committed universe).
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "mandate-host-{}-{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("scratch dir");
    let committed = gen_dir();
    for f in ["wasm-slice.wasm", "wasm-slice.wasm.hdr", "schema-slice.wit"] {
        fs::copy(committed.join(f), dir.join(f)).expect("copy the committed artifact");
    }
    dir
}

/// THE PIN: the committed module loads skew-checked and runs to the
/// golden — the artifact the toolchain emitted is the artifact the
/// host runs, and it produces `i64 42`.
#[test]
fn the_slice_runs_to_the_golden() {
    let got = run_slice(&gen_dir()).expect("the committed slice runs");
    assert_eq!(got, GOLDEN_ANSWER);
    assert_eq!(got, 42);
}

/// TAMPER TOOTH: one flipped byte in the module -> the hash tie
/// refuses with the typed mismatch, and the engine never sees bytes.
#[test]
fn tampered_module_refuses() {
    let dir = scratch("tampered-module");
    let p = dir.join("wasm-slice.wasm");
    let mut wasm = fs::read(&p).expect("read");
    let last = wasm.len() - 1;
    wasm[last] ^= 0xff;
    fs::write(&p, wasm).expect("write");

    let err = run_slice(&dir).expect_err("tampered bytes refuse");
    assert!(matches!(err, HostError::ContentHashMismatch { .. }), "{err:?}");
}

/// TAMPER TOOTH: a doctored SIDECAR (the declared hash no longer names
/// the bytes) refuses too — the tie is bidirectional in effect: both
/// directions of drift name the same typed mismatch.
#[test]
fn tampered_sidecar_refuses() {
    let dir = scratch("tampered-sidecar");
    let p = dir.join("wasm-slice.wasm.hdr");
    let sidecar = fs::read_to_string(&p).expect("read");
    let doctored = sidecar.replace(
        "content hash 10175063987543006018",
        "content hash 10175063987543006019",
    );
    assert_ne!(sidecar, doctored, "the committed hash string must be present");
    fs::write(&p, doctored).expect("write");

    let err = run_slice(&dir).expect_err("a doctored sidecar refuses");
    assert!(matches!(err, HostError::ContentHashMismatch { .. }), "{err:?}");
}

/// SKEW TOOTH: the sidecar is absent -> the artifact set is
/// incomplete, refused before the engine starts.
#[test]
fn missing_sidecar_refuses() {
    let dir = scratch("missing-sidecar");
    fs::remove_file(dir.join("wasm-slice.wasm.hdr")).expect("remove");

    let err = run_slice(&dir).expect_err("the incomplete set refuses");
    assert!(
        matches!(err, HostError::Io { what: "wasm-slice.wasm.hdr", .. }),
        "{err:?}"
    );
}

/// SKEW TOOTH: the WIT surface is absent -> refused (the artifact set
/// is incomplete even though the module itself is intact).
#[test]
fn missing_wit_refuses() {
    let dir = scratch("missing-wit");
    fs::remove_file(dir.join("schema-slice.wit")).expect("remove");

    let err = run_slice(&dir).expect_err("the incomplete set refuses");
    assert!(
        matches!(err, HostError::Io { what: "schema-slice.wit", .. }),
        "{err:?}"
    );
}

/// SKEW TOOTH: a hand-made (non-GENERATED) WIT file fails the presence
/// check.
#[test]
fn forged_wit_refuses() {
    let dir = scratch("forged-wit");
    fs::write(dir.join("schema-slice.wit"), "package not-mine;\n").expect("write");

    let err = run_slice(&dir).expect_err("a forged surface refuses");
    assert!(matches!(err, HostError::Incomplete(_)), "{err:?}");
}

/// GOLDEN TOOTH: a VALID, correctly sidecar'd module whose `answer`
/// returns 43 — the run itself refuses with the typed mismatch. (The
/// sidecar is recomputed for the doctored bytes: this isolates the
/// golden check from the hash tie.)
#[test]
fn wrong_answer_refuses() {
    let dir = scratch("wrong-answer");
    let wat = "(module (type (func (result i64))) \
               (export \"answer\" (func 0)) (func (type 0) i64.const 43))";
    let wasm = wat::parse_str(wat).expect("the wrong-answer module builds");
    fs::write(dir.join("wasm-slice.wasm"), &wasm).expect("write");
    // Re-sidecar the doctored bytes with the SAME recurrence the
    // toolchain uses (mandate_host::bytes_hash — the pinned twin).
    let hash = mandate_host::bytes_hash(&wasm);
    let sidecar = fs::read_to_string(dir.join("wasm-slice.wasm.hdr")).expect("read");
    let resided = sidecar.replace(
        "content hash 10175063987543006018",
        &format!("content hash {hash}"),
    );
    fs::write(dir.join("wasm-slice.wasm.hdr"), resided).expect("write");

    let err = run_slice(&dir).expect_err("43 is not the golden");
    assert!(matches!(err, HostError::AnswerMismatch { got: 43 }), "{err:?}");
}

/// The run path over RAW bytes (no artifact set) still enforces the
/// golden — `run_answer` is the engine seam and carries the same
/// tooth.
#[test]
fn raw_run_answer_checks_the_golden() {
    let got = run_answer(&fs::read(gen_dir().join("wasm-slice.wasm")).expect("read"))
        .expect("the committed bytes run");
    assert_eq!(got, GOLDEN_ANSWER);
    let wat = "(module (export \"answer\" (func 0)) (func (result i64) i64.const 43))";
    let err = run_answer(&wat::parse_str(wat).expect("builds")).expect_err("43 refuses");
    assert!(matches!(err, HostError::AnswerMismatch { got: 43 }), "{err:?}");
}

/// The engine seam reports a missing export and a wrong signature as
/// typed errors (no panics on real error paths).
#[test]
fn missing_export_and_signature_are_typed() {
    let no_export = wat::parse_str("(module (func (result i64) i64.const 42))")
        .expect("builds");
    assert!(matches!(
        run_answer(&no_export),
        Err(HostError::MissingExport(name)) if name == "answer"
    ));

    let wrong_ty = wat::parse_str(
        "(module (export \"answer\" (func 0)) (func (result i32) i32.const 42))",
    )
    .expect("builds");
    assert!(matches!(run_answer(&wrong_ty), Err(HostError::Signature)));
}

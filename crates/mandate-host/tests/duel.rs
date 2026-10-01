//! The duel suite: the full duel agrees (the pin), and the TEETH — a
//! tampered expectation diverges WITH THE WITNESS (the row + both
//! values), a tampered vector refuses on the sidecar tie, and the
//! invalid control's expected refusal passes (the negative control).
//! Every scratch run is a per-test copy of the committed duel
//! directory; the committed universe is never mutated.

use std::fs;
use std::path::{Path, PathBuf};

use mandate_host::{Expectation, HostError, RowVerdict, run_duel};

/// The committed duel directory.
fn committed_duel_dir() -> PathBuf {
    mandate_host::repo_gen_dir().join("wasm-duel")
}

/// A scratch repo root: `<tmp>/<name>/gen/wasm-duel/...` — a fresh
/// copy of the committed duel directory (the manifest + the vectors +
/// their sidecars). Returns the scratch GEN dir (run_duel's input).
fn scratch(name: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!(
        "mandate-duel-{}-{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&root);
    let duel = root.join("gen").join("wasm-duel");
    fs::create_dir_all(&duel).expect("scratch duel dir");
    for entry in fs::read_dir(committed_duel_dir()).expect("the committed duel dir") {
        let entry = entry.expect("entry");
        if entry.path().is_file() {
            fs::copy(entry.path(), duel.join(entry.file_name())).expect("copy the artifact");
        }
    }
    root.join("gen")
}

/// Rewrites the manifest: every row whose path is `path` gets its
/// expectation replaced by `new` (the tamper teeth's editor).
fn retarget(scratch_gen: &Path, path: &str, new: &str) {
    let mpath = scratch_gen.join("wasm-duel").join("manifest.txt");
    let text = fs::read_to_string(&mpath).expect("read the manifest");
    let old_prefix = format!("{path}\t");
    let mut hit = false;
    let out: String = text
        .lines()
        .map(|l| {
            if l.starts_with(&old_prefix) {
                hit = true;
                format!("{path}\t{new}")
            } else {
                l.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(hit, "the manifest names {path}");
    fs::write(&mpath, out).expect("write the doctored manifest");
}

/// THE PIN: the committed duel runs, and EVERY row agrees — the Lean
/// executor's computed expectations and the real engine's observed
/// values agree over the slice + the whole family, and the invalid
/// control's refusal passes on BOTH sides (the negative control).
#[test]
fn the_duel_agrees() {
    let report = run_duel(&mandate_host::repo_gen_dir()).expect("the duel runs");
    assert_eq!(report.generator, "WasmCore.Duel");
    // 1 slice + 19 generated op rows + 7 mem + 7 mem-trap + 3
    // scenarios + 1 invalid control = 38.
    assert_eq!(report.rows.len(), 38, "the slice + 33 generated + 3 scenarios + the control");
    for row in &report.rows {
        assert!(matches!(row.verdict, RowVerdict::Agree), "{:?}", row);
    }
    // The rows' identities, in order (the manifest's shape): the seed,
    // then the op-table fold's rows (allOps order, then the mem rows'
    // normal + trap pairs), then the scenarios, the control last.
    let names: Vec<&str> = report.rows.iter().map(|r| r.path.as_str()).collect();
    assert_eq!(names[0], "gen/wasm-duel/op-i64.add.wasm");
    assert_eq!(names[18], "gen/wasm-duel/op-i64.extend_i32_u.wasm");
    assert_eq!(names[19], "gen/wasm-duel/mem-i32.load8_u.wasm");
    assert_eq!(names[25], "gen/wasm-duel/mem-i64.store8.wasm");
    assert_eq!(names[26], "gen/wasm-duel/trap-mem-i32.load8_u.wasm");
    assert_eq!(names[32], "gen/wasm-duel/trap-mem-i64.store8.wasm");
    assert_eq!(names[33], "gen/wasm-duel/slice.wasm");
    assert_eq!(names[34], "gen/wasm-duel/control.wasm");
    assert_eq!(names[35], "gen/wasm-duel/memory.wasm");
    assert_eq!(names[36], "gen/wasm-duel/trap.wasm");
    assert_eq!(names[37], "gen/wasm-duel/invalid.wasm");
    // The expected vocabularies actually crossed (a duel whose rows
    // all collapsed to one kind would be vacuous coverage).
    assert_eq!(report.rows[33].expectation, Expectation::Run("i64:42".into()));
    assert_eq!(report.rows[36].expectation, Expectation::Trap);
    assert_eq!(report.rows[37].expectation, Expectation::Refuse);
    // The fold: all-agree IS agree.
    assert_eq!(report.verdict(), RowVerdict::Agree);
    // THE TIER HONESTY: the report says TESTED AGREEMENT, never proof.
    let rendered = report.render();
    assert!(rendered.contains("TESTED AGREEMENT"), "{rendered}");
    assert!(rendered.contains("never a theorem"), "{rendered}");
}

/// TAMPER TOOTH (the deliberate-wrong-expectation control): the
/// GENERATED `op-i32.add` row's committed expectation
/// `run i64:4294967294` doctored to 43 — the host reports the
/// DIVERGENCE with the witness: the row AND both values.
#[test]
fn tampered_expectation_diverges_with_witness() {
    let gdir = scratch("tampered-expectation");
    retarget(&gdir, "gen/wasm-duel/op-i32.add.wasm", "run i64:43");

    let report = run_duel(&gdir).expect("the duel still runs");
    match report.verdict() {
        RowVerdict::Diverge { loc, lhs, rhs } => {
            assert_eq!(loc, "gen/wasm-duel/op-i32.add.wasm");
            assert_eq!(lhs, "run i64:43", "lhs names the tampered expectation");
            assert_eq!(rhs, "i64:4294967294", "rhs names the engine's true observation");
        }
        other => panic!("expected the divergence witness, got {other:?}"),
    }
    // The OTHER rows still agree (the fold names the first failure).
    assert_eq!(report.rows[0].verdict, RowVerdict::Agree);
}

/// TRAP-LANE TOOTH: the slice row's expectation doctored from
/// `run i64:42` to `trap` — the engine produced a VALUE where the
/// manifest demands a trap: the divergence, witnessed both ways.
#[test]
fn trap_expectation_against_a_value_diverges() {
    let gdir = scratch("trap-vs-value");
    retarget(&gdir, "gen/wasm-duel/slice.wasm", "trap");

    let report = run_duel(&gdir).expect("the duel still runs");
    match report.verdict() {
        RowVerdict::Diverge { loc, lhs, rhs } => {
            assert_eq!(loc, "gen/wasm-duel/slice.wasm");
            assert_eq!(lhs, "trap");
            assert_eq!(rhs, "i64:42");
        }
        other => panic!("expected the divergence witness, got {other:?}"),
    }
}

/// VALUE-LANE TOOTH (the mirror): the TRAP row's expectation doctored
/// to `run i64:0` — the engine TRAPS where the manifest demands a
/// value: the same lane, crossed the other way.
#[test]
fn run_expectation_against_a_trap_diverges() {
    let gdir = scratch("value-vs-trap");
    retarget(&gdir, "gen/wasm-duel/trap.wasm", "run i64:0");

    let report = run_duel(&gdir).expect("the duel still runs");
    match report.verdict() {
        RowVerdict::Diverge { loc, lhs, rhs } => {
            assert_eq!(loc, "gen/wasm-duel/trap.wasm");
            assert_eq!(lhs, "run i64:0");
            assert_eq!(rhs, "trap");
        }
        other => panic!("expected the divergence witness, got {other:?}"),
    }
}

/// REFUSAL-LANE TOOTH: the INVALID control's expectation doctored
/// from `refuse` to `run i64:1` — the host's engine REFUSES the
/// module (as Lean's validator did at generation), and the demand for
/// a value is the divergence.
#[test]
fn run_expectation_against_a_refusal_diverges() {
    let gdir = scratch("run-vs-refuse");
    retarget(&gdir, "gen/wasm-duel/invalid.wasm", "run i64:1");

    let report = run_duel(&gdir).expect("the duel still runs");
    match report.verdict() {
        RowVerdict::Diverge { loc, lhs, rhs } => {
            assert_eq!(loc, "gen/wasm-duel/invalid.wasm");
            assert_eq!(lhs, "run i64:1");
            assert!(rhs.starts_with("the host refused to compile"), "{rhs}");
        }
        other => panic!("expected the divergence witness, got {other:?}"),
    }
}

/// TAMPER TOOTH (the vector itself): one flipped byte in a committed
/// vector — the per-vector sidecar tie refuses BEFORE the engine sees
/// a byte: the typed refusal IS the row's verdict (a duel row's
/// refusal is a verdict, never a crash).
#[test]
fn tampered_vector_refuses_on_the_sidecar_tie() {
    let gdir = scratch("tampered-vector");
    let vp = gdir.join("wasm-duel").join("op-i32.add.wasm");
    let mut wasm = fs::read(&vp).expect("read");
    let last = wasm.len() - 1;
    wasm[last] ^= 0xff;
    fs::write(&vp, wasm).expect("write");

    let report = run_duel(&gdir).expect("the duel still runs");
    match report.verdict() {
        RowVerdict::Refused { why } => {
            assert!(why.contains("sidecar hash mismatch"), "{why}");
        }
        other => panic!("expected the refusal, got {other:?}"),
    }
}

/// SKEW TOOTH: a vector's sidecar doctored to name another hash — the
/// same tie, the other direction.
#[test]
fn tampered_sidecar_refuses() {
    let gdir = scratch("tampered-duel-sidecar");
    let sp = gdir.join("wasm-duel").join("slice.wasm.hdr");
    let sidecar = fs::read_to_string(&sp).expect("read");
    // Decrement the declared hash's last digit (a parseable but WRONG
    // value — the tie must name the DRIFT, never a malformed field).
    let start = sidecar.find("content hash ").expect("the field") + "content hash ".len();
    let digits: &str = sidecar[start..].split(|c: char| !c.is_ascii_digit()).next().unwrap();
    assert!(!digits.is_empty(), "the committed sidecar names a hash");
    let last = digits.chars().last().unwrap().to_digit(10).unwrap();
    let rolled = (last + 9) % 10;
    let doctored = format!(
        "{}{}{}",
        &sidecar[..start],
        &digits[..digits.len() - 1],
        rolled
    );
    assert_ne!(sidecar, doctored);
    fs::write(&sp, doctored).expect("write");

    let report = run_duel(&gdir).expect("the duel still runs");
    match report.verdict() {
        RowVerdict::Refused { why } => {
            assert!(why.contains("sidecar hash mismatch"), "{why}");
        }
        other => panic!("expected the refusal, got {other:?}"),
    }
}

/// The manifest's OWN shape is enforced: a hand-mangled manifest is a
/// typed refusal before any row runs.
#[test]
fn mangled_manifest_refuses() {
    let gdir = scratch("mangled-manifest");
    let mpath = gdir.join("wasm-duel").join("manifest.txt");
    fs::write(&mpath, "not a manifest\n").expect("write");
    let err = run_duel(&gdir).expect_err("the mangled manifest refuses");
    assert!(matches!(err, HostError::DuelManifest(_)), "{err:?}");
}

// ── THE THREE-WAY DUEL (D1's triangle: Lean exec ≡ wasmtime ≡ wasmi) ──

use mandate_host::{TriVerdict, run_triangle};

/// THE TRIANGLE PIN: all 38 rows agree on BOTH engine legs — the Lean
/// executor's computed expectations match wasmtime's AND wasmi's
/// observations over the whole family (the rt-conformance face: the
/// portability proof, both engines riding the ONE committed profile).
#[test]
fn the_triangle_agrees() {
    let report = run_triangle(&mandate_host::repo_gen_dir()).expect("the triangle runs");
    assert_eq!(report.generator, "WasmCore.Duel");
    assert_eq!(report.rows.len(), 38, "the same 38 vectors, both legs");
    for row in &report.rows {
        assert!(matches!(row.verdict, TriVerdict::Agree), "{:?}", row);
    }
    // The fold: all-agree IS agree; the tier sentence is part of the
    // report (TESTED AGREEMENT, never a theorem).
    assert_eq!(report.verdict(), TriVerdict::Agree);
    let rendered = report.render();
    assert!(rendered.contains("TESTED AGREEMENT"), "{rendered}");
    assert!(rendered.contains("never a theorem"), "{rendered}");
}

/// THE TRIANGLE'S REFUSAL CONTROL: the invalid control refuses on
/// BOTH legs (wasmtime's compiler AND wasmi's validator under the
/// shared profile — the negative control passing engine-portably).
#[test]
fn the_triangle_refuse_row_agrees_on_both_legs() {
    let report = run_triangle(&mandate_host::repo_gen_dir()).expect("the triangle runs");
    let invalid = report
        .rows
        .iter()
        .find(|r| r.path == "gen/wasm-duel/invalid.wasm")
        .expect("the invalid control row");
    assert_eq!(invalid.expectation, Expectation::Refuse);
    assert_eq!(invalid.verdict, TriVerdict::Agree);
}

/// THE TRIANGLE TOOTH: a doctored expectation diverges WITH THE
/// WITNESS naming the row (the wasmtime leg's true observation in the
/// wasmtime face — the scratch copy, never the committed universe).
#[test]
fn the_triangle_tamper_tooth_diverges_with_witness() {
    let gdir = scratch("triangle-tamper");
    retarget(&gdir, "gen/wasm-duel/op-i32.add.wasm", "run i64:43");

    let report = run_triangle(&gdir).expect("the triangle still runs");
    match report.verdict() {
        TriVerdict::Diverge { loc, lhs, wasmtime, wasmi } => {
            assert_eq!(loc, "gen/wasm-duel/op-i32.add.wasm");
            assert_eq!(lhs, "run i64:43", "lhs names the tampered expectation");
            assert_eq!(wasmtime, "i64:4294967294", "the wasmtime leg's true observation");
            assert_eq!(wasmi, "i64:4294967294", "the wasmi leg's true observation");
        }
        other => panic!("expected the divergence witness, got {other:?}"),
    }
}

//! FAULT INJECTION — corrupt/truncated forge job manifests
//! (review 2026-09-16 item 6).
//!
//! Injection surface: `src/jobs_generated.json` +
//! `src/faults_jobs_generated.json` — the ONLY files the forge binary
//! parses to decide what to run. The parser is a hand-rolled minimal
//! reader PRIVATE to the binary (`main.rs::load_jobs_of`), so the
//! honest test drives the REAL binary as a subprocess with
//! `DEVENV_ROOT` pointed at a tempdir holding corrupted manifest
//! copies. Asserts per case:
//!   (a) the run FAILS (nonzero exit),
//!   (b) the failure is the clean `forge: <err>` + `exit(1)` path —
//!       NOT a panic (exit 101) / abort (134) — and stderr names the
//!       manifest file or the corruption class,
//!   (c) statelessness: a separate run over the intact manifests gets
//!       PAST manifest loading (each run is its own process, so this
//!       is the strongest form).
//!
//! Resolutions from the 2026-09-17 injection run:
//!   - Truncated `outputs`/`args` lists were SILENTLY ACCEPTED (the
//!     `unterminated` error arms were dead code — `split(']').next()`
//!     always yields `Some`): FIXED in main.rs, pinned by
//!     `truncated_manifest_in_{outputs,args}_is_a_named_error`.
//!   - UNKNOWN extra fields are tolerated DELIBERATELY (additive
//!     tolerance — a newer emitter must not break an older forge);
//!     pinned as documentation by `unknown_field_is_tolerated_deliberately`.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Fail loud, fail clear (the house pattern: no bare `unwrap`).
#[track_caller]
#[allow(clippy::panic, reason = "test helper: fail loud, fail clear")]
fn fail(msg: &str) -> ! {
    panic!("{msg}");
}

/// The two generated manifests the binary loads (the `MANIFESTS`
/// constant in main.rs), keyed by their repo-root-relative path.
const MANIFESTS: &[&str] = &[
    "crates/forge/src/jobs_generated.json",
    "crates/forge/src/faults_jobs_generated.json",
];

/// Unique tempdir per test (the wasm-delta pattern).
fn tempdir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "forge-fault-{tag}-{}-{:x}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.subsec_nanos())
            .unwrap_or(0)
    ));
    std::fs::create_dir_all(&dir).unwrap_or_else(|e| fail(&format!("tempdir: {e}")));
    dir
}

/// A fake repo root with BOTH manifests copied in intact. Returns the
/// root; the caller then corrupts one file under it.
fn stage_root(tag: &str) -> PathBuf {
    let root = tempdir(tag);
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    for manifest in MANIFESTS {
        let file_name = Path::new(manifest).file_name().unwrap_or_else(|| fail("name"));
        let dst = root.join(manifest);
        std::fs::create_dir_all(dst.parent().unwrap_or_else(|| fail("parent")))
            .unwrap_or_else(|e| fail(&format!("mkdir: {e}")));
        std::fs::copy(src_dir.join(file_name), &dst)
            .unwrap_or_else(|e| fail(&format!("copy {manifest}: {e}")));
    }
    root
}

struct Run {
    code: i32,
    stdout: String,
    stderr: String,
}

/// Run the REAL forge binary against the staged root (no args = the
/// gen pipeline; a manifest failure aborts before any job runs).
fn run_forge(root: &Path) -> Run {
    let out = Command::new(env!("CARGO_BIN_EXE_forge"))
        .env("DEVENV_ROOT", root)
        .output()
        .unwrap_or_else(|e| fail(&format!("spawn forge: {e}")));
    Run {
        code: out.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&out.stdout).to_string(),
        stderr: String::from_utf8_lossy(&out.stderr).to_string(),
    }
}

/// (a)+(b): the run failed via the clean error path — exit 1, a
/// `forge:` diagnostic, no panic signature.
fn assert_clean_failure(run: &Run, what: &str) {
    assert_eq!(
        run.code, 1,
        "{what}: expected the clean exit(1) path, got code {} \
         (101 = panic, 134 = abort)\nstdout: {}\nstderr: {}",
        run.code, run.stdout, run.stderr
    );
    assert!(
        !run.stderr.contains("panicked"),
        "{what}: panic signature in stderr: {}",
        run.stderr
    );
    assert!(
        run.stderr.contains("forge:"),
        "{what}: the diagnostic must carry the forge prefix: {}",
        run.stderr
    );
}

/// (c) STATELESSNESS: the intact manifests get PAST loading — the
/// driver reaches the gen phase and prints its per-job lines (the jobs
/// themselves fail in the fake root: no lean/ tree, no lake targets —
/// that downstream failure is the CONTROL proving the manifests were
/// accepted and parsed into jobs).
fn assert_manifests_accepted(root: &Path, what: &str) {
    let run = run_forge(root);
    assert!(
        run.stdout.contains("forge: gen schema-lang"),
        "{what}: intact manifests must reach the gen phase\nstdout: {}\nstderr: {}",
        run.stdout,
        run.stderr
    );
    assert!(
        !run.stderr.contains("job missing") && !run.stderr.contains("ZERO jobs"),
        "{what}: intact manifests must not raise a manifest error: {}",
        run.stderr
    );
}

/// TRUNCATED manifest, cut MID-STRING (inside a field value): the
/// parser's `unterminated string` guard fires — a clean exit-1
/// diagnostic, no panic. (Naming gap: this one error does NOT carry
/// the manifest path, unlike the `job missing` family — reported.)
#[test]
fn truncated_manifest_mid_string_is_a_clean_error() {
    let root = stage_root("truncstr");
    let target = root.join(MANIFESTS[0]);
    let raw = std::fs::read_to_string(&target).unwrap_or_else(|e| fail(&format!("read: {e}")));
    // Cut inside the `"package": "schema-lang"` value.
    let needle = "\"package\": \"";
    let idx = raw.find(needle).unwrap_or_else(|| fail("needle"));
    std::fs::write(&target, &raw[..idx + needle.len() + 3])
        .unwrap_or_else(|e| fail(&format!("write: {e}")));

    let run = run_forge(&root);
    assert_clean_failure(&run, "truncated mid-string manifest");
    assert!(
        run.stderr.contains("unterminated string"),
        "the truncation class must be named: {}",
        run.stderr
    );

    // (c) statelessness.
    let good = stage_root("truncstr-control");
    assert_manifests_accepted(&good, "truncated-mid-string control");
    std::fs::remove_dir_all(&root).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
    std::fs::remove_dir_all(&good).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// TRUNCATED manifest, cut INSIDE THE OUTPUTS LIST: a hard parse
/// error naming the file AND the truncated key. (Regression pin: the
/// `unterminated outputs` arm was once DEAD CODE —
/// `str::split(']').next()` always yields `Some` — so this corruption
/// was silently accepted with a PREFIX of the committed outputs list,
/// weakening the byte-tie. Fixed in main.rs::load_jobs_of by requiring
/// the closing `]` in the field's raw slice.)
#[test]
fn truncated_manifest_in_outputs_is_a_named_error() {
    let root = stage_root("truncout");
    let target = root.join(MANIFESTS[0]);
    let raw = std::fs::read_to_string(&target).unwrap_or_else(|e| fail(&format!("read: {e}")));
    // Cut at 3/4: inside the single job's outputs list — after the
    // `"outputs": [` marker, before its closing `]` (the args list's
    // earlier `]` is irrelevant).
    let marker = "\"outputs\": [";
    let m = raw.find(marker).unwrap_or_else(|| fail("outputs marker"));
    let cut = raw.len() * 3 / 4;
    assert!(
        cut > m + marker.len() && !raw[m..cut].contains(']'),
        "the cut must land inside the outputs list"
    );
    std::fs::write(&target, &raw[..cut]).unwrap_or_else(|e| fail(&format!("write: {e}")));

    let run = run_forge(&root);
    assert_clean_failure(&run, "truncated outputs list");
    assert!(
        run.stderr.contains("jobs_generated.json") && run.stderr.contains("unterminated outputs"),
        "the error must name the file AND the truncated key: {}",
        run.stderr
    );

    // (c) statelessness.
    let good = stage_root("truncout-control");
    assert_manifests_accepted(&good, "truncated-outputs control");
    std::fs::remove_dir_all(&root).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
    std::fs::remove_dir_all(&good).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// TRUNCATED manifest, cut INSIDE THE ARGS list (the `"args": [`
/// marker present, no closing `]`): the same unterminated-list guard
/// on the optional field.
#[test]
fn truncated_manifest_in_args_is_a_named_error() {
    let root = stage_root("truncargs");
    let target = root.join(MANIFESTS[0]);
    let raw = std::fs::read_to_string(&target).unwrap_or_else(|e| fail(&format!("read: {e}")));
    let marker = "\"args\": [";
    let idx = raw.find(marker).unwrap_or_else(|| fail("args marker"));
    // Cut after the marker, before the list closes.
    let cut = idx + marker.len() + 2;
    assert!(!raw[..cut].contains(']'), "the cut must precede the closer");
    std::fs::write(&target, &raw[..cut]).unwrap_or_else(|e| fail(&format!("write: {e}")));

    let run = run_forge(&root);
    assert_clean_failure(&run, "truncated args list");
    assert!(
        run.stderr.contains("jobs_generated.json") && run.stderr.contains("unterminated args"),
        "the error must name the file AND the truncated key: {}",
        run.stderr
    );

    let good = stage_root("truncargs-control");
    assert_manifests_accepted(&good, "truncated-args control");
    std::fs::remove_dir_all(&root).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
    std::fs::remove_dir_all(&good).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// MISSING manifest file: the read error names the path.
#[test]
fn missing_manifest_file_is_a_named_error() {
    let root = stage_root("missing");
    std::fs::remove_file(root.join(MANIFESTS[1])).unwrap_or_else(|e| fail(&format!("rm: {e}")));

    let run = run_forge(&root);
    assert_clean_failure(&run, "missing manifest");
    assert!(
        run.stderr.contains("faults_jobs_generated.json"),
        "the error must NAME the missing file: {}",
        run.stderr
    );

    let good = stage_root("missing-control");
    assert_manifests_accepted(&good, "missing manifest control");
    std::fs::remove_dir_all(&root).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
    std::fs::remove_dir_all(&good).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// SCHEMA-WRONG, syntactically valid: a job with the `exe` field
/// deleted. Clean error naming the file AND the missing key.
#[test]
fn job_missing_field_is_a_named_error() {
    let root = stage_root("noexe");
    let target = root.join(MANIFESTS[0]);
    let raw = std::fs::read_to_string(&target).unwrap_or_else(|e| fail(&format!("read: {e}")));
    let corrupt = raw.replacen(r#""exe": "schema", "#, "", 1);
    assert_ne!(corrupt, raw, "the corruption must land");
    std::fs::write(&target, corrupt).unwrap_or_else(|e| fail(&format!("write: {e}")));

    let run = run_forge(&root);
    assert_clean_failure(&run, "missing exe field");
    assert!(
        run.stderr.contains("jobs_generated.json") && run.stderr.contains("missing `exe`"),
        "the error must name the file AND the missing key: {}",
        run.stderr
    );

    let good = stage_root("noexe-control");
    assert_manifests_accepted(&good, "missing-field control");
    std::fs::remove_dir_all(&root).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
    std::fs::remove_dir_all(&good).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// SCHEMA-WRONG TYPE: `outputs` as a bare string instead of a list.
/// Clean error naming the file AND the owning package.
#[test]
fn job_wrong_type_outputs_is_a_named_error() {
    let root = stage_root("wrongtype");
    let target = root.join(MANIFESTS[1]);
    let raw = std::fs::read_to_string(&target).unwrap_or_else(|e| fail(&format!("read: {e}")));
    let corrupt = raw.replacen(r#""outputs": ["#, r#""outputs": "#, 1);
    assert_ne!(corrupt, raw, "the corruption must land");
    std::fs::write(&target, corrupt).unwrap_or_else(|e| fail(&format!("write: {e}")));

    let run = run_forge(&root);
    assert_clean_failure(&run, "wrong-type outputs");
    assert!(
        run.stderr.contains("faults_jobs_generated.json") && run.stderr.contains("outputs"),
        "the error must name the file AND the outputs key: {}",
        run.stderr
    );

    let good = stage_root("wrongtype-control");
    assert_manifests_accepted(&good, "wrong-type control");
    std::fs::remove_dir_all(&root).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
    std::fs::remove_dir_all(&good).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// BOTH manifests parse to ZERO jobs: the driver's own guard fires —
/// "regenerate (just gen)", not an empty-run success.
#[test]
fn empty_manifests_are_refused_as_zero_jobs() {
    let root = stage_root("zero");
    for manifest in MANIFESTS {
        std::fs::write(root.join(manifest), "[]\n").unwrap_or_else(|e| fail(&format!("write: {e}")));
    }

    let run = run_forge(&root);
    assert_clean_failure(&run, "zero jobs");
    assert!(
        run.stderr.contains("ZERO jobs") && run.stderr.contains("just gen"),
        "the zero-jobs guard must name the remedy: {}",
        run.stderr
    );

    let good = stage_root("zero-control");
    assert_manifests_accepted(&good, "zero-jobs control");
    std::fs::remove_dir_all(&root).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
    std::fs::remove_dir_all(&good).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

/// DELIBERATE TOLERANCE (pinned as documentation, per the parser's
/// own comment): an UNKNOWN extra field on a job is silently accepted
/// — additive tolerance, so a newer emitter adding a field does not
/// break an older forge. The run reaches the gen phase with the extra
/// field present (the downstream job failure in the fake root is the
/// acceptance control). The byte-tie (`just gen --check`) owns drift
/// control for the committed manifest; the parser does not reject
/// unknown keys.
#[test]
fn unknown_field_is_tolerated_deliberately() {
    let root = stage_root("unknown");
    let target = root.join(MANIFESTS[1]);
    let raw = std::fs::read_to_string(&target).unwrap_or_else(|e| fail(&format!("read: {e}")));
    let corrupt = raw.replacen(r#""package": "faults""#, r#""bogus": "x", "package": "faults""#, 1);
    assert_ne!(corrupt, raw, "the corruption must land");
    std::fs::write(&target, corrupt).unwrap_or_else(|e| fail(&format!("write: {e}")));

    let run = run_forge(&root);
    // Deliberate: no manifest error — the driver ACCEPTED the unknown
    // field and advanced to the gen phase (jobs then fail in the fake
    // root, which is the acceptance control, not the assertion).
    assert!(
        run.stdout.contains("forge: gen faults"),
        "tolerance pinned: the unknown field passed the parser — the \
         driver reached the gen phase\nstdout: {}\nstderr: {}",
        run.stdout,
        run.stderr
    );
    assert!(
        !run.stderr.contains("job missing") && !run.stderr.contains("panicked"),
        "the acceptance must be silent (no manifest error, no panic): {}",
        run.stderr
    );

    std::fs::remove_dir_all(&root).unwrap_or_else(|e| fail(&format!("cleanup: {e}")));
}

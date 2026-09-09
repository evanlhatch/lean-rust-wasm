//! forge — the codegen pipeline orchestrator.
//!
//! Owns: invoking Lean emitters (`lake build` + `lake exe` per package),
//! byte-tie checking (`gen --check`), the OCI layout store, and later:
//! component linking, splice orchestration.
//!
//! Never contains: emitters (Lean owns those — they read the elaborated
//! environment), devenv logic (shell stays thin).

mod oci;

// GENERATED driver surface (byte-tied): the pipeline stage machine.
// (path is relative to THIS file's dir: crates/forge/src)
#[path = "../../../src/pipeline_generated.rs"]
pub mod pipeline_generated;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use pipeline_generated::{PipelineEvent, PipelineStage};

/// One codegen job: a Lean package whose generator exe writes committed
/// artifacts (repo-root-relative paths). One writer per artifact (the
/// audit) — an output path belongs to exactly one job.
struct Job {
    /// Directory under `lean/`.
    package: String,
    /// `lake build` target + `lake exe` name.
    exe: String,
    /// Committed artifacts this job owns (repo-root-relative).
    outputs: Vec<String>,
}

/// The jobs the driver runs: LOADED from the generated manifest
/// (`jobs_generated.json`), not hand-copied. The hand-written table this
/// replaces had drifted — registered emitters whose artifacts were never
/// byte-tied. The manifest is itself byte-tied (`just gen --check`), and
/// the Lean-side consistency test (`jobsCoverEmitters`) fails CI on
/// registry/manifest drift.
const MANIFESTS: &[&str] = &[
    "crates/forge/src/jobs_generated.json",
    "crates/forge/src/faults_jobs_generated.json",
];

fn load_jobs(root: &Path) -> Result<Vec<Job>, String> {
    let mut jobs = Vec::new();
    for manifest in MANIFESTS {
        jobs.extend(load_jobs_of(root, manifest)?);
    }
    if jobs.is_empty() {
        return Err("job manifests parsed to ZERO jobs — regenerate (just gen)".into());
    }
    Ok(jobs)
}

/// Parse one package's manifest file (generated; see MANIFESTS).
fn load_jobs_of(root: &Path, manifest: &str) -> Result<Vec<Job>, String> {
    let raw = fs::read_to_string(root.join(manifest)).map_err(|e| format!("{manifest}: {e}"))?;
    // Strip the GENERATED header (comment lines) — JSON has no comments.
    let json = raw
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .collect::<Vec<_>>()
        .join("\n");
    // Minimal parse: the manifest is generated, single-line objects, one
    // key-set shape ("package"/"exe" strings + an "outputs" string list).
    let mut jobs = Vec::new();
    for obj in json.split("{").skip(1) {
        let string_val = |key: &str| -> Result<String, String> {
            let needle = format!("\"{key}\": \"");
            let idx = obj
                .find(&needle)
                .ok_or_else(|| format!("{manifest}: job missing `{key}`"))?;
            let rest = &obj[idx + needle.len()..];
            let end = rest.find('"').ok_or("unterminated string")?;
            Ok(rest[..end].to_string())
        };
        let package = string_val("package")?;
        let exe = string_val("exe")?;
        let outputs: Vec<String> = obj
            .split("\"outputs\": [")
            .nth(1)
            .ok_or_else(|| format!("{manifest}: job missing outputs ({package})"))?
            .split(']')
            .next()
            .ok_or("unterminated outputs")?
            .split(", ")
            .map(|s| s.trim().trim_matches('"').to_string())
            .filter(|s| !s.is_empty())
            .collect();
        jobs.push(Job {
            package,
            exe,
            outputs,
        });
    }
    Ok(jobs)
}

/// The driver's stage machine, in its Lean-proved form: `step` returns
/// `None` on an illegal transition. `None` here is a DRIVER BUG (the
/// pipeline machine is deadlock-free over its own phases) — abort loudly
/// instead of running stages out of order.
fn advance(stage: PipelineStage, e: PipelineEvent, what: &str) -> PipelineStage {
    match pipeline_generated::step(stage, e) {
        Some(s) => s,
        None => {
            eprintln!("forge: ILLEGAL pipeline transition at {what}: {stage:?} -{e:?}-> None");
            std::process::exit(1);
        }
    }
}

fn lean_tc() -> PathBuf {
    if let Ok(tc) = std::env::var("LEAN_TC") {
        return PathBuf::from(tc);
    }
    let version = "leanprover--lean4---v4.33.0";
    let home = std::env::var("HOME").expect("HOME unset");
    PathBuf::from(home)
        .join(".elan/toolchains")
        .join(version)
        .join("bin")
}

fn repo_root() -> PathBuf {
    PathBuf::from(std::env::var("DEVENV_ROOT").unwrap_or_else(|_| ".".into()))
}

fn run(cmd: &mut Command, what: &str) -> Result<(), String> {
    let status = cmd.status().map_err(|e| format!("{what}: {e}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("{what}: exited {status}"))
    }
}

/// Build + run one generator exe. CWD is the lean package dir; the exe
/// writes repo-root-relative paths (GenMain convention).
fn run_job(tc: &Path, root: &Path, job: &Job) -> Result<(), String> {
    let pkg_dir = root.join("lean").join(&job.package);
    let lake = tc.join("lake");
    let mut path = std::env::var("PATH").unwrap_or_default();
    path = format!("{}:{}", tc.display(), path);
    run(
        Command::new(&lake)
            .arg("build")
            .arg(&job.exe)
            .current_dir(&pkg_dir)
            .env("PATH", &path),
        &format!("lake build {}", job.exe),
    )?;
    run(
        Command::new(&lake)
            .arg("exe")
            .arg(&job.exe)
            .current_dir(&pkg_dir)
            .env("PATH", &path),
        &format!("lake exe {}", job.exe),
    )
}

fn read_if_exists(p: &Path) -> Option<Vec<u8>> {
    fs::read(p).ok()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let check = args.iter().any(|a| a == "--check");
    let store_artifacts = args.iter().any(|a| a == "--store");
    let tc = lean_tc();
    let root = repo_root();

    // Initialize the OCI store (lazy — only used with --store, and
    // read-only for drift checks with --check).
    let oci_root = root.join("target/oci");
    let mut store = oci::OciStore::open(&oci_root).expect("oci store init");

    let jobs = match load_jobs(&root) {
        Ok(j) => j,
        Err(e) => {
            eprintln!("forge: {e}");
            std::process::exit(1);
        }
    };

    // The driver's own phases run through the GENERATED stage machine —
    // the same one Lean proves acyclic (`rank_advances`). Illegal
    // transitions abort (`advance`): a driver that fires `tie` before
    // `emit` is a bug, not a degraded mode.
    let mut stage = PipelineStage::Idle;
    stage = advance(stage, PipelineEvent::Reflect, "gen loop");

    if !check {
        let mut failed = false;
        for job in &jobs {
            println!(
                "forge: gen {} ({} artifacts)",
                job.package,
                job.outputs.len()
            );
            if let Err(e) = run_job(&tc, &root, job) {
                eprintln!("forge: FAIL {e}");
                failed = true;
            }
        }
        stage = advance(stage, PipelineEvent::Check, "lean elaboration");
        stage = advance(stage, PipelineEvent::Emit, "lean emitters");
        if store_artifacts {
            // Collect (label, path) pairs for every artifact.
            let mut pairs: Vec<(String, PathBuf)> = Vec::new();
            for job in &jobs {
                for out in &job.outputs {
                    let path = root.join(out);
                    if path.exists() {
                        pairs.push((out.clone(), path));
                    }
                }
            }
            let pair_refs: Vec<(&str, &Path)> = pairs
                .iter()
                .map(|(l, p)| (l.as_str(), p.as_path()))
                .collect();
            match oci::store_artifacts(&mut store, &pair_refs) {
                Ok(digests) => {
                    for (label, digest) in &digests {
                        println!("forge: oci {label} → {digest}");
                    }
                    // OCI-level byte-tie: re-read each blob from the
                    // store and verify against the file. The file is
                    // the authority; the store is the cache.
                    let mut verify_failed = false;
                    for (label, path) in &pairs {
                        match store.verify(label, path) {
                            Ok(oci::Verify::Match) => {
                                println!("forge: oci verify {label}: ok");
                            }
                            Ok(oci::Verify::NotStored) => {
                                eprintln!("forge: oci verify {label}: not stored");
                                verify_failed = true;
                            }
                            Ok(oci::Verify::Mismatch { stored, actual }) => {
                                eprintln!(
                                    "forge: oci verify {label}: DRIFT stored {stored} != file {actual}"
                                );
                                verify_failed = true;
                            }
                            Err(e) => {
                                eprintln!("forge: oci verify {label}: {e}");
                                verify_failed = true;
                            }
                        }
                    }
                    if verify_failed {
                        std::process::exit(1);
                    }
                }
                Err(e) => {
                    eprintln!("forge: oci store: {e}");
                    std::process::exit(1);
                }
            }
            match store.write_index() {
                Ok(()) => println!("forge: oci index written"),
                Err(e) => eprintln!("forge: oci index: {e}"),
            }
        }
        std::process::exit(if failed { 1 } else { 0 });
    }

    // Byte-tie: snapshot outputs, regenerate, compare. A mismatch is
    // drift — regenerate with `just gen`, never hand-edit.
    stage = advance(stage, PipelineEvent::Check, "lean elaboration");
    stage = advance(stage, PipelineEvent::Emit, "lean emitters");
    stage = advance(stage, PipelineEvent::Tie, "byte-tie");

    let mut drifted = Vec::new();
    for job in &jobs {
        let before: Vec<Option<Vec<u8>>> = job
            .outputs
            .iter()
            .map(|o| read_if_exists(&root.join(o)))
            .collect();
        if let Err(e) = run_job(&tc, &root, job) {
            eprintln!("forge: FAIL {e}");
            std::process::exit(1);
        }
        for (out, old) in job.outputs.iter().zip(before) {
            let new = read_if_exists(&root.join(out));
            if old != new {
                drifted.push(out.clone());
            }
            // OCI-level byte-tie: if the store has a digest for this
            // artifact and the current file's hash doesn't match,
            // that's drift too (file drifted after the last --store).
            match store.verify(out, &root.join(out)) {
                Ok(oci::Verify::Mismatch { stored, actual }) => {
                    eprintln!("forge: oci {out}: stored {stored} != file {actual}");
                    if !drifted.contains(out) {
                        drifted.push(out.clone());
                    }
                }
                Ok(_) => {}
                Err(e) => eprintln!("forge: oci verify {out}: {e}"),
            }
        }
    }
    if drifted.is_empty() {
        println!("forge: byte-tie clean ({} jobs)", jobs.len());
    } else {
        for p in &drifted {
            eprintln!("forge: DRIFT {p} differs from committed artifact");
        }
        eprintln!("forge: run `just gen` to regenerate; never hand-edit GENERATED files");
        std::process::exit(1);
    }
}

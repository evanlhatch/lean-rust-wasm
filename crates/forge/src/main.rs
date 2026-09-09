//! forge — the codegen pipeline orchestrator.
//!
//! Owns: invoking Lean emitters (`lake build` + `lake exe` per package),
//! byte-tie checking (`gen --check`), the OCI layout store, and later:
//! component linking, splice orchestration.
//!
//! Never contains: emitters (Lean owns those — they read the elaborated
//! environment), devenv logic (shell stays thin).

mod oci;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// One codegen job: a Lean package whose generator exe writes committed
/// artifacts (repo-root-relative paths). One writer per artifact (the
/// audit) — an output path belongs to exactly one job.
struct Job {
    /// Directory under `lean/`.
    package: &'static str,
    /// `lake build` target + `lake exe` name.
    exe: &'static str,
    /// Committed artifacts this job owns.
    outputs: &'static [&'static str],
}

const JOBS: &[Job] = &[
    Job {
        package: "schema-lang",
        exe: "schema-gen",
        outputs: &["wit/gateway.wit", "src/schema_generated.rs", "src/vortex_generated.rs"],
    },
    Job {
        package: "faults",
        exe: "faults-gen",
        outputs: &["src/faults_generated.rs", "src/host_faults_generated.rs"],
    },
];

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
    let pkg_dir = root.join("lean").join(job.package);
    let lake = tc.join("lake");
    let mut path = std::env::var("PATH").unwrap_or_default();
    path = format!("{}:{}", tc.display(), path);
    run(
        Command::new(&lake)
            .arg("build")
            .arg(job.exe)
            .current_dir(&pkg_dir)
            .env("PATH", &path),
        &format!("lake build {}", job.exe),
    )?;
    run(
        Command::new(&lake)
            .arg("exe")
            .arg(job.exe)
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

    if !check {
        let mut failed = false;
        for job in JOBS {
            println!("forge: gen {} ({} artifacts)", job.package, job.outputs.len());
            if let Err(e) = run_job(&tc, &root, job) {
                eprintln!("forge: FAIL {e}");
                failed = true;
            }
        }
        if store_artifacts {
            // Collect (label, path) pairs for every artifact.
            let mut pairs: Vec<(&str, PathBuf)> = Vec::new();
            for job in JOBS {
                for out in job.outputs {
                    let path = root.join(out);
                    if path.exists() {
                        pairs.push((out, path));
                    }
                }
            }
            let pair_refs: Vec<(&str, &Path)> =
                pairs.iter().map(|(l, p)| (*l, p.as_path())).collect();
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
    let mut drifted = Vec::new();
    for job in JOBS {
        let before: Vec<Option<Vec<u8>>> =
            job.outputs.iter().map(|o| read_if_exists(&root.join(o))).collect();
        if let Err(e) = run_job(&tc, &root, job) {
            eprintln!("forge: FAIL {e}");
            std::process::exit(1);
        }
        for (out, old) in job.outputs.iter().zip(before) {
            let new = read_if_exists(&root.join(out));
            if old != new {
                drifted.push(*out);
            }
            // OCI-level byte-tie: if the store has a digest for this
            // artifact and the current file's hash doesn't match,
            // that's drift too (file drifted after the last --store).
            match store.verify(out, &root.join(out)) {
                Ok(oci::Verify::Mismatch { stored, actual }) => {
                    eprintln!("forge: oci {out}: stored {stored} != file {actual}");
                    if !drifted.contains(out) {
                        drifted.push(out);
                    }
                }
                Ok(_) => {}
                Err(e) => eprintln!("forge: oci verify {out}: {e}"),
            }
        }
    }
    if drifted.is_empty() {
        println!("forge: byte-tie clean ({} jobs)", JOBS.len());
    } else {
        for p in &drifted {
            eprintln!("forge: DRIFT {p} differs from committed artifact");
        }
        eprintln!("forge: run `just gen` to regenerate; never hand-edit GENERATED files");
        std::process::exit(1);
    }
}

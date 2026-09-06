//! forge — the codegen pipeline orchestrator.
//!
//! Owns: invoking Lean emitters (`lake build` + `lake exe` per package),
//! byte-tie checking (`gen --check`), and later: component linking, OCI
//! layout. Logic lives here; just/devenv stay thin shims.
//!
//! Never contains: emitters (Lean owns those — they read the elaborated
//! environment), devenv logic (shell stays thin).

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

const JOBS: &[Job] = &[Job {
    package: "schema-lang",
    exe: "schema-gen",
    outputs: &["wit/gateway.wit", "src/schema_generated.rs"],
  },
  Job {
    package: "faults",
    exe: "faults-gen",
    outputs: &["src/faults_generated.rs"],
}];

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
    let check = std::env::args().any(|a| a == "--check");
    let tc = lean_tc();
    let root = repo_root();

    if !check {
        let mut failed = false;
        for job in JOBS {
            println!("forge: gen {} ({} artifacts)", job.package, job.outputs.len());
            if let Err(e) = run_job(&tc, &root, job) {
                eprintln!("forge: FAIL {e}");
                failed = true;
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

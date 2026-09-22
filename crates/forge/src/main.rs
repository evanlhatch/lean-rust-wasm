//! forge — the codegen pipeline orchestrator.
//!
//! Owns: invoking Lean emitters (`lake build` + `lake exe` per package),
//! byte-tie checking (`gen --check`), the OCI layout store, and later:
//! component linking, splice orchestration.
//!
//! Never contains: emitters (Lean owns those — they read the elaborated
//! environment), devenv logic (shell stays thin).

// error! emits Error::provide — nightly-only (same gate as the root crate).
#![feature(error_generic_member_access)]

#[global_allocator]
static GLOBAL_ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

use forge::oci;

// GENERATED driver surface (byte-tied): the pipeline stage machine.
// (path is relative to THIS file's dir: crates/forge/src)
#[path = "../../../generated/rust/pipeline_generated.rs"]
pub mod pipeline_generated;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use fast_observe::exn::Fault;
use pipeline_generated::{PipelineEvent, PipelineStage};

// The driver's fault domain (fast-observe is the error tool — the
// valves.rs pattern, local to this bin): manifest loads/parses, lake
// subprocess runs, and the driver's own environment/usage. F-space
// codes — the Lean faults registry owns E1xx; no collision. The message
// text rides `detail` (bare `{detail}` Display) so the driver's
// `forge: <diagnostic>` stderr lines stay byte-identical — the
// fault-injection suite pins their content. EXCLUDED from this
// conversion: the io Result channels in oci.rs (tests consume them);
// they map at this driver's seam.
fast_observe::error! {
    /// A forge driver fault: a failed manifest, subprocess, or
    /// environment problem.
    #[derive(Debug)]
    pub enum ForgeFault {
        /// A generated job manifest failed to load or parse (the byte-tie
        /// domain — never hand-edit GENERATED files).
        #[error("{detail}")]
        #[code = "F101", category = Content, advice = "regenerate with `just gen`; never hand-edit GENERATED files"]
        Manifest {
            detail: String,
        },

        /// A lake subprocess failed (build or exe run).
        #[error("{detail}")]
        #[code = "F102", category = Transient, advice = "re-run the failed job; the lake output names the cause"]
        Subprocess {
            detail: String,
        },

        /// The driver's environment or CLI usage is wrong.
        #[error("{detail}")]
        #[code = "F104", category = Content, advice = "fix the environment or arguments named in the detail"]
        Environment {
            detail: String,
        },
    }
}

/// The driver's fallible flow: fast-observe faults over [`ForgeFault`].
type DriverResult<T> = fast_observe::Result<T, ForgeFault>;

/// One codegen job: a Lean package whose generator exe writes committed
/// artifacts (repo-root-relative paths). One writer per artifact (the
/// audit) — an output path belongs to exactly one job.
struct Job {
    /// Directory under `lean/`.
    package: String,
    /// `lake build` target + `lake exe` name.
    exe: String,
    /// Args forwarded to the exe (e.g. the subcommand for consolidated
    /// drivers: exe `schema`, args `["gen"]`). Absent in the manifest = [].
    args: Vec<String>,
    /// Committed artifacts this job owns (repo-root-relative).
    outputs: Vec<String>,
}

/// The jobs the driver runs: LOADED from the generated manifest
/// (`jobs_generated.json`), not hand-copied. The hand-written table this
/// replaces had drifted — registered emitters whose artifacts were never
/// byte-tied. The manifest is itself byte-tied (`just gen --check`), and
/// the Lean-side consistency test (`jobsCoverEmitters`) fails CI on
/// registry/manifest drift.
// Cross-language mirror of the same manifest set: the Lean side lives as
// `forgeJobManifests` in lean/LintKit/LintKit/Runner.lean — same paths, no
// shared const; keep the two in lockstep when the manifest set changes.
const MANIFESTS: &[&str] = &[
    "generated/json/jobs_generated.json",
    "generated/json/faults_jobs_generated.json",
];

fn load_jobs(root: &Path) -> DriverResult<Vec<Job>> {
    let mut jobs = Vec::new();
    for manifest in MANIFESTS {
        jobs.extend(load_jobs_of(root, manifest)?);
    }
    if jobs.is_empty() {
        return Err(ForgeFault::Manifest(Manifest {
            detail: "job manifests parsed to ZERO jobs — regenerate (just gen)".into(),
        })
        .into());
    }
    Ok(jobs)
}

/// Parse one package's manifest file (generated; see MANIFESTS).
///
/// serde_json does the parsing (the hand-rolled string scan it replaced
/// had the dead-code truncation bug the fault-injection suite caught);
/// the DIAGNOSTICS stay byte-compatible with it — the fault-injection
/// suite pins the corruption classes:
///   - truncated inside a list    → `unterminated {args,outputs} (job)`
///   - truncated inside a string  → `unterminated string`
///   - `outputs` absent/non-list  → `job missing outputs (job)`
/// Unknown fields are TOLERATED deliberately (additive tolerance): a
/// newer emitter adding a field must not break an older forge — the
/// byte-tie (`just gen --check`) owns drift control, not the parser.
fn load_jobs_of(root: &Path, manifest: &str) -> DriverResult<Vec<Job>> {
    // The io error rides the tree as the wrapped original AND in `detail`
    // (the pinned diagnostic names the file + the cause).
    let raw = fs::read_to_string(root.join(manifest)).map_err(|e| {
        let detail = format!("{manifest}: {e}");
        Fault::new(e).wrap(ForgeFault::Manifest(Manifest { detail }))
    })?;
    // Strip the GENERATED header (comment lines) — JSON has no comments.
    let json = raw
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .collect::<Vec<_>>()
        .join("\n");
    // The generated shape is a JSON array of job objects; a truncated
    // tail surfaces as a parse error classified against the UNPARSED
    // tail (the raw text after the last fully consumed value).
    let mut jobs = Vec::new();
    let mut consumed = 0usize;
    let mut stream = serde_json::Deserializer::from_str(&json).into_iter::<serde_json::Value>();
    while let Some(item) = stream.next() {
        match item {
            Ok(value) => {
                consumed = stream.byte_offset();
                match value {
                    serde_json::Value::Array(elements) => {
                        for element in elements {
                            jobs.push(job_from_value(manifest, element)?);
                        }
                    }
                    // A bare object (no array wrap) — the old scanner
                    // tolerated both shapes; keep the tolerance.
                    element => jobs.push(job_from_value(manifest, element)?),
                }
            }
            Err(e) => {
                let tail = json.get(consumed..).unwrap_or("");
                return Err(ForgeFault::Manifest(Manifest {
                    detail: format!("{manifest}: {}", truncation_class(tail, &e)),
                })
                .into());
            }
        }
    }
    Ok(jobs)
}

/// Name the corruption class in the UNPARSED tail (the fault-injection
/// suite's pins). The generated shape is known — `package`/`args`/
/// `outputs` — so the tail's raw text is enough to name the owning job
/// and the truncated key (the old scanner's diagnostics, kept verbatim).
fn truncation_class(tail: &str, err: &serde_json::Error) -> String {
    // The owning job's `package`, for the error text (diagnostic only —
    // the structural parse is serde's above).
    let package = || {
        tail.split("\"package\": \"")
            .nth(1)
            .and_then(|rest| rest.find('"').map(|end| &rest[..end]))
            .unwrap_or("?")
    };
    // A list field is truncated when its opening `[` has no closing `]`
    // after it in the tail (args precedes outputs in the generated
    // objects, so an outputs cut leaves args' `]` intact — no ambiguity).
    let unterminated_list = |key: &str| -> Option<String> {
        let marker = format!("\"{key}\": [");
        let idx = tail.find(&marker)?;
        tail[idx + marker.len()..]
            .find(']')
            .is_none()
            .then(|| format!("unterminated {key} ({})", package()))
    };
    if let Some(class) = unterminated_list("args") {
        return class;
    }
    if let Some(class) = unterminated_list("outputs") {
        return class;
    }
    // `outputs` as a non-list (a bare string where the list belongs).
    if tail.contains("\"outputs\": \"") {
        return format!("job missing outputs ({})", package());
    }
    if err.to_string().contains("EOF while parsing a string") {
        return "unterminated string".into();
    }
    format!("truncated manifest ({err})")
}

/// Extract one [`Job`] from a parsed manifest object. Schema errors name
/// the manifest file + the offending key (the pinned `job missing` family).
fn job_from_value(manifest: &str, value: serde_json::Value) -> DriverResult<Job> {
    let obj = value.as_object().ok_or_else(|| {
        ForgeFault::Manifest(Manifest {
            detail: format!("{manifest}: job is not an object"),
        })
    })?;
    let string_field = |key: &str| -> core::result::Result<String, ForgeFault> {
        obj.get(key)
            .and_then(|v| v.as_str())
            .map(String::from)
            .ok_or_else(|| {
                ForgeFault::Manifest(Manifest {
                    detail: format!("{manifest}: job missing `{key}`"),
                })
            })
    };
    let package = string_field("package")?;
    let exe = string_field("exe")?;
    // Optional subcommand args (absent = none; a non-list also reads as
    // none — the generated shape never emits one, and the old scanner
    // tolerated the shape).
    let args: Vec<String> = obj
        .get("args")
        .and_then(|v| v.as_array())
        .map(|list| {
            list.iter()
                .filter_map(|v| v.as_str().map(String::from))
                .collect()
        })
        .unwrap_or_default();
    // The outputs list is NOT optional: absent or non-list = a named
    // error (the fault-injection suite pins the wrong-type class).
    let outputs: Vec<String> = obj
        .get("outputs")
        .and_then(|v| v.as_array())
        .map(|list| {
            list.iter()
                .filter_map(|v| v.as_str().map(String::from))
                .collect()
        })
        .ok_or_else(|| {
            ForgeFault::Manifest(Manifest {
                detail: format!("{manifest}: job missing outputs ({package})"),
            })
        })?;
    Ok(Job {
        package,
        exe,
        args,
        outputs,
    })
}

/// The driver's stage machine, in its Lean-proved form: `step` returns
/// `None` on an illegal transition. `None` here is a DRIVER BUG (the
/// pipeline machine is deadlock-free over its own phases) — abort loudly
/// instead of running stages out of order. DELIBERATE INVARIANT (audit
/// class (a)): the Lean-proved machine never returns None over its own
/// phases, so this abort is unreachable by construction — kept as a
/// loud exit (not an error path) for exactly that reason.
fn advance(stage: PipelineStage, e: PipelineEvent, what: &str) -> PipelineStage {
    match pipeline_generated::step(stage, e) {
        Some(s) => s,
        None => {
            eprintln!("forge: ILLEGAL pipeline transition at {what}: {stage:?} -{e:?}-> None");
            std::process::exit(1);
        }
    }
}

fn lean_tc() -> DriverResult<PathBuf> {
    if let Ok(tc) = std::env::var("LEAN_TC") {
        return Ok(PathBuf::from(tc));
    }
    let version = "leanprover--lean4---v4.33.0";
    let home = std::env::var("HOME").map_err(|_| {
        ForgeFault::Environment(Environment {
            detail: "HOME unset — cannot locate the elan toolchain (set LEAN_TC or HOME)".into(),
        })
    })?;
    Ok(PathBuf::from(home)
        .join(".elan/toolchains")
        .join(version)
        .join("bin"))
}

fn repo_root() -> PathBuf {
    PathBuf::from(std::env::var("DEVENV_ROOT").unwrap_or_else(|_| ".".into()))
}

fn run(cmd: &mut Command, what: &str) -> DriverResult<()> {
    // The io error (spawn failure) rides the tree as the wrapped original
    // AND in `detail` (the diagnostic carries the command label + cause).
    let status = cmd.status().map_err(|e| {
        let detail = format!("{what}: {e}");
        Fault::new(e).wrap(ForgeFault::Subprocess(Subprocess { detail }))
    })?;
    if status.success() {
        Ok(())
    } else {
        Err(ForgeFault::Subprocess(Subprocess {
            detail: format!("{what}: exited {status}"),
        })
        .into())
    }
}

/// Build + run one generator exe. CWD is the lean package dir; the exe
/// writes repo-root-relative paths (GenMain convention).
/// SINGLE-LAKE (notes/single-lake-migration.md §7): the leaf lakefiles
/// are deleted (the root lakefile is the workspace), so lake needs
/// `--dir ../..` (the root workspace) and the CWD stays at the package
/// dir for the exe's cwd-relative writes (the §7 gen-exe rule).
fn run_job(tc: &Path, root: &Path, job: &Job) -> DriverResult<()> {
    let pkg_dir = root.join("lean").join(&job.package);
    let lake = tc.join("lake");
    let mut path = std::env::var("PATH").unwrap_or_default();
    path = format!("{}:{}", tc.display(), path);
    run(
        Command::new(&lake)
            .arg("--dir")
            .arg("../..")
            .arg("build")
            .arg(&job.exe)
            .current_dir(&pkg_dir)
            .env("PATH", &path),
        &format!("lake build {}", job.exe),
    )?;
    run(
        Command::new(&lake)
            .arg("--dir")
            .arg("../..")
            .arg("exe")
            .arg(&job.exe)
            .args(&job.args)
            .current_dir(&pkg_dir)
            .env("PATH", &path),
        &format!("lake exe {} {:?}", job.exe, job.args),
    )
}

fn read_if_exists(p: &Path) -> Option<Vec<u8>> {
    fs::read(p).ok()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let check = args.iter().any(|a| a == "--check");
    let store_artifacts = args.iter().any(|a| a == "--store");
    // The clean-error paths below keep the pinned failure contract:
    // exit 1 + a `forge:` diagnostic, never a panic (the fault-injection
    // suite asserts this shape on every manifest corruption).
    let tc = match lean_tc() {
        Ok(tc) => tc,
        Err(e) => {
            eprintln!("forge: {e}");
            std::process::exit(1);
        }
    };
    let root = repo_root();

    // Initialize the OCI store (lazy — only used with --store, and
    // read-only for drift checks with --check).
    let oci_root = root.join("cache/oci");
    let mut store = match oci::OciStore::open(&oci_root) {
        Ok(store) => store,
        Err(e) => {
            eprintln!("forge: oci store init: {e}");
            std::process::exit(1);
        }
    };

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
            // THE CONTENT-ONLY COMPARE: the header = the metadata (the
            // timestamp/git state change per regen) — the strip on both
            // sides; the byte-tie = the content's authority.
            let old_c = old.as_deref().map(forge::oci::OciStore::strip_header);
            let new_c = new.as_deref().map(forge::oci::OciStore::strip_header);
            if old_c != new_c {
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

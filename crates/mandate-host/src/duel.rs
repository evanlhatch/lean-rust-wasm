//! The duel runner — the HOST half of the wasm execution duel.
//!
//! THE DUEL (WasmCore.Duel — the Lean half): a vector set of
//! (module-input, expected-output) rows over the slice module + the
//! grown family (arithmetic / control flow / memory / the trap row /
//! the invalid control). The LEAN side computed each expected output
//! by RUNNING its executor and committed the manifest + the vectors
//! through the artifact spine; THIS side executes the same bytes in
//! the real wasmtime engine and answers per row:
//!
//! - `agree` — the engines agree (a regression row);
//! - `diverge` — they disagree; the witness names the row AND BOTH
//!   values (the expectation vs the engine's observation);
//! - `refused` — a typed refusal: EXPECTED (the invalid control —
//!   the negative control passing) or unexpected (the witness).
//!
//! THE TIER HONESTY (notes/v3/04-verification.md §6): the duel's
//! verdict is TESTED AGREEMENT — `oracleSwept`, a regression surface,
//! NEVER a theorem over unbounded inputs. `DuelReport::render` says
//! so verbatim; the verdicts are typed ctors, never strings (the
//! Verdict discipline's Rust face).
//!
//! THE SKEW DISCIPLINE PER VECTOR: every vector is hash-tied to its
//! own committed `.hdr` sidecar (the binary lane's discipline) BEFORE
//! the engine sees a byte — a tampered vector refuses, typed.
//!
//! ERROR DISCIPLINE (12 §8): no bare panics on real error paths —
//! every failure is a [`crate::HostError`].

use std::path::{Path, PathBuf};

use wasmtime::Trap;

use crate::artifact::bytes_hash;
use crate::{HostError, engine::{export_i64, instantiate_core_module}};

/// The manifest's path inside the duel directory.
const MANIFEST: &str = "manifest.txt";

/// The consumer-side expectation (the manifest's second column —
/// `Kit.Duel.Expect`'s Rust face: `run <result>` / `trap` / `refuse`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expectation {
    /// MUST execute to completion and return the pinned result values
    /// (the duel's value vocabulary, e.g. `i64:42`).
    Run(String),
    /// MUST trap — the typed wasm trap, in every engine.
    Trap,
    /// MUST be refused (the invalid control: Lean's validator refuses
    /// it at generation; wasmtime's compiler must refuse it here).
    Refuse,
}

impl Expectation {
    /// Parses one expectation column. `None` = unknown vocabulary —
    /// the caller refuses (a malformed manifest, never a guess).
    fn parse(s: &str) -> Option<Expectation> {
        if s == "trap" {
            return Some(Expectation::Trap);
        }
        if s == "refuse" {
            return Some(Expectation::Refuse);
        }
        s.strip_prefix("run ").map(|r| Expectation::Run(r.to_string()))
    }
}

/// One row's verdict (Kit.Duel.Verdict's Rust face — ctors, never
/// strings). `diverge` carries the WITNESS: which row, what each side
/// observed (`lhs` = the manifest's expectation, `rhs` = the engine's
/// observation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RowVerdict {
    Agree,
    Diverge { loc: String, lhs: String, rhs: String },
    Refused { why: String },
}

impl RowVerdict {
    /// The report line's verdict face.
    pub fn render(&self) -> String {
        match self {
            RowVerdict::Agree => "agree".to_string(),
            RowVerdict::Diverge { loc, lhs, rhs } => {
                format!("diverge at {loc}: expected {lhs}, host observed {rhs}")
            }
            RowVerdict::Refused { why } => format!("refused: {why}"),
        }
    }
}

/// One duel row's outcome.
#[derive(Debug, Clone)]
pub struct DuelRow {
    /// The vector path (the manifest's first column).
    pub path: String,
    /// The expectation this row ran under.
    pub expectation: Expectation,
    /// The verdict.
    pub verdict: RowVerdict,
}

/// The duel's report: every row's verdict + the honest tier. This is
/// TESTED AGREEMENT — never a theorem, and the rendering says so.
#[derive(Debug, Clone)]
pub struct DuelReport {
    /// The manifest's `generator` provenance row.
    pub generator: String,
    /// The rows, manifest order.
    pub rows: Vec<DuelRow>,
}

/// The counts over any duel's rows: (agree, diverge, refused) — the
/// fold the reports' renderings share (ONE copy for every duel lane).
pub(crate) fn verdict_counts<'a, I: IntoIterator<Item = (&'a str, &'a RowVerdict)>>(
    rows: I,
) -> (usize, usize, usize) {
    let mut a = 0;
    let mut d = 0;
    let mut r = 0;
    for (_, v) in rows {
        match v {
            RowVerdict::Agree => a += 1,
            RowVerdict::Diverge { .. } => d += 1,
            RowVerdict::Refused { .. } => r += 1,
        }
    }
    (a, d, r)
}

/// THE duel verdict fold (Kit.Duel.Verdict.foldRows' face): all-agree
/// is agree; the FIRST non-agree row is the failure evidence (the
/// minimal-counterexample discipline), its witness's `loc` repaired to
/// the row's own path. Shared by every duel lane's report.
pub(crate) fn fold_verdicts<'a, I: IntoIterator<Item = (&'a str, &'a RowVerdict)>>(
    rows: I,
) -> RowVerdict {
    for (path, v) in rows {
        match v {
            RowVerdict::Agree => continue,
            v @ (RowVerdict::Diverge { .. } | RowVerdict::Refused { .. }) => {
                let mut w = v.clone();
                if let RowVerdict::Diverge { loc, .. } = &mut w {
                    *loc = path.to_string();
                }
                return w;
            }
        }
    }
    RowVerdict::Agree
}

/// THE honest report body (the tier sentence is part of the report —
/// 04 §6: a duel verdict is tested agreement, never a theorem):
/// `header`, then one line per row, then the counts line. Shared by
/// every duel lane's report.
pub(crate) fn render_report<'a, I: IntoIterator<Item = (&'a str, &'a RowVerdict)>>(
    header: &str,
    rows: I,
) -> String {
    let rows: Vec<(&str, &RowVerdict)> = rows.into_iter().collect();
    let (a, d, r) = verdict_counts(rows.iter().copied());
    let mut out = String::new();
    out.push_str(header);
    for (path, v) in &rows {
        out.push_str(&format!("  {path}: {}\n", v.render()));
    }
    out.push_str(&format!(
        "{n} row(s): {a} agree, {d} diverge, {r} refused",
        n = rows.len()
    ));
    out
}

impl DuelReport {
    /// The counts: (agree, diverge, refused).
    pub fn counts(&self) -> (usize, usize, usize) {
        verdict_counts(self.rows.iter().map(|r| (r.path.as_str(), &r.verdict)))
    }

    /// THE honest rendering (the tier sentence is part of the report —
    /// 04 §6: a duel verdict is tested agreement, never a theorem).
    pub fn render(&self) -> String {
        render_report(
            &format!(
                "wasm-exec duel (generator {}): TESTED AGREEMENT — the \
                 oracleSwept tier, never a theorem (notes/v3/04 §6)\n",
                self.generator
            ),
            self.rows.iter().map(|r| (r.path.as_str(), &r.verdict)),
        )
    }

    /// THE duel verdict (Kit.Duel.Verdict.foldRows' face): all-agree is
    /// agree; the FIRST non-agree row is the failure evidence (the
    /// minimal-counterexample discipline).
    pub fn verdict(&self) -> RowVerdict {
        fold_verdicts(self.rows.iter().map(|r| (r.path.as_str(), &r.verdict)))
    }
}

/// Parses the committed manifest (the ONE format — `Kit.Duel.manifestRows`):
/// the GENERATED comment header, then `generator\t<module>`, then one
/// `<path>\t<expectation>` row per vector. The structural walk is the
/// SHARED parser's (the manifest module — every duel lane consumes it);
/// the expectation vocabulary is THIS lane's.
pub(crate) fn parse_manifest(text: &str) -> Result<(String, Vec<(String, Expectation)>), HostError> {
    let parsed = mandate_delta::parse_duel_manifest(text, Expectation::parse)
        .map_err(|e| HostError::DuelManifest(e.reason))?;
    Ok((
        parsed.generator,
        parsed
            .rows
            .into_iter()
            .map(|r| (r.path, r.expectation))
            .collect(),
    ))
}

/// Runs ONE module's exported function (`() -> i64`) in a fresh
/// engine. The outcome is the engine's OBSERVATION — a value, the
/// typed wasm trap, or a typed refusal — never a panic (12 §8).
pub(crate) fn observe(wasm: &[u8]) -> Result<Result<i64, Trap>, HostError> {
    let (_engine, mut store, instance) = instantiate_core_module(wasm)?;
    // The duel's convention: the module's ONE export is the entry —
    // discovered off the instance's own export face.
    let export_name = {
        let mut exports = instance.exports(&mut store);
        let export_count = exports.len();
        let name = exports.next().map(|e| e.name().to_string());
        if export_count != 1 {
            return Err(HostError::EngineRefused(format!(
                "expected exactly one export, found {export_count}"
            )));
        }
        name
    };
    let typed = export_i64(&mut store, &instance, export_name.as_deref().unwrap_or(""))?;
    match typed.call(&mut store, ()) {
        Ok(v) => Ok(Ok(v)),
        Err(e) => match e.downcast_ref::<Trap>() {
            // THE typed runtime trap — the duel's `.trap` vocabulary.
            Some(t) => Ok(Err(t.clone())),
            None => Err(HostError::Engine(format!("call: {e:?}"))),
        },
    }
}

/// Runs one duel row: hash-tie the vector to its sidecar, execute,
/// compare with the expectation. THE error discipline: an EXPECTED
/// refusal is the negative control passing; an unexpected refusal or
/// a value/trap mismatch is the DIVERGENCE WITNESS (the row + both
/// values), never a bare `false`.
fn run_row(
    root: &Path,
    path: &str,
    expect: &Expectation,
) -> Result<RowVerdict, HostError> {
    // The vector bytes + their own sidecar hash tie (the binary lane's
    // skew discipline, per vector — a tampered vector refuses BEFORE
    // the engine sees a byte).
    let vp = resolve_vector(root, path)?;
    let wasm = std::fs::read(&vp)
        .map_err(|source| HostError::Io { what: "duel vector", source })?;
    let sidecar = std::fs::read_to_string(PathBuf::from(format!("{}.hdr", vp.display())))
        .map_err(|source| HostError::Io { what: "duel vector sidecar", source })?;
    let declared = crate::artifact::sidecar_hash(&sidecar).ok_or(
        HostError::SidecarMalformed("the duel vector's sidecar names no content hash"),
    )?;
    let computed = bytes_hash(&wasm);
    if computed != declared {
        return Ok(RowVerdict::Refused {
            why: format!("sidecar hash mismatch: declared {declared}, computed {computed}"),
        });
    }

    Ok(match expect {
        // MUST be refused: wasmtime's compiler is the second refusal —
        // the negative control passing (Lean's validator refused the
        // same module at generation).
        Expectation::Refuse => match observe(&wasm) {
            Err(HostError::EngineRefused(_)) => RowVerdict::Agree,
            Err(other) => return Err(other),
            Ok(_) => RowVerdict::Diverge {
                loc: path.to_string(),
                lhs: "refuse".to_string(),
                rhs: "the host engine ACCEPTED the module".to_string(),
            },
        },
        // MUST trap: the typed trap is the agreement; a compile
        // refusal or a value is the divergence, witnessed.
        Expectation::Trap => match observe(&wasm) {
            Ok(Err(_trap)) => RowVerdict::Agree,
            Ok(Ok(v)) => RowVerdict::Diverge {
                loc: path.to_string(),
                lhs: "trap".to_string(),
                rhs: format!("i64:{v}"),
            },
            Err(HostError::EngineRefused(why)) => RowVerdict::Diverge {
                loc: path.to_string(),
                lhs: "trap".to_string(),
                rhs: format!("the host refused to compile: {why}"),
            },
            Err(other) => return Err(other),
        },
        // MUST run to the pinned values: the engines' arithmetic,
        // control flow, and memory must agree on the VALUES. A host
        // compile refusal under a run expectation is ALSO a divergence
        // (Lean's side ran the same bytes; the engine refused them —
        // the witness names both faces).
        Expectation::Run(expected) => match observe(&wasm) {
            Ok(Ok(v)) => {
                let observed = format!("i64:{v}");
                if &observed == expected {
                    RowVerdict::Agree
                } else {
                    RowVerdict::Diverge {
                        loc: path.to_string(),
                        lhs: format!("run {expected}"),
                        rhs: observed,
                    }
                }
            }
            Ok(Err(_trap)) => RowVerdict::Diverge {
                loc: path.to_string(),
                lhs: format!("run {expected}"),
                rhs: "trap".to_string(),
            },
            Err(HostError::EngineRefused(why)) => RowVerdict::Diverge {
                loc: path.to_string(),
                lhs: format!("run {expected}"),
                rhs: format!("the host refused to compile: {why}"),
            },
            Err(other) => return Err(other),
        },
    })
}

/// Resolves a manifest row's repo-root-relative vector path against
/// the repo root (the duel directory is `gen/wasm-duel` — one
/// directory per duel, the committed convention).
pub(crate) fn resolve_vector(root: &Path, path: &str) -> Result<PathBuf, HostError> {
    if !path.starts_with("gen/") {
        return Err(HostError::DuelManifest(format!(
            "{path}: the vector path is not repo-root-relative under gen/"
        )));
    }
    Ok(root.join(path))
}

/// Runs the whole duel: reads `gen_dir/wasm-duel/manifest.txt`, ties +
/// executes each vector, reports the verdict per row. The verdict is
/// TESTED AGREEMENT — `DuelReport::render` carries the tier sentence.
pub fn run_duel(gen_dir: &Path) -> Result<DuelReport, HostError> {
    let root = gen_dir
        .parent()
        .ok_or_else(|| HostError::Incomplete("duel: the gen dir has no parent"))?;
    let manifest = std::fs::read_to_string(gen_dir.join("wasm-duel").join(MANIFEST))
        .map_err(|source| HostError::Io { what: "duel manifest", source })?;
    let (generator, rows) = parse_manifest(&manifest)?;
    let mut out = Vec::new();
    for (path, expect) in rows {
        let verdict = run_row(root, &path, &expect)?;
        out.push(DuelRow { path, expectation: expect, verdict });
    }
    Ok(DuelReport { generator, rows: out })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The manifest parser's positive pin (the ONE format's shape).
    #[test]
    fn manifest_parses() {
        let text = "# GENERATED by wasmgen — DO NOT EDIT\n# spec - | WasmCore.Duel | 12 item(s) | content hash 1 | regen\n\
                    generator\tWasmCore.Duel\n\
                    gen/wasm-duel/slice.wasm\trun i64:42\n\
                    gen/wasm-duel/trap.wasm\ttrap\n\
                    gen/wasm-duel/invalid.wasm\trefuse\n";
        let (generator, rows) = parse_manifest(text).expect("the manifest parses");
        assert_eq!(generator, "WasmCore.Duel");
        assert_eq!(
            rows,
            vec![
                ("gen/wasm-duel/slice.wasm".to_string(), Expectation::Run("i64:42".to_string())),
                ("gen/wasm-duel/trap.wasm".to_string(), Expectation::Trap),
                ("gen/wasm-duel/invalid.wasm".to_string(), Expectation::Refuse),
            ]
        );
    }

    /// The parser's negative controls: no header, no generator row, an
    /// unknown expectation word — all typed refusals.
    #[test]
    fn manifest_refuses_malformed() {
        let e = parse_manifest("generator\tg\n").expect_err("no header");
        assert!(matches!(e, HostError::DuelManifest(_)), "{e:?}");
        let e = parse_manifest("# GENERATED x\n# y\nrow\tg\n").expect_err("no generator row");
        assert!(matches!(e, HostError::DuelManifest(_)), "{e:?}");
        let e = parse_manifest(
            "# GENERATED x\n# y\ngenerator\tg\np.wasm\texplode\n",
        )
        .expect_err("unknown expectation");
        assert!(matches!(e, HostError::DuelManifest(_)), "{e:?}");
    }

    /// The verdict fold's face: all-agree folds to agree; the first
    /// non-agree row wins (the minimal-counterexample discipline).
    #[test]
    fn verdict_folds_first_non_agree() {
        let report = |vs: Vec<RowVerdict>| DuelReport {
            generator: "g".to_string(),
            rows: vs
                .into_iter()
                .enumerate()
                .map(|(i, v)| DuelRow {
                    path: format!("p{i}"),
                    expectation: Expectation::Refuse,
                    verdict: v,
                })
                .collect(),
        };
        assert_eq!(
            report(vec![RowVerdict::Agree, RowVerdict::Agree]).verdict(),
            RowVerdict::Agree
        );
        match report(vec![
            RowVerdict::Agree,
            RowVerdict::Diverge {
                loc: "p1".to_string(),
                lhs: "run i64:1".to_string(),
                rhs: "i64:2".to_string(),
            },
            RowVerdict::Refused { why: "w".to_string() },
        ])
        .verdict()
        {
            RowVerdict::Diverge { loc, lhs, rhs } => {
                assert_eq!((loc.as_str(), lhs.as_str(), rhs.as_str()), ("p1", "run i64:1", "i64:2"));
            }
            other => panic!("expected the first diverge, got {other:?}"),
        }
    }
}

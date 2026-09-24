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

use wasmtime::{Engine, Module as WasmModule, Store, Trap};

use crate::artifact::bytes_hash;
use crate::HostError;

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
    /// The manifest spelling (the ONE format's second column) — kept
    /// for the round-trip face (`render ∘ parse = id`); the tests pin
    /// it, the lib never calls it.
    #[allow(dead_code)]
    fn render(&self) -> String {
        match self {
            Expectation::Run(r) => format!("run {r}"),
            Expectation::Trap => "trap".to_string(),
            Expectation::Refuse => "refuse".to_string(),
        }
    }

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

impl DuelReport {
    /// The counts: (agree, diverge, refused).
    pub fn counts(&self) -> (usize, usize, usize) {
        let mut a = 0;
        let mut d = 0;
        let mut r = 0;
        for row in &self.rows {
            match row.verdict {
                RowVerdict::Agree => a += 1,
                RowVerdict::Diverge { .. } => d += 1,
                RowVerdict::Refused { .. } => r += 1,
            }
        }
        (a, d, r)
    }

    /// THE honest rendering (the tier sentence is part of the report —
    /// 04 §6: a duel verdict is tested agreement, never a theorem).
    pub fn render(&self) -> String {
        let (a, d, r) = self.counts();
        let mut out = String::new();
        out.push_str(&format!(
            "wasm-exec duel (generator {}): TESTED AGREEMENT — the \
             oracleSwept tier, never a theorem (notes/v3/04 §6)\n",
            self.generator
        ));
        for row in &self.rows {
            out.push_str(&format!("  {}: {}\n", row.path, row.verdict.render()));
        }
        out.push_str(&format!(
            "{n} row(s): {a} agree, {d} diverge, {r} refused",
            n = self.rows.len()
        ));
        out
    }

    /// THE duel verdict (Kit.Duel.Verdict.foldRows' face): all-agree is
    /// agree; the FIRST non-agree row is the failure evidence (the
    /// minimal-counterexample discipline).
    pub fn verdict(&self) -> RowVerdict {
        for row in &self.rows {
            match &row.verdict {
                RowVerdict::Agree => continue,
                v @ (RowVerdict::Diverge { .. } | RowVerdict::Refused { .. }) => {
                    let mut w = v.clone();
                    if let RowVerdict::Diverge { loc, .. } = &mut w {
                        *loc = row.path.clone();
                    }
                    return w;
                }
            }
        }
        RowVerdict::Agree
    }
}

/// Parses the committed manifest (the ONE format — `Kit.Duel.manifestRows`):
/// the 2-line GENERATED header, then `generator\t<module>`, then one
/// `<path>\t<expectation>` row per vector.
fn parse_manifest(text: &str) -> Result<(String, Vec<(String, Expectation)>), HostError> {
    let mut lines = text.lines();
    // The 2-line GENERATED header (skipped; its presence is the
    // artifact surface's shape — the headers gate owns the audit).
    let header1 = lines
        .next()
        .ok_or_else(|| HostError::DuelManifest("empty manifest".to_string()))?;
    if !header1.starts_with('#') || !header1.contains("GENERATED") {
        return Err(HostError::DuelManifest(
            "the manifest carries no GENERATED header".to_string(),
        ));
    }
    lines
        .next()
        .ok_or_else(|| HostError::DuelManifest("truncated header".to_string()))?;

    let mut rows = lines.filter(|l| !l.is_empty());
    // The generator provenance row.
    let gen_row = rows
        .next()
        .ok_or_else(|| HostError::DuelManifest("no generator row".to_string()))?;
    let mut gen_parts = gen_row.split('\t');
    let _keyword = gen_parts
        .next()
        .filter(|k| *k == "generator")
        .ok_or_else(|| {
            HostError::DuelManifest("the first row is not the generator row".to_string())
        })?;
    let generator = gen_parts
        .next()
        .ok_or_else(|| {
            HostError::DuelManifest("the generator row names no module".to_string())
        })?
        .to_string();

    let mut out = Vec::new();
    for line in rows {
        let mut parts = line.split('\t');
        let path = parts
            .next()
            .filter(|p| !p.is_empty())
            .ok_or_else(|| HostError::DuelManifest("an empty row".to_string()))?;
        let expect = parts
            .next()
            .and_then(Expectation::parse)
            .ok_or_else(|| {
                HostError::DuelManifest(format!("{path}: unknown expectation `{expect}`", expect = &line[path.len() + 1..]))
            })?;
        if parts.next().is_some() {
            return Err(HostError::DuelManifest(format!("{path}: extra columns")));
        }
        out.push((path.to_string(), expect));
    }
    if out.is_empty() {
        return Err(HostError::DuelManifest("no expectation rows".to_string()));
    }
    Ok((generator, out))
}

/// Runs ONE module's exported function (`() -> i64`) in a fresh
/// engine. The outcome is the engine's OBSERVATION — a value, the
/// typed wasm trap, or a typed refusal — never a panic (12 §8).
fn observe(wasm: &[u8]) -> Result<Result<i64, Trap>, HostError> {
    let engine = Engine::new(&wasmtime::Config::new())
        .map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let module = WasmModule::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("module compile: {e:?}")))?;

    // The duel's convention: the module's ONE export is the entry.
    let mut exports = module.exports();
    let export_count = exports.len();
    let export_name = exports.next().map(|e| e.name().to_string());
    if export_count != 1 {
        return Err(HostError::EngineRefused(format!(
            "expected exactly one export, found {export_count}"
        )));
    }
    let mut store = Store::new(&engine, ());
    let linker = wasmtime::Linker::<()>::new(&engine);
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| HostError::Engine(format!("instantiate: {e:?}")))?;
    let func = instance
        .get_func(&mut store, export_name.as_deref().unwrap_or(""))
        .ok_or_else(|| HostError::MissingExport(export_name.clone().unwrap_or_default()))?;
    // The typed lift IS the signature check (the engine's typed
    // refusal — a module with any other shape is a refusal, not a
    // misread).
    let typed = func
        .typed::<(), i64>(&store)
        .map_err(|_| HostError::Signature)?;
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
fn resolve_vector(root: &Path, path: &str) -> Result<PathBuf, HostError> {
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

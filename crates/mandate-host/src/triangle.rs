//! THE THREE-WAY DUEL (D1's triangle — the rt-conformance gate's face):
//! Lean exec ≡ wasmtime ≡ wasmi over the SAME 38 generated vectors.
//!
//! The duel (WasmCore.Duel + [`crate::duel`]) is the TWO-way
//! differential: the Lean executor's computed expectations vs the
//! wasmtime engine's observations. The triangle extends the verdict
//! machinery to THREE legs: every manifest row is observed by BOTH
//! real engines — wasmtime (the compiler line's host) and wasmi (the
//! mandate-rt interpreter under the SAME deterministic profile) — and
//! a row agrees only when both legs match the Lean expectation.
//!
//! THE PROFILE'S TEETH HERE: both engine legs ride the ONE committed
//! profile (`gen/wasm-duel/profile.txt` — wasmtime's config via
//! [`crate::engine`]'s applier, wasmi's via mandate-rt's); the two-way
//! duel's wasmtime leg ALREADY ran profiled, so the triangle adds the
//! wasmi leg without a second config anywhere.
//!
//! THE TIER HONESTY (notes/v3/04-verification.md §6, carried over):
//! the triangle's verdict is TESTED AGREEMENT — a regression surface,
//! NEVER a theorem over unbounded inputs. The rendering says so.
//!
//! ERROR DISCIPLINE (12 §8): no bare panics on real error paths.

use std::path::Path;

use crate::HostError;
use crate::duel::Expectation;

/// EITHER leg's observation: a completing call's value, the typed
/// runtime trap, or a LOAD refusal (a compile/validation refusal —
/// the `.refuse` rows' EXPECTED outcome on every leg). A refusal is an
/// OBSERVATION, never a harness error; the harness error face is
/// strictly the plumbing (io, engine init).
#[derive(Debug, Clone, PartialEq, Eq)]
enum Observed {
    Value(i64),
    Trap,
    Refused(String),
}

impl Observed {
    /// The witness's rendered face (the duel's vocabulary).
    fn render(&self) -> String {
        match self {
            Observed::Value(v) => format!("i64:{v}"),
            Observed::Trap => "trap".into(),
            Observed::Refused(why) => format!("refused: {why}"),
        }
    }
}

/// Runs ONE module through the wasmtime leg (the duel lane's profiled
/// engine walk): the engine's compile refusal is the [`Observed::Refused`]
/// observation, the typed wasm trap is [`Observed::Trap`], a
/// completing call is the value.
fn observe_wasmtime(wasm: &[u8]) -> Result<Observed, HostError> {
    match crate::duel::observe(wasm) {
        Ok(Ok(v)) => Ok(Observed::Value(v)),
        Ok(Err(_trap)) => Ok(Observed::Trap),
        Err(HostError::EngineRefused(why)) => Ok(Observed::Refused(why)),
        Err(e) => Err(e),
    }
}

/// Runs ONE module through the wasmi leg (mandate-rt's
/// profile-driven engine): the same observation vocabulary.
fn observe_wasmi(wasm: &[u8]) -> Result<Observed, HostError> {
    match mandate_rt::observe(wasm) {
        Ok(Ok(v)) => Ok(Observed::Value(v)),
        Ok(Err(_trap)) => Ok(Observed::Trap),
        Err(e) => Ok(Observed::Refused(e.0)),
    }
}

/// One triangle row's verdict: the manifest's expectation against BOTH
/// engine legs. `agree` = both legs match the Lean expectation; any
/// other outcome carries the WITNESS — the row AND all three faces
/// (the expectation, wasmtime's observation, wasmi's observation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TriVerdict {
    /// Both engine legs agree with the Lean expectation.
    Agree,
    /// At least one leg disagrees — the witness names the row, the
    /// expectation, and each leg's observation.
    Diverge { loc: String, lhs: String, wasmtime: String, wasmi: String },
    /// The row could not be EXECUTED on a leg (a harness error —
    /// distinct from a module refusal: an IO/engine-plumbing failure
    /// is never evidence about the model).
    HarnessError(String),
}

impl TriVerdict {
    /// The report line's face.
    pub fn render(&self) -> String {
        match self {
            TriVerdict::Agree => "agree".to_string(),
            TriVerdict::Diverge { loc, lhs, wasmtime, wasmi } => format!(
                "diverge at {loc}: expected {lhs}, wasmtime observed {wasmtime}, wasmi observed {wasmi}"
            ),
            TriVerdict::HarnessError(why) => format!("harness error: {why}"),
        }
    }
}

/// One triangle row's outcome.
#[derive(Debug, Clone)]
pub struct TriRow {
    /// The vector path (the manifest's first column).
    pub path: String,
    /// The expectation both legs ran under.
    pub expectation: Expectation,
    /// The verdict.
    pub verdict: TriVerdict,
}

/// The triangle's report: every row's three-way verdict + the honest
/// tier. TESTED AGREEMENT — never a theorem; the rendering says so.
#[derive(Debug, Clone)]
pub struct TriangleReport {
    /// The manifest's `generator` provenance row.
    pub generator: String,
    /// The rows, manifest order.
    pub rows: Vec<TriRow>,
}

impl TriangleReport {
    /// THE triangle verdict (Verdict.foldRows' face): all-agree is
    /// agree; the FIRST non-agree row is the failure evidence (the
    /// minimal-counterexample discipline).
    pub fn verdict(&self) -> TriVerdict {
        for row in &self.rows {
            match &row.verdict {
                TriVerdict::Agree => continue,
                v => return v.clone(),
            }
        }
        TriVerdict::Agree
    }

    /// THE honest rendering (the tier sentence is part of the report —
    /// 04 §6: a duel verdict is tested agreement, never a theorem).
    pub fn render(&self) -> String {
        let (total, agrees) = (self.rows.len(), self.rows.iter().filter(|r| r.verdict == TriVerdict::Agree).count());
        let mut out = String::new();
        out.push_str(&format!(
            "three-way wasm duel (generator {generator}): TESTED AGREEMENT — the \
             oracleSwept tier, never a theorem (notes/v3/04 §6)\n",
            generator = self.generator
        ));
        for row in &self.rows {
            out.push_str(&format!("  {}: {}\n", row.path, row.verdict.render()));
        }
        out.push_str(&format!("{total} row(s): {agrees} agree, {} not-agree", total - agrees));
        out
    }
}

/// The expectation's rendered face (the witness's lhs — the duel's
/// own vocabulary, `run i64:42` / `trap` / `refuse`; the Debug derive
/// is harness-internal, the WITNESS speaks the manifest's words).
fn expect_note(e: &Expectation) -> String {
    match e {
        Expectation::Run(r) => format!("run {r}"),
        Expectation::Trap => "trap".into(),
        Expectation::Refuse => "refuse".into(),
    }
}

/// Runs the whole triangle: reads the committed manifest, ties +
/// executes each vector on BOTH engine legs, answers per row. The
/// verdict is TESTED AGREEMENT — `TriangleReport::render` carries the
/// tier sentence. (The per-vector sidecar hash tie + the wasmtime
/// observation's typed faces are the duel lane's; the manifest parser
/// is the ONE shared copy — this lane re-walks the rows through the
/// same runners.)
pub fn run_triangle(gen_dir: &Path) -> Result<TriangleReport, HostError> {
    let root = gen_dir
        .parent()
        .ok_or_else(|| HostError::Incomplete("triangle: the gen dir has no parent"))?;
    let manifest = std::fs::read_to_string(gen_dir.join("wasm-duel").join("manifest.txt"))
        .map_err(|source| HostError::Io { what: "triangle manifest", source })?;
    let (generator, rows) = crate::duel::parse_manifest(&manifest)?;
    let mut out = Vec::new();
    for (path, expect) in rows {
        // The hash-tie + the bytes: the duel lane's per-vector walk
        // (the same discipline, replayed — a tampered vector refuses
        // BEFORE either engine sees a byte).
        let vp = crate::duel::resolve_vector(root, &path)?;
        let wasm = std::fs::read(&vp)
            .map_err(|source| HostError::Io { what: "triangle vector", source })?;
        let sidecar = std::fs::read_to_string(format!("{}.hdr", vp.display()))
            .map_err(|source| HostError::Io { what: "triangle vector sidecar", source })?;
        let declared = crate::artifact::sidecar_hash(&sidecar).ok_or(
            HostError::SidecarMalformed("the triangle vector's sidecar names no content hash"),
        )?;
        let computed = crate::artifact::bytes_hash(&wasm);
        if computed != declared {
            out.push(TriRow {
                path: path.clone(),
                expectation: expect,
                verdict: TriVerdict::Diverge {
                    loc: path.clone(),
                    lhs: "the sidecar tie".into(),
                    wasmtime: format!("declared {declared}"),
                    wasmi: format!("computed {computed}"),
                },
            });
            continue;
        }
        // BOTH legs run; a leg's HARNESS failure (not a module
        // refusal) is a harness error, never a verdict about the model.
        let verdict = match (observe_wasmtime(&wasm), observe_wasmi(&wasm)) {
            (Ok(wt), Ok(mi)) => match (&expect, &wt, &mi) {
                // THE `.run` row: both legs complete to the pinned
                // values AND the legs agree with each other.
                (Expectation::Run(expected), Observed::Value(a), Observed::Value(b))
                    if format!("i64:{a}") == *expected && a == b =>
                {
                    TriVerdict::Agree
                }
                // THE `.trap` row: BOTH legs trap — the typed wasm
                // trap in every engine.
                (Expectation::Trap, Observed::Trap, Observed::Trap) => TriVerdict::Agree,
                // THE `.refuse` row: BOTH legs refuse (the negative
                // control passing on both engines — Lean's validator
                // refused at generation).
                (Expectation::Refuse, Observed::Refused(_), Observed::Refused(_)) => {
                    TriVerdict::Agree
                }
                _ => TriVerdict::Diverge {
                    loc: path.clone(),
                    lhs: expect_note(&expect),
                    wasmtime: wt.render(),
                    wasmi: mi.render(),
                },
            },
            (Err(e), _) | (_, Err(e)) => TriVerdict::HarnessError(e.to_string()),
        };
        out.push(TriRow { path, expectation: expect, verdict });
    }
    Ok(TriangleReport { generator, rows: out })
}

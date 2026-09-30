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
use crate::duel::{Expectation, RowVerdict};

/// The wasmi leg's observation (mandate_rt::observe's face, widened to
/// the refusal case): a value, a typed trap, or a load refusal.
enum WasmiObserved {
    Value(i64),
    Trap(String),
    Refused(String),
}

/// Runs ONE module through the wasmi leg (mandate-rt's
/// profile-driven engine): a load refusal is the typed [`WasmiObserved::Refused`]
/// (the `.refuse` rows' EXPECTED outcome on this leg), a trap code is
/// [`WasmiObserved::Trap`], a completing call is the value.
fn observe_wasmi(wasm: &[u8]) -> Result<WasmiObserved, HostError> {
    match mandate_rt::observe(wasm) {
        Ok(Ok(v)) => Ok(WasmiObserved::Value(v)),
        Ok(Err(trap)) => Ok(WasmiObserved::Trap(trap)),
        Err(e) => Ok(WasmiObserved::Refused(e.0)),
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

/// The wasmtime leg's rendered observation (the witness's face): the
/// same vocabulary the two-way duel's `run_row` speaks — `i64:<v>` /
/// `trap` / the refusal text.
fn run_wasmtime_leg(wasm: &[u8]) -> Result<Result<String, String>, HostError> {
    let observed = crate::duel::observe(wasm)?;
    Ok(match observed {
        Ok(v) => Ok(format!("i64:{v}")),
        Err(_trap) => Ok(Err("trap".into())),
    })
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
                path,
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
        let wt = run_wasmtime_leg(&wasm);
        let mi = observe_wasmi(&wasm);
        let verdict = match (wt, mi) {
            (Ok(Ok(wt)), Ok(WasmiObserved::Value(v))) => {
                let observed = format!("i64:{v}");
                match &expect {
                    Expectation::Run(expected) if &observed == expected && wt == observed => {
                        TriVerdict::Agree
                    }
                    _ => TriVerdict::Diverge {
                        loc: path.clone(),
                        lhs: expect_note(&expect),
                        wasmtime: wt,
                        wasmi: observed,
                    },
                }
            }
            (Ok(Ok(wt)), Ok(WasmiObserved::Trap(t))) => match &expect {
                Expectation::Trap if wt == "trap" => TriVerdict::Agree,
                _ => TriVerdict::Diverge {
                    loc: path.clone(),
                    lhs: expect_note(&expect),
                    wasmtime: wt,
                    wasmi: t,
                },
            },
            (Ok(Ok(_wt)), Ok(WasmiObserved::Refused(r))) => TriVerdict::Diverge {
                loc: path.clone(),
                lhs: expect_note(&expect),
                wasmtime: "completed".into(),
                wasmi: format!("refused: {r}"),
            },
            (Ok(Err(_)), Ok(WasmiObserved::Value(v))) => TriVerdict::Diverge {
                loc: path.clone(),
                lhs: expect_note(&expect),
                wasmtime: "refused/trapped".into(),
                wasmi: format!("i64:{v}"),
            },
            (Ok(Err(_)), Ok(WasmiObserved::Trap(_t))) => match &expect {
                Expectation::Refuse => TriVerdict::Agree,
                _ => TriVerdict::Diverge {
                    loc: path.clone(),
                    lhs: expect_note(&expect),
                    wasmtime: "refused".into(),
                    wasmi: "trapped".into(),
                },
            },
            (Ok(Err(_)), Ok(WasmiObserved::Refused(_r))) => match &expect {
                // THE `.refuse` row's agreement: BOTH legs refuse (the
                // negative control passing on both engines).
                Expectation::Refuse => TriVerdict::Agree,
                _ => TriVerdict::Diverge {
                    loc: path.clone(),
                    lhs: expect_note(&expect),
                    wasmtime: "refused".into(),
                    wasmi: "refused".into(),
                },
            },
            (Err(e), _) | (_, Err(e)) => TriVerdict::HarnessError(e.to_string()),
        };
        out.push(TriRow { path, expectation: expect, verdict });
    }
    Ok(TriangleReport { generator, rows: out })
}

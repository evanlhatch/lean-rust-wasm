//! The duel manifest's ONE parser — `Kit.Duel.manifestRows`' consumer
//! contract, shared by every duel lane (the journal duel here, the
//! wasm duel + the commit duel + the witness duel in the consumers).
//!
//! THE ONE FORMAT: a GENERATED comment header (`#`- or `//`-prefixed;
//! the FIRST line must carry `GENERATED` — the artifact-headers
//! discipline), then the `generator\t<name>` provenance row, then one
//! `<path>\t<expectation>` row per vector. The EXPECTATION VOCABULARY
//! is the caller's (the lanes pin different faces of the same
//! contract: `run X`/`trap`/`refuse`, `decode accept`/`refuse`,
//! `decode <note>`), passed as the parse callback — the structural
//! walk is HERE, never a second one (the drift class the dedup wave
//! closed: four byte-shaped walks could not agree on the header).

use std::fmt;

/// A malformed duel manifest (the typed refusal — never a guess, and
/// for the tests' faces never a panic either: the caller maps this to
/// its own error surface).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ManifestError {
    /// What refused.
    pub reason: String,
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "duel manifest: {}", self.reason)
    }
}

impl std::error::Error for ManifestError {}

/// One parsed manifest row: the vector path + the caller-vocabulary
/// expectation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DuelRow<E> {
    /// The vector path (the manifest's first column; repo-root-relative
    /// by the committed convention).
    pub path: String,
    /// The parsed expectation (the second column, in the caller's
    /// vocabulary).
    pub expectation: E,
}

/// A parsed duel manifest: the generator provenance + every row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DuelManifest<E> {
    /// The `generator` row's payload (the emitter's provenance).
    pub generator: String,
    /// The rows, manifest order.
    pub rows: Vec<DuelRow<E>>,
}

/// Parses the committed manifest (the ONE format): the GENERATED
/// comment header, the `generator` provenance row, then one
/// `<path>\t<expectation>` row per vector. `parse_expect` is the
/// lane's expectation vocabulary — returning `None` refuses the row
/// (a malformed manifest, never a guess).
///
/// # Errors
/// No GENERATED header, no (or a second) generator row, an empty or
/// extra-columned row, an unknown expectation, or no rows at all.
pub fn parse_duel_manifest<E>(
    text: &str,
    parse_expect: impl Fn(&str) -> Option<E>,
) -> Result<DuelManifest<E>, ManifestError> {
    let err = |reason: &str| ManifestError {
        reason: reason.to_string(),
    };
    let mut generator: Option<String> = None;
    let mut rows = Vec::new();
    let mut header_seen = false;
    for line in text.lines() {
        if line.trim().is_empty() {
            continue;
        }
        // The comment header (`#` or `//` dialects — the lanes' two
        // emitter spellings); the FIRST comment line must carry
        // GENERATED (the artifact-headers discipline's consumer face).
        if line.starts_with('#') || line.starts_with("//") {
            if !header_seen {
                if !line.contains("GENERATED") {
                    return Err(err("the manifest carries no GENERATED header"));
                }
                header_seen = true;
            }
            continue;
        }
        if !header_seen {
            return Err(err("the manifest carries no GENERATED header"));
        }
        let mut parts = line.split('\t');
        let first = parts
            .next()
            .filter(|k| !k.is_empty())
            .ok_or_else(|| err("an empty row"))?;
        if first == "generator" {
            if generator.is_some() {
                return Err(err("a second generator row"));
            }
            let name = parts
                .next()
                .ok_or_else(|| err("the generator row names no module"))?;
            if parts.next().is_some() {
                return Err(err("the generator row has extra columns"));
            }
            generator = Some(name.to_string());
            continue;
        }
        let column = parts.next().unwrap_or_default();
        let expectation = parse_expect(column)
            .ok_or_else(|| err(&format!("{first}: unknown expectation `{column}`")))?;
        if parts.next().is_some() {
            return Err(err(&format!("{first}: extra columns")));
        }
        rows.push(DuelRow {
            path: first.to_string(),
            expectation,
        });
    }
    let generator = generator.ok_or_else(|| err("no generator row"))?;
    if rows.is_empty() {
        return Err(err("no expectation rows"));
    }
    Ok(DuelManifest { generator, rows })
}

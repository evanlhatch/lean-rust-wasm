//! The provenance annotations: the gates' outputs, as OCI manifest
//! annotations (design-wave-30 D5; notes/v3/09-gates-ops.md §4 — the
//! artifact stage's provenance face).
//!
//! THE DISCIPLINE: the ledger's row → the manifest's annotations, ONE
//! writer. The writer (the store's `put` caller) supplies the attested
//! values as a [`Provenance`]; the store composes the annotation map
//! exactly once (`compose`) and checks it exactly once (`check`). The
//! store never invents a badge — a `Provenance` whose ledger hash does
//! not match the bytes' own digest refuses at put (a lying ledger row
//! is a refusal, not a warning).
//!
//! The badges (the keys are THIS module's single spec — no second
//! spelling anywhere):
//!
//! - `org.opencontainers.image.ref.name` — the artifact label (the
//!   repo-root-relative path; the OCI ref-name convention legacy used).
//! - `dev.mandate.prov.axiom-report` — the AXIOM BADGE: the sha256 of
//!   the gates' axiom report at store time (the artifact's axiom
//!   surface, attested by content).
//! - `dev.mandate.prov.gates` — the gates-green stamp: the literal
//!   `green`; a stored artifact without it is unread (`read` refuses).
//! - `dev.mandate.prov.gates-stamp` — the reports' digest: sha256 over
//!   the gates' report files' contents (name + bytes, sorted) — the
//!   stamp is an attestation BY CONTENT, not a bare claim.
//! - `dev.mandate.prov.ledger-hash` — the ledger's content hash for
//!   this artifact; must equal the blob's own digest (the cross-check
//!   that ties the ledger row to the stored bytes).

use crate::digest::{is_valid_digest, oci_digest, parse_oci_digest};
use serde_json::{Map, Value};

/// The artifact label (repo-root-relative path).
pub const LABEL: &str = "org.opencontainers.image.ref.name";
/// The axiom-report badge (the gates' axiom surface, by content).
pub const AXIOM_REPORT: &str = "dev.mandate.prov.axiom-report";
/// The gates-green stamp (the literal `green`).
pub const GATES: &str = "dev.mandate.prov.gates";
/// The gates stamp's content digest (the reports' hash).
pub const GATES_STAMP: &str = "dev.mandate.prov.gates-stamp";
/// The ledger's content hash (must equal the blob's digest).
pub const LEDGER_HASH: &str = "dev.mandate.prov.ledger-hash";

/// The provenance a `put` MUST carry (the gates' outputs, attested by
/// the writer). Every field is checked; none is defaulted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provenance {
    /// The artifact label (repo-root-relative path).
    pub label: String,
    /// sha256 of the gates' axiom report (`notes/axiom-report.md`) at
    /// store time.
    pub axiom_report_sha256: String,
    /// The gates' report files as (name, bytes) — hashed into the
    /// stamp. Sorted by name at composition; order never matters to
    /// the writer.
    pub gates_reports: Vec<(String, Vec<u8>)>,
    /// The ledger's content hash for this artifact. MUST equal the
    /// artifact bytes' own sha256 (checked at put).
    pub ledger_hash: String,
}

/// The literal gates-green value.
pub const GATES_GREEN: &str = "green";

/// The gates stamp: sha256 over the reports' (name, bytes) pairs,
/// sorted by name — an attestation by content, deterministic in the
/// reports' SET (order-independent, duplicate-name-independent: the
/// last row per name wins, matching a map's semantics).
pub fn gates_stamp(reports: &[(String, Vec<u8>)]) -> String {
    let mut sorted: Vec<(String, Vec<u8>)> = reports.to_vec();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    sorted.dedup_by(|a, b| a.0 == b.0);
    let mut buf = Vec::new();
    for (name, bytes) in &sorted {
        buf.extend_from_slice(name.as_bytes());
        buf.push(0); // the separator (names cannot contain NUL)
        buf.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        buf.extend_from_slice(bytes);
    }
    crate::digest::sha256_hex(&buf)
}

/// Compose the annotation map — the ONE writer's face (only `put`
/// calls this). The ledger hash is NOT written here as supplied: it is
/// written from the bytes' own digest, and `put` refuses when the
/// supplied ledger hash disagrees. The map is the truth of what was
/// stored, never the writer's claim about it.
pub fn compose(prov: &Provenance, blob_digest: &str) -> Map<String, Value> {
    let mut ann = Map::new();
    ann.insert(
        LABEL.into(),
        Value::String(prov.label.clone()),
    );
    ann.insert(
        AXIOM_REPORT.into(),
        Value::String(oci_digest(&prov.axiom_report_sha256)),
    );
    ann.insert(GATES.into(), Value::String(GATES_GREEN.into()));
    ann.insert(
        GATES_STAMP.into(),
        Value::String(oci_digest(&gates_stamp(&prov.gates_reports))),
    );
    ann.insert(
        LEDGER_HASH.into(),
        Value::String(oci_digest(blob_digest)),
    );
    ann
}

/// A provenance-shape refusal: which annotation, why (the
/// refuse-with-report discipline — rendered, never silent).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvRefusal {
    Missing { key: String },
    Malformed { key: String, why: String },
    Stale { key: String, declared: String, actual: String },
}

impl ProvRefusal {
    /// The rendered report line.
    pub fn report(&self) -> String {
        match self {
            Self::Missing { key } => {
                format!("REFUSED provenance: annotation `{key}` missing")
            }
            Self::Malformed { key, why } => {
                format!("REFUSED provenance: annotation `{key}` malformed: {why}")
            }
            Self::Stale { key, declared, actual } => format!(
                "REFUSED provenance: annotation `{key}` stale: declared {declared}, actual {actual}"
            ),
        }
    }
}

/// Check the annotation SHAPE: every badge present, every digest
/// well-formed, the label matching, gates green. Pure (no IO, no
/// staleness — the live-report check is `check_axiom_fresh`).
pub fn check(ann: &Map<String, Value>, expect_label: &str) -> Result<(), ProvRefusal> {
    let get = |key: &str| -> Result<String, ProvRefusal> {
        ann.get(key)
            .and_then(Value::as_str)
            .map(str::to_owned)
            .ok_or_else(|| match ann.get(key) {
                Some(_) => ProvRefusal::Malformed {
                    key: key.into(),
                    why: "not a string".into(),
                },
                None => ProvRefusal::Missing { key: key.into() },
            })
    };
    let label = get(LABEL)?;
    if label != expect_label {
        return Err(ProvRefusal::Malformed {
            key: LABEL.into(),
            why: format!("label `{label}` != requested `{expect_label}`"),
        });
    }
    for key in [AXIOM_REPORT, GATES_STAMP, LEDGER_HASH] {
        let v = get(key)?;
        if parse_oci_digest(&v).is_none() {
            return Err(ProvRefusal::Malformed {
                key: key.into(),
                why: format!("`{v}` is not sha256:<64 lowercase hex>"),
            });
        }
    }
    let gates = get(GATES)?;
    if gates != GATES_GREEN {
        return Err(ProvRefusal::Malformed {
            key: GATES.into(),
            why: format!("`{gates}` is not `{GATES_GREEN}` — an artifact stored without a green gates run is unread"),
        });
    }
    Ok(())
}

/// The staleness face: the axiom badge against the LIVE report bytes.
/// A badge from an older gates run is STALE — the artifact's axiom
/// surface moved under it.
pub fn check_axiom_fresh(ann: &Map<String, Value>, live_report: &[u8]) -> Result<(), ProvRefusal> {
    let declared = ann
        .get(AXIOM_REPORT)
        .and_then(Value::as_str)
        .unwrap_or_default();
    let actual = crate::digest::sha256_hex(live_report);
    if declared != oci_digest(&actual) || parse_oci_digest(declared).is_none() {
        return Err(ProvRefusal::Stale {
            key: AXIOM_REPORT.into(),
            declared: declared.into(),
            actual,
        });
    }
    Ok(())
}

/// A digest is well-formed? (the read-side re-check on any digest read
/// out of a document).
pub fn valid_digest_ref(key: &str, v: &str) -> Result<(), ProvRefusal> {
    if is_valid_digest(v) {
        Ok(())
    } else {
        Err(ProvRefusal::Malformed {
            key: key.into(),
            why: format!("`{v}` is not a 64-lowercase-hex digest"),
        })
    }
}

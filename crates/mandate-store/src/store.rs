//! The OCI image-layout store (the local lane; design-wave-30 D5).
//!
//! Layout (the image spec's honest subset — what standard tooling can
//! inspect, nothing speculative):
//!
//! ```text
//! <root>/
//! ├── oci-layout                  {"imageLayoutVersion":"1.0.0"}
//! ├── index.json                  label → manifest digest
//! └── blobs/sha256/<hex>          config + layers + manifests
//! ```
//!
//! One artifact = one manifest = one layer blob (the wasm components,
//! the WIT worlds, the duel manifests — the gen/ artifacts). The
//! manifest carries the provenance annotations (`prov.rs` — the ONE
//! writer is `put`, the ONE reader is `read`).
//!
//! THE VERIFY DISCIPLINE: every blob read re-hashes the bytes against
//! the digest that names it; a tampered blob refuses with a report.
//! Every manifest read checks the annotation shape; a manifest without
//! a complete, green, well-formed provenance refuses. The staleness
//! face (`read_fresh`) refuses an axiom badge that disagrees with the
//! live report. Refuse-with-report — never a silent fallback, never a
//! warning-shaped pass.

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde_json::{json, Map, Value};

use crate::digest::{self, Digest};
use crate::prov::{self, ProvRefusal, Provenance};

/// The OCI media types this store writes (the honest subset).
pub const MANIFEST_MT: &str = "application/vnd.oci.image.manifest.v1+json";
pub const INDEX_MT: &str = "application/vnd.oci.image.index.v1+json";
pub const CONFIG_MT: &str = "application/vnd.oci.image.config.v1+json";
pub const ARTIFACT_MT: &str = "application/vnd.mandate.artifact.v1";

/// The config blob — fixed bytes, no timestamps (determinism: the
/// store's bytes are a function of content + annotations only).
pub const CONFIG_JSON: &[u8] =
    br#"{"architecture":"unknown","os":"unknown","rootfs":{"type":"layers","diff_ids":[]}}"#;

/// The store's refusals (refuse-with-report: every variant renders).
#[derive(Debug)]
pub enum Refusal {
    /// The manifest's provenance shape is missing/malformed.
    Prov(ProvRefusal),
    /// The axiom badge disagrees with the live report (stale).
    ProvStale(ProvRefusal),
    /// A blob's bytes do not hash to the digest that names it.
    HashMismatch { what: String, digest: Digest, actual: Digest },
    /// The put-time cross-check: the ledger's hash disagrees with the
    /// bytes' own digest (a lying ledger row refuses at put).
    LedgerMismatch { declared: Digest, actual: Digest },
    /// No manifest digest recorded for this label.
    UnknownLabel { label: String },
    /// A document (manifest) does not parse or is structurally wrong.
    MalformedDocument { what: String, why: String },
    /// A digest string that is not 64 lowercase hex (path safety: this
    /// refusal fires before the filesystem is touched).
    InvalidDigest { value: String },
}

impl Refusal {
    /// The rendered report (the report IS the refusal's value — the
    /// caller prints it, the store never logs through a side channel).
    pub fn report(&self) -> String {
        match self {
            Self::Prov(p) | Self::ProvStale(p) => p.report(),
            Self::HashMismatch { what, digest, actual } => format!(
                "REFUSED {what}: tampered blob — stored digest {digest}, actual {actual}"
            ),
            Self::LedgerMismatch { declared, actual } => format!(
                "REFUSED put: ledger hash {declared} != artifact digest {actual} — the ledger row lies"
            ),
            Self::UnknownLabel { label } => {
                format!("REFUSED read: no artifact stored under `{label}`")
            }
            Self::MalformedDocument { what, why } => {
                format!("REFUSED {what}: malformed document: {why}")
            }
            Self::InvalidDigest { value } => {
                format!("REFUSED: `{value}` is not a 64-lowercase-hex digest")
            }
        }
    }
}

/// `Refusal` (typed) or IO — the store's error surface.
#[derive(Debug)]
pub enum StoreError {
    Io(io::Error),
    Refusal(Refusal),
}

impl From<io::Error> for StoreError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<Refusal> for StoreError {
    fn from(r: Refusal) -> Self {
        Self::Refusal(r)
    }
}

impl From<ProvRefusal> for Refusal {
    fn from(p: ProvRefusal) -> Self {
        Refusal::Prov(p)
    }
}

/// A read-back artifact: the verified bytes + their provenance.
#[derive(Debug, Clone)]
pub struct Artifact {
    pub label: String,
    /// The layer blob's digest (the content address).
    pub digest: Digest,
    pub data: Vec<u8>,
    /// The manifest's annotations (the provenance badges).
    pub annotations: Map<String, Value>,
}

/// The byte-tie face's verdict (`verify_file`).
#[derive(Debug, PartialEq, Eq)]
pub enum Verify {
    /// Nothing stored under this label.
    NotStored,
    /// The file's digest matches the stored layer's.
    Match,
    /// Drift: the file's digest differs from the stored layer's.
    Mismatch { stored: Digest, actual: Digest },
}

/// One `list` row (the store's query face: label → content + badges).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredRow {
    pub label: String,
    pub manifest_digest: Digest,
    pub layer_digest: Digest,
    /// The axiom badge (bare hex).
    pub axiom_report: Digest,
    /// The gates stamp (bare hex).
    pub gates_stamp: Digest,
}

/// The OCI image-layout store.
pub struct Store {
    root: PathBuf,
    /// label → manifest digest (loaded from index.json at open,
    /// updated by `put`).
    tags: BTreeMap<String, Digest>,
}

impl Store {
    /// Open (or lazily create) an OCI layout at `root`.
    pub fn open(root: &Path) -> io::Result<Self> {
        fs::create_dir_all(root.join("blobs/sha256"))?;
        let layout = root.join("oci-layout");
        if !layout.exists() {
            fs::write(&layout, r#"{"imageLayoutVersion":"1.0.0"}"#)?;
        }
        let index = root.join("index.json");
        if !index.exists() {
            fs::write(&index, json!({"schemaVersion": 2, "manifests": []}).to_string())?;
        }
        let tags = Self::load_tags(&index);
        Ok(Self { root: root.to_path_buf(), tags })
    }

    /// Read label → manifest digest from index.json. Missing or
    /// malformed entries are skipped (the index is the pointer cache;
    /// the blobs are the truth).
    fn load_tags(index: &Path) -> BTreeMap<String, Digest> {
        let Ok(raw) = fs::read_to_string(index) else {
            return BTreeMap::new();
        };
        let Ok(value) = serde_json::from_str::<Value>(&raw) else {
            return BTreeMap::new();
        };
        value["manifests"]
            .as_array()
            .map(|ms| {
                ms.iter()
                    .filter_map(|m| {
                        let digest = m["digest"].as_str()?;
                        let hex = digest.strip_prefix("sha256:")?;
                        let label = m["annotations"][prov::LABEL].as_str()?;
                        Some((label.to_string(), hex.to_string()))
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn blobs_dir(&self) -> PathBuf {
        self.root.join("blobs/sha256")
    }

    /// Path of a blob by bare hex digest.
    pub fn blob_path(&self, digest: &str) -> PathBuf {
        self.blobs_dir().join(digest)
    }

    /// Read a blob BY DIGEST, verifying the bytes hash to the digest
    /// that names them (the tamper refusal; path-safe — a non-hex
    /// digest refuses before the filesystem is touched).
    fn blob(&self, digest: &str, what: &str) -> Result<Vec<u8>, StoreError> {
        if !digest::is_valid_digest(digest) {
            return Err(Refusal::InvalidDigest { value: digest.into() }.into());
        }
        let bytes = fs::read(self.blob_path(digest))?;
        let actual = digest::sha256_hex(&bytes);
        if actual != digest {
            return Err(Refusal::HashMismatch {
                what: what.into(),
                digest: digest.into(),
                actual,
            }
            .into());
        }
        Ok(bytes)
    }

    /// Write a blob (unconditionally, so a corrupted cache blob
    /// self-heals on the next put — legacy's precedent).
    fn write_blob(&self, digest: &str, data: &[u8]) -> io::Result<()> {
        fs::write(self.blob_path(digest), data)
    }

    /// Content-address an artifact: hash, write the layer blob, build
    /// + store the provenance manifest, record label → manifest.
    ///
    /// THE ONE WRITER: the annotation map is composed here and nowhere
    /// else. The ledger hash is cross-checked against the bytes' own
    /// digest FIRST — a lying ledger row refuses before anything is
    /// written.
    pub fn put(&mut self, p: &Provenance, data: &[u8]) -> Result<Digest, StoreError> {
        let digest = digest::sha256_hex(data);
        if p.ledger_hash != digest {
            return Err(Refusal::LedgerMismatch {
                declared: p.ledger_hash.clone(),
                actual: digest.clone(),
            }
            .into());
        }
        if p.label.is_empty() {
            return Err(Refusal::MalformedDocument {
                what: "put".into(),
                why: "empty label".into(),
            }
            .into());
        }
        self.write_blob(&digest, data)?;

        let config = digest::sha256_hex(CONFIG_JSON);
        self.write_blob(&config, CONFIG_JSON)?;

        let annotations = prov::compose(p, &digest);
        let manifest = json!({
            "schemaVersion": 2,
            "mediaType": MANIFEST_MT,
            "config": {
                "mediaType": CONFIG_MT,
                "digest": digest::oci_digest(&config),
                "size": CONFIG_JSON.len(),
            },
            "layers": [{
                "mediaType": ARTIFACT_MT,
                "digest": digest::oci_digest(&digest),
                "size": data.len(),
                "annotations": { prov::LABEL: p.label },
            }],
            "annotations": Value::Object(annotations),
        });
        let manifest_bytes = manifest.to_string().into_bytes();
        let manifest_digest = digest::sha256_hex(&manifest_bytes);
        self.write_blob(&manifest_digest, &manifest_bytes)?;

        self.tags.insert(p.label.clone(), manifest_digest.clone());
        self.write_index()?;
        Ok(digest)
    }

    /// Read a stored artifact, verifying EVERYTHING: the manifest
    /// blob's hash, the annotation shape (complete, green,
    /// well-formed), the layer blob's hash, and the ledger hash
    /// against the layer's actual digest. Any failure refuses with a
    /// report.
    pub fn read(&self, label: &str) -> Result<Artifact, StoreError> {
        let manifest_digest = self
            .tags
            .get(label)
            .ok_or_else(|| Refusal::UnknownLabel { label: label.into() })?
            .clone();
        let manifest_bytes = self.blob(&manifest_digest, "manifest")?;
        let manifest: Value = serde_json::from_slice(&manifest_bytes).map_err(|e| {
            Refusal::MalformedDocument { what: "manifest".into(), why: e.to_string() }
        })?;
        if manifest["schemaVersion"] != json!(2) {
            return Err(Refusal::MalformedDocument {
                what: "manifest".into(),
                why: format!("schemaVersion {} != 2", manifest["schemaVersion"]),
            }
            .into());
        }
        let config_digest = manifest["config"]["digest"]
            .as_str()
            .and_then(digest::parse_oci_digest)
            .ok_or_else(|| {
                Refusal::MalformedDocument {
                    what: "manifest".into(),
                    why: "config.digest is not sha256:<hex>".into(),
                }
            })?;
        self.blob(config_digest, "config")?;

        let layers = manifest["layers"].as_array().ok_or_else(|| {
            Refusal::MalformedDocument { what: "manifest".into(), why: "layers missing".into() }
        })?;
        let [layer] = &layers[..] else {
            return Err(Refusal::MalformedDocument {
                what: "manifest".into(),
                why: format!("{} layers — one artifact = one layer", layers.len()),
            }
            .into());
        };
        let layer_hex = layer["digest"]
            .as_str()
            .and_then(digest::parse_oci_digest)
            .ok_or_else(|| {
                Refusal::MalformedDocument {
                    what: "manifest".into(),
                    why: "layer digest is not sha256:<hex>".into(),
                }
            })?;
        let data = self.blob(layer_hex, "layer")?;

        let ann = manifest["annotations"].as_object().ok_or_else(|| {
            Refusal::MalformedDocument { what: "manifest".into(), why: "annotations missing".into() }
        })?;
        prov::check(ann, label).map_err(Refusal::Prov)?;
        let ledger_hex = ann[prov::LEDGER_HASH].as_str().unwrap_or_default();
        if ledger_hex != digest::oci_digest(layer_hex) {
            return Err(Refusal::Prov(ProvRefusal::Malformed {
                key: prov::LEDGER_HASH.into(),
                why: format!("ledger hash {ledger_hex} != layer digest {}", digest::oci_digest(layer_hex)),
            })
            .into());
        }
        Ok(Artifact {
            label: label.to_string(),
            digest: layer_hex.to_string(),
            data,
            annotations: ann.clone(),
        })
    }

    /// The staleness face: `read` + the axiom badge against the LIVE
    /// axiom report's bytes. A stale badge (an older gates run) refuses
    /// with the declared/actual digests in the report.
    pub fn read_fresh(&self, label: &str, live_axiom_report: &[u8]) -> Result<Artifact, StoreError> {
        let artifact = self.read(label)?;
        prov::check_axiom_fresh(&artifact.annotations, live_axiom_report)
            .map_err(Refusal::ProvStale)?;
        Ok(artifact)
    }

    /// The byte-tie face: compare a file on disk against the stored
    /// artifact (full bytes — the OCI digest is over the whole blob;
    /// the regen-header discipline stays with the gates' own
    /// artifact-header checks, it never dilutes a content address).
    pub fn verify_file(&self, label: &str, path: &Path) -> Result<Verify, StoreError> {
        let Some(manifest_digest) = self.tags.get(label) else {
            return Ok(Verify::NotStored);
        };
        let manifest_bytes = self.blob(manifest_digest, "manifest")?;
        let manifest: Value = serde_json::from_slice(&manifest_bytes).map_err(|e| {
            StoreError::Refusal(Refusal::MalformedDocument {
                what: "manifest".into(),
                why: e.to_string(),
            })
        })?;
        let layer_hex = manifest["layers"][0]["digest"]
            .as_str()
            .and_then(digest::parse_oci_digest)
            .ok_or_else(|| {
                Refusal::MalformedDocument { what: "manifest".into(), why: "layer digest".into() }
            })?;
        let file = fs::read(path).map_err(|e| {
            io::Error::new(e.kind(), format!("verify {label}: {}: {e}", path.display()))
        })?;
        let actual = digest::sha256_hex(&file);
        if actual == layer_hex {
            Ok(Verify::Match)
        } else {
            Ok(Verify::Mismatch { stored: layer_hex.to_string(), actual })
        }
    }

    /// The query face: every stored label with its content + badge
    /// digests (reads each manifest — the badges live there). A row
    /// whose manifest is unreadable is SKIPPED, never silently green —
    /// the skip is reported in the row count's place by `list`'s
    /// caller re-running `read` (the honest boundary: list is a
    /// summary, `read` is the verdict).
    pub fn list(&self) -> Vec<StoredRow> {
        let mut rows = Vec::new();
        for (label, manifest_digest) in &self.tags {
            let Ok(bytes) = self.blob(manifest_digest, "manifest") else {
                continue;
            };
            let Ok(m) = serde_json::from_slice::<Value>(&bytes) else {
                continue;
            };
            let (Some(layer), Some(ann)) = (
                m["layers"][0]["digest"].as_str().and_then(digest::parse_oci_digest),
                m["annotations"].as_object(),
            ) else {
                continue;
            };
            let badge = |k: &str| {
                m["annotations"][k]
                    .as_str()
                    .and_then(digest::parse_oci_digest)
                    .unwrap_or_default()
                    .to_string()
            };
            rows.push(StoredRow {
                label: label.clone(),
                manifest_digest: manifest_digest.clone(),
                layer_digest: layer.to_string(),
                axiom_report: badge(prov::AXIOM_REPORT),
                gates_stamp: badge(prov::GATES_STAMP),
            });
            let _ = ann; // the shape verdict is `read`'s; list summarizes
        }
        rows
    }

    /// Write index.json from the tags (sorted — stable bytes; the ONE
    /// writer's pointer document).
    fn write_index(&self) -> io::Result<()> {
        let blobs_dir = self.blobs_dir();
        let mut manifests = Vec::new();
        for (label, manifest_digest) in &self.tags {
            let size = fs::metadata(blobs_dir.join(manifest_digest))
                .map(|m| m.len())
                .unwrap_or(0);
            manifests.push(json!({
                "mediaType": MANIFEST_MT,
                "digest": digest::oci_digest(manifest_digest),
                "size": size,
                "annotations": { prov::LABEL: label },
            }));
        }
        let index = json!({
            "schemaVersion": 2,
            "mediaType": INDEX_MT,
            "manifests": manifests,
        });
        fs::write(self.root.join("index.json"), serde_json::to_string_pretty(&index)?)?;
        Ok(())
    }
}

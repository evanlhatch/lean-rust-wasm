//! OCI image manifest: pack a stored artifact into an image-spec
//! manifest, parse one back (pull path).
//!
//! The config blob is a minimal wasm image config, sha256-addressed in
//! the store like any other blob. The single layer is the artifact blob
//! with media type `application/wasm`. Provenance rides in the
//! manifest-level `annotations` map.

use std::collections::BTreeMap;
use std::io;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::oci::{Digest, OciStore};

pub const MANIFEST_MEDIA_TYPE: &str = "application/vnd.oci.image.manifest.v1+json";
pub const CONFIG_MEDIA_TYPE: &str = "application/vnd.oci.image.config.v1+json";
pub const WASM_MEDIA_TYPE: &str = "application/wasm";

/// Manifest annotation holding the artifact label (repo-root-relative
/// path). Same key the local index.json uses.
pub const REF_NAME_ANNOTATION: &str = "org.opencontainers.image.ref.name";

/// Axiom-gate report annotation. The value is caller-provenance: the
/// verbatim content of an axiom-report file (default "unchecked" when
/// the caller passes no report). forge never runs the gate itself —
/// running lake at pack time is slow and needs the toolchain; the
/// caller (CI, `just lean-axioms`) produces the report, forge ships it.
pub const AXIOMS_ANNOTATION: &str = "com.guestlang.axioms";

/// Lean toolchain (kernel) version annotation.
pub const LEAN_VERSION_ANNOTATION: &str = "com.guestlang.lean.version";

/// Provenance-record schema version annotation.
pub const PROVENANCE_SCHEMA_ANNOTATION: &str = "com.guestlang.provenance.schema";

/// Bump when the annotation set/format above changes shape.
pub const PROVENANCE_SCHEMA_VERSION: &str = "1";

/// Caller-supplied provenance stamped into every packed manifest.
/// `axioms` defaults to "unchecked" (no report passed); `kernel` to
/// "unknown" (no `--lean-version` flag).
#[derive(Debug, Clone)]
pub struct Provenance {
    /// Verbatim axiom-gate report (content of `--axiom-report <path>`).
    pub axioms: String,
    /// Lean toolchain version string (from `lean --version`).
    pub kernel: String,
    /// Provenance-record schema version (forge constant).
    pub schema_version: String,
}

impl Default for Provenance {
    fn default() -> Self {
        Provenance {
            axioms: "unchecked".to_string(),
            kernel: "unknown".to_string(),
            schema_version: PROVENANCE_SCHEMA_VERSION.to_string(),
        }
    }
}

/// A blob reference inside a manifest. `digest` is the bare 64-hex
/// sha256 (the `sha256:` prefix is added on the wire).
#[derive(Debug, Clone)]
pub struct Descriptor {
    pub media_type: String,
    pub digest: Digest,
    pub size: u64,
}

/// An OCI image manifest for one artifact.
#[derive(Debug, Clone)]
pub struct Manifest {
    /// Artifact label (also in `annotations[REF_NAME_ANNOTATION]`).
    pub label: String,
    pub config: Descriptor,
    pub layers: Vec<Descriptor>,
    pub annotations: BTreeMap<String, String>,
}

impl Descriptor {
    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "mediaType": self.media_type,
            "digest": format!("sha256:{}", self.digest),
            "size": self.size,
        })
    }
}

impl Manifest {
    /// All blobs a puller must fetch, in fetch order: config, then layers.
    pub fn blobs(&self) -> impl Iterator<Item = &Descriptor> {
        std::iter::once(&self.config).chain(self.layers.iter())
    }

    /// Serialize to the manifest JSON bytes (what PUT /manifests/<tag> sends).
    pub fn to_bytes(&self) -> Vec<u8> {
        serde_json::to_vec(&self.to_json()).unwrap_or_default()
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "schemaVersion": 2,
            "mediaType": MANIFEST_MEDIA_TYPE,
            "config": self.config.to_json(),
            "layers": self.layers.iter().map(Descriptor::to_json).collect::<Vec<_>>(),
            "annotations": self.annotations,
        })
    }

    /// Parse a manifest from registry bytes (pull path).
    pub fn from_bytes(raw: &[u8]) -> Result<Manifest, String> {
        let v: serde_json::Value =
            serde_json::from_slice(raw).map_err(|e| format!("manifest JSON: {e}"))?;
        let config = descriptor(&v["config"], "config")?;
        let layers = v["layers"]
            .as_array()
            .ok_or("manifest: missing `layers`")?
            .iter()
            .map(|d| descriptor(d, "layer"))
            .collect::<Result<Vec<_>, _>>()?;
        let annotations = v["annotations"]
            .as_object()
            .map(|m| {
                m.iter()
                    .filter_map(|(k, val)| val.as_str().map(|s| (k.clone(), s.to_string())))
                    .collect::<BTreeMap<_, _>>()
            })
            .unwrap_or_default();
        let label = annotations
            .get(REF_NAME_ANNOTATION)
            .ok_or(format!("manifest: missing `{REF_NAME_ANNOTATION}` annotation"))?
            .clone();
        Ok(Manifest {
            label,
            config,
            layers,
            annotations,
        })
    }
}

fn descriptor(v: &serde_json::Value, what: &str) -> Result<Descriptor, String> {
    let digest = v["digest"]
        .as_str()
        .and_then(|d| d.strip_prefix("sha256:"))
        .ok_or(format!("manifest {what}: missing/invalid sha256 digest"))?
        .to_string();
    Ok(Descriptor {
        media_type: v["mediaType"].as_str().unwrap_or_default().to_string(),
        digest,
        size: v["size"].as_u64().unwrap_or(0),
    })
}

/// Build the OCI image manifest for a stored artifact label. The config
/// blob is generated, hashed, and content-addressed into the store as
/// part of packing.
pub fn pack(store: &mut OciStore, label: &str, provenance: &Provenance) -> io::Result<Manifest> {
    let layer_digest = store
        .digest(label)
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!("no stored digest for label `{label}` (run `forge gen --store` first)"),
            )
        })?
        .clone();
    let layer_bytes = store.get(&layer_digest)?;
    let layer = Descriptor {
        media_type: WASM_MEDIA_TYPE.to_string(),
        digest: layer_digest.clone(),
        size: layer_bytes.len() as u64,
    };

    let config_bytes = config_blob(&layer_digest);
    let config_digest = store.put(&format!("{label}.config"), &config_bytes)?;
    let config = Descriptor {
        media_type: CONFIG_MEDIA_TYPE.to_string(),
        digest: config_digest,
        size: config_bytes.len() as u64,
    };

    let mut annotations = BTreeMap::new();
    annotations.insert(REF_NAME_ANNOTATION.to_string(), label.to_string());
    // Real provenance, caller-supplied: no stubs, no gate runs here.
    annotations.insert(AXIOMS_ANNOTATION.to_string(), provenance.axioms.clone());
    annotations.insert(LEAN_VERSION_ANNOTATION.to_string(), provenance.kernel.clone());
    annotations.insert(
        PROVENANCE_SCHEMA_ANNOTATION.to_string(),
        provenance.schema_version.clone(),
    );

    Ok(Manifest {
        label: label.to_string(),
        config,
        layers: vec![layer],
        annotations,
    })
}

/// Minimal wasm image config JSON. `diff_ids` is empty: the layer is a
/// single opaque artifact, not a filesystem diff.
fn config_blob(_layer_digest: &str) -> Vec<u8> {
    let config = serde_json::json!({
        "architecture": "wasm",
        "os": "none",
        "rootfs": { "type": "layers", "diff_ids": [] },
        "created": rfc3339_now(),
    });
    serde_json::to_vec(&config).unwrap_or_default()
}

/// Current UTC time as RFC3339 (`YYYY-MM-DDTHH:MM:SSZ`). Hand-rolled to
/// avoid a chrono dep: civil-from-days over the unix timestamp.
fn rfc3339_now() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (y, m, d) = civil_from_days(days);
    format!(
        "{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}Z",
        rem / 3600,
        (rem % 3600) / 60,
        rem % 60
    )
}

/// Days since 1970-01-01 → (year, month, day). Howard Hinnant's algorithm.
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as u64; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32; // [1, 12]
    (if m <= 2 { y + 1 } else { y }, m, d)
}

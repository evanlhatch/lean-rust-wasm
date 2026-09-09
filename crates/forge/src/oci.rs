//! OCI image-layout store for pipeline artifacts.
//!
//! Content-addressed by xxh3-128 (fast, non-cryptographic — these are
//! local build caches, not security boundaries). The layout follows the
//! OCI image-spec directory structure so standard tooling can inspect
//! it, but the digest algorithm is xxh3 instead of sha256 for speed.
//! Switch to sha256 when registry push/pull is needed.
//!
//! ```text
//! target/oci/
//! ├── oci-layout                    {"imageLayoutVersion":"1.0.0"}
//! ├── index.json                    label → manifest digest (annotations)
//! └── blobs/
//!     └── xxh3/
//!         └── <hex digest>          content-addressed artifact
//! ```

use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use xxhash_rust::xxh3::xxh3_128;

/// xxh3-128 digest as a lowercase hex string (32 chars).
pub type Digest = String;

/// Annotation key holding the artifact label (repo-root-relative path).
const LABEL_ANNOTATION: &str = "org.opencontainers.image.ref.name";

pub struct OciStore {
    root: PathBuf,
    /// label (artifact path) → digest, loaded from index.json at open
    /// and updated by `put`.
    tags: HashMap<String, Digest>,
}

/// Result of `OciStore::verify`.
#[derive(Debug, PartialEq, Eq)]
pub enum Verify {
    /// Store has no digest for this label — nothing to check.
    NotStored,
    /// File hash matches the stored digest.
    Match,
    /// Drift: the file's hash differs from the stored digest.
    Mismatch { stored: Digest, actual: Digest },
}

impl OciStore {
    /// Open (or lazily create) an OCI layout at `root`.
    pub fn open(root: &Path) -> io::Result<Self> {
        let blobs = root.join("blobs/xxh3");
        fs::create_dir_all(&blobs)?;
        let layout = root.join("oci-layout");
        if !layout.exists() {
            fs::write(&layout, r#"{"imageLayoutVersion":"1.0.0"}"#)?;
        }
        let index = root.join("index.json");
        if !index.exists() {
            fs::write(&index, r#"{"schemaVersion":2,"manifests":[]}"#)?;
        }
        let tags = Self::load_tags(&index);
        Ok(Self {
            root: root.to_path_buf(),
            tags,
        })
    }

    /// Read label → digest from an existing index.json. Missing or
    /// malformed entries are skipped (the index is a cache; `--store`
    /// rebuilds it).
    fn load_tags(index: &Path) -> HashMap<String, Digest> {
        let Ok(raw) = fs::read_to_string(index) else {
            return HashMap::new();
        };
        let Ok(value) = serde_json::from_str::<serde_json::Value>(&raw) else {
            return HashMap::new();
        };
        value["manifests"]
            .as_array()
            .map(|manifests| {
                manifests
                    .iter()
                    .filter_map(|m| {
                        let digest = m["digest"].as_str()?.strip_prefix("xxh3:")?.to_string();
                        let label = m["annotations"][LABEL_ANNOTATION].as_str()?.to_string();
                        Some((label, digest))
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn blobs_dir(&self) -> PathBuf {
        self.root.join("blobs/xxh3")
    }

    /// Content-address a blob: hash with xxh3-128, write (unconditionally,
    /// so a corrupted cache blob self-heals on the next --store), record
    /// `label → digest`, return the hex digest.
    pub fn put(&mut self, label: &str, data: &[u8]) -> io::Result<Digest> {
        let digest = xxh3_hex(data);
        fs::write(self.blobs_dir().join(&digest), data)?;
        self.tags.insert(label.to_string(), digest.clone());
        Ok(digest)
    }

    /// Read a blob by digest.
    pub fn get(&self, digest: &str) -> io::Result<Vec<u8>> {
        fs::read(self.blobs_dir().join(digest))
    }

    /// Check if a blob exists (for skip-if-unchanged).
    pub fn has(&self, digest: &str) -> bool {
        self.blobs_dir().join(digest).exists()
    }

    /// Byte-tie a label against the store: look up the stored digest,
    /// read the current file, rehash, and compare. The file is the
    /// authority; the store is the cache. Also re-reads the stored blob
    /// and byte-compares with the file, so a corrupted cache blob is
    /// caught even if the digest entry survived.
    pub fn verify(&self, label: &str, path: &Path) -> io::Result<Verify> {
        let Some(stored) = self.tags.get(label) else {
            return Ok(Verify::NotStored);
        };
        let file = fs::read(path).map_err(|e| {
            io::Error::new(e.kind(), format!("verify {label}: {}: {e}", path.display()))
        })?;
        let actual = xxh3_hex(&file);
        if &actual != stored {
            return Ok(Verify::Mismatch {
                stored: stored.clone(),
                actual,
            });
        }
        // Digest matches; confirm the cached blob bytes too. A corrupted
        // blob self-heals on the next `--store` (put overwrites).
        if let Ok(blob) = self.get(stored) {
            if blob != file {
                return Ok(Verify::Mismatch {
                    stored: stored.clone(),
                    actual,
                });
            }
        }
        Ok(Verify::Match)
    }

    /// Write the label → digest mapping to index.json as OCI manifests
    /// with label annotations.
    pub fn write_index(&self) -> io::Result<()> {
        let blobs_dir = self.blobs_dir();
        let mut manifests = Vec::new();

        // Tagged entries first (sorted for stable output).
        let mut tagged: Vec<_> = self.tags.iter().collect();
        tagged.sort();
        for (label, digest) in tagged {
            let size = fs::metadata(blobs_dir.join(digest))
                .map(|m| m.len())
                .unwrap_or(0);
            manifests.push(serde_json::json!({
                "mediaType": "application/vnd.guestlang.artifact",
                "digest": format!("xxh3:{digest}"),
                "size": size,
                "annotations": { LABEL_ANNOTATION: label },
            }));
        }
        // Any untagged blobs (e.g. from a previous run) stay inspectable.
        let mut seen: Vec<_> = self.tags.values().cloned().collect();
        seen.sort();
        if blobs_dir.exists() {
            let mut entries: Vec<_> = fs::read_dir(&blobs_dir)?
                .filter_map(|e| e.ok())
                .map(|e| e.file_name().to_string_lossy().to_string())
                .filter(|d| !seen.contains(d))
                .collect();
            entries.sort();
            for digest in entries {
                let size = fs::metadata(blobs_dir.join(&digest))
                    .map(|m| m.len())
                    .unwrap_or(0);
                manifests.push(serde_json::json!({
                    "mediaType": "application/vnd.guestlang.artifact",
                    "digest": format!("xxh3:{digest}"),
                    "size": size,
                }));
            }
        }

        let index = serde_json::json!({
            "schemaVersion": 2,
            "manifests": manifests,
        });
        fs::write(
            self.root.join("index.json"),
            serde_json::to_string_pretty(&index)?,
        )?;
        Ok(())
    }
}

/// Store a list of (label, path) pairs: hash + write each artifact into
/// the store, return the label → digest mapping.
pub fn store_artifacts(
    store: &mut OciStore,
    artifacts: &[(&str, &Path)],
) -> io::Result<HashMap<String, Digest>> {
    let mut digests = HashMap::new();
    for (label, path) in artifacts {
        let data = fs::read(path).map_err(|e| {
            io::Error::new(e.kind(), format!("store {label}: {}: {e}", path.display()))
        })?;
        let digest = store.put(label, &data)?;
        digests.insert((*label).to_string(), digest);
    }
    Ok(digests)
}

/// xxh3-128 hex digest (32 hex chars, 128 bits).
fn xxh3_hex(data: &[u8]) -> Digest {
    format!("{:032x}", xxh3_128(data))
}

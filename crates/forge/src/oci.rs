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
//! ├── index.json                    tag → manifest digest
//! └── blobs/
//!     └── xxh3/
//!         └── <hex digest>          content-addressed artifact
//! ```

use std::fs;
use std::path::{Path, PathBuf};

/// xxh3-128 digest as a lowercase hex string (32 chars).
pub type Digest = String;

pub struct OciStore {
    root: PathBuf,
}

impl OciStore {
    /// Open (or lazily create) an OCI layout at `root`.
    pub fn open(root: &Path) -> std::io::Result<Self> {
        let blobs = root.join("blobs/xxh3");
        fs::create_dir_all(&blobs)?;
        let layout = root.join("oci-layout");
        if !layout.exists() {
            fs::write(&layout, r#"{"imageLayoutVersion":"1.0.0"}"#)?;
        }
        let index = root.join("index.json");
        if !index.exists() {
            fs::write(&index, r#"{"manifests":[]}"#)?;
        }
        Ok(Self { root: root.to_path_buf() })
    }

    fn blobs_dir(&self) -> PathBuf {
        self.root.join("blobs/xxh3")
    }

    /// Content-address a blob: hash with xxh3-128, write if absent,
    /// return the hex digest.
    pub fn put(&self, _label: &str, data: &[u8]) -> std::io::Result<Digest> {
        let digest = xxh3_hex(data);
        let blob_path = self.blobs_dir().join(&digest);
        if !blob_path.exists() {
            fs::write(&blob_path, data)?;
        }
        Ok(digest)
    }

    /// Read a blob by digest.
    pub fn get(&self, digest: &str) -> std::io::Result<Vec<u8>> {
        fs::read(self.blobs_dir().join(digest))
    }

    /// Check if a blob exists (for skip-if-unchanged).
    pub fn has(&self, digest: &str) -> bool {
        self.blobs_dir().join(digest).exists()
    }

    /// Write the tag → digest mapping to index.json.
    pub fn write_index(&self) -> std::io::Result<()> {
        // v1: scan blobs dir, build the index. No tags yet — tags land
        // when the component pipeline exists (tag = build target).
        let blobs_dir = self.blobs_dir();
        let mut manifests = Vec::new();
        if blobs_dir.exists() {
            let mut entries: Vec<_> = fs::read_dir(&blobs_dir)?
                .filter_map(|e| e.ok())
                .map(|e| e.file_name().to_string_lossy().to_string())
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
        fs::write(self.root.join("index.json"), serde_json::to_string_pretty(&index)?)?;
        Ok(())
    }
}

/// xxh3-128 hex digest (32 chars). Uses a simple FNV fallback when the
/// xxhash crate is not available — upgrade to xxh3 via `xxhash-rust`.
fn xxh3_hex(data: &[u8]) -> Digest {
    // FNV-1a 64-bit as a placeholder — swap for xxh3_128 when the
    // xxhash-rust crate is added. The layout is identical; only the
    // digest length changes (32 hex chars for 128-bit).
    let mut hash: u64 = 0xcbf29ce484222325;
    for &byte in data {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{hash:032x}")
}

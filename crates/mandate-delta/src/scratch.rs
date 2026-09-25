//! The scratch-directory face: per-run unique temp dirs under the
//! system temp dir — the tests' isolation AND the duel's per-row
//! journal fixtures (std-only: no tempfile dep — the one-dependency
//! rule reaches the dev faces).

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

/// A unique scratch directory `<tmp>/<tag>-<pid>-<nanos>`, created at
/// construction and removed on drop. The drop's removal is
/// BEST-EFFORT (drop cannot report): a caller that must observe the
/// cleanup removes the directory itself before dropping.
#[derive(Debug)]
pub struct ScratchDir {
    path: PathBuf,
    tag: OsString,
}

impl ScratchDir {
    /// Creates the unique scratch directory.
    ///
    /// # Errors
    /// `std::fs` create failure (the system temp dir unwritable).
    pub fn new(tag: &str) -> Result<Self, std::io::Error> {
        let stamp = format!(
            "{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        );
        let path = std::env::temp_dir().join(&stamp);
        std::fs::create_dir_all(&path)?;
        Ok(Self { path, tag: stamp.into() })
    }

    /// The scratch directory's path.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The unique stamp (the cleanup diagnostics' face).
    #[must_use]
    pub fn stamp(&self) -> &OsStr {
        &self.tag
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        // Best effort — drop cannot report; the temp dir is the
        // system's to reclaim either way.
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

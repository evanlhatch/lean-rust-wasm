//! The persistence seam: the delta-log API available to the host — the
//! honest minimal (the full lifecycle integration is a later order).
//!
//! WHAT THIS IS (notes/v3/13-interfaces.md, the delta-log row):
//! `mandate-delta` is the byte-exact port of SchemaCore's journal
//! codec; this module EXPOSES it beside the host so a component's
//! effects can land in the journal — `record` is the seam the
//! component lane calls when an accepted effect fires (the journal
//! written ON the effect, never beside a hypothetical one). WHAT THIS
//! ISN'T: no second semantics — the state, the wire, and the crash
//! recovery are `mandate-delta`'s (which is SchemaCore's), the host
//! only wires the API to a path.

use std::path::Path;

use mandate_delta::{Delta, DeltaLog, FsBackend, Recovery, Schema};

use crate::HostError;

/// A file-backed delta journal beside the host: open (with the honest
/// crash recovery — a torn tail is cut to the last good frame and the
/// cut REPORTED), record deltas, read the materialized state.
#[derive(Debug)]
pub struct Journal {
    log: DeltaLog<FsBackend>,
}

impl Journal {
    /// Open (or create) the journal at `path` over `schema`.
    ///
    /// # Errors
    /// I/O failure, or a corrupt COMPLETE frame (the typed refusal —
    /// a torn tail recovers; corruption never silently truncates).
    pub fn open(path: &Path, schema: Schema) -> Result<Self, HostError> {
        let log = DeltaLog::open(path, schema).map_err(HostError::from)?;
        Ok(Self { log })
    }

    /// THE EFFECT SEAM: record one accepted delta — the journal write
    /// that rides the component's effect (append + fsync before the
    /// call returns). Returns the entry's sequence number.
    ///
    /// # Errors
    /// The delta's payload doesn't match the journal's schema, or the
    /// backend I/O failed.
    pub fn record(&mut self, delta: Delta) -> Result<u64, HostError> {
        self.log.append(delta).map_err(HostError::from)
    }

    /// The materialized state (the full replay).
    #[must_use]
    pub fn state(&self) -> &mandate_delta::delta::Table {
        self.log.state()
    }

    /// The entry count.
    #[must_use]
    pub fn len(&self) -> u64 {
        self.log.len()
    }

    /// Is the journal empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.log.is_empty()
    }

    /// The recovery report of the open (`None` = the journal loaded
    /// clean end to end — a torn tail never went silently unreported).
    #[must_use]
    pub fn recovery(&self) -> Option<&Recovery> {
        self.log.recovery()
    }

    /// The whole-log wire form (`SchemaCore.Event.encJournal`'s bytes —
    /// the byte-exactness surface the Lean side can duel).
    #[must_use]
    pub fn journal_bytes(&self) -> Vec<u8> {
        self.log.journal_bytes()
    }
}

// (the `DeltaError` → `HostError` conversion rides the `#[from]` on
// `HostError::Journal` — thiserror's single conversion).

#[cfg(test)]
mod tests {
    use super::*;
    use mandate_delta::schema::{Field, Row};
    use mandate_delta::value::{Ty, Value};

    fn schema() -> Schema {
        Schema::build(
            vec![
                Field { name: "id".into(), ty: Ty::U64 },
                Field { name: "name".into(), ty: Ty::Str },
            ],
            "id",
        )
        .unwrap_or_else(|e| panic!("schema: {e}"))
    }

    fn row(id: u64, name: &str) -> Row {
        Row::build(&schema(), vec![Value::U64(id), Value::Str(name.into())])
            .unwrap_or_else(|e| panic!("row: {e}"))
    }

    /// The persistence round trip: record effects, drop, reopen — the
    /// state and the wire form survive.
    #[test]
    fn record_reopen_round_trip() {
        let dir = std::env::temp_dir().join(format!(
            "mandate-host-journal-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        std::fs::create_dir_all(&dir).unwrap_or_else(|e| panic!("tempdir: {e}"));
        let path = dir.join("journal.bin");
        {
            let mut j = Journal::open(&path, schema()).unwrap_or_else(|e| panic!("{e}"));
            assert!(j.recovery().is_none(), "a fresh journal reports no recovery");
            let seq = j.record(Delta::Insert(row(1, "a"))).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(seq, 0);
            j.record(Delta::Remove(Value::U64(1))).unwrap_or_else(|e| panic!("{e}"));
            assert!(j.state().rows().is_empty());
        }
        {
            let j = Journal::open(&path, schema()).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(j.len(), 2);
            assert!(j.recovery().is_none(), "a clean journal reports no recovery");
            assert!(j.state().rows().is_empty());
        }
        std::fs::remove_dir_all(&dir).unwrap_or_else(|e| panic!("cleanup: {e}"));
    }
}

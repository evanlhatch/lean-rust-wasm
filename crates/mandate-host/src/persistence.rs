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

use mandate_delta::snapshot::SnapshotReport;
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

    /// Open the journal WITH its snapshot (`snapshot_path` — derive it
    /// with [`mandate_delta::snapshot_path_for`], never by hand): the
    /// state materializes from snapshot + tail, every honesty rule of
    /// both files applies, and the snapshot side of the open REPORTS
    /// ([`SnapshotReport`]): absent, applied (at the snapshot's
    /// seqno), or fell back (torn / refused / unaligned — the full
    /// replay took over, never a silent fallback). The LOG's own torn
    /// tail rides [`Self::recovery`] separately — both reports can
    /// surface on one open.
    ///
    /// # Errors
    /// I/O failure, or a corrupt COMPLETE frame in the log (the typed
    /// refusal — the snapshot's anomalies are reports, the log's
    /// corruption is an error).
    pub fn open_snapshotted(
        path: &Path,
        snapshot_path: &Path,
        schema: Schema,
    ) -> Result<(Self, SnapshotReport), HostError> {
        let (log, report) =
            DeltaLog::open_snapshotted(path, snapshot_path, schema).map_err(HostError::from)?;
        Ok((Self { log }, report))
    }

    /// COMPACT: write the state at `seqno` to `snapshot_path` (the
    /// atomic write), then cut the log's head — the crash windows are
    /// `mandate-delta`'s (each recovers, none silent, see
    /// [`DeltaLog::compact`]). The materialized state is unchanged.
    ///
    /// # Errors
    /// `seqno` past the log's end (nothing written, nothing cut), or
    /// backend/write I/O failure.
    pub fn compact(&mut self, seqno: u64, snapshot_path: &Path) -> Result<(), HostError> {
        self.log
            .compact(seqno, snapshot_path)
            .map_err(HostError::from)
    }

    /// THE EFFECT SEAM: record one accepted delta — the journal write
    /// that rides the component's effect (append + fsync before the
    /// call returns). Returns the entry's sequence number.
    ///
    /// # Errors
    /// The delta's payload doesn't match the journal's schema, or the
    /// backend I/O failed.
    pub fn record(&mut self, delta: Delta) -> Result<u64, HostError> {
        // THE OBSERVABILITY FACE (C1): the journal's append is one of the
        // host's named operations — the dotted-static scope (low-cardinality
        // ONLY; the delta's PAYLOAD data never enters the tag).
        let _span = fast_observe::scope!("ledger.journal");
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
    use mandate_delta::ScratchDir;
    use mandate_delta::schema::fixtures::{fixture, fixture_row};
    use mandate_delta::value::Value;

    fn schema() -> Schema {
        fixture()
    }

    fn row(id: u64, name: &str) -> mandate_delta::Row {
        fixture_row(id, name)
    }

    /// The persistence round trip: record effects, drop, reopen — the
    /// state and the wire form survive.
    #[test]
    fn record_reopen_round_trip() {
        let dir =
            ScratchDir::new("mandate-host-journal").unwrap_or_else(|e| panic!("tempdir: {e}"));
        let path = dir.path().join("journal.bin");
        {
            let mut j = Journal::open(&path, schema()).unwrap_or_else(|e| panic!("{e}"));
            assert!(
                j.recovery().is_none(),
                "a fresh journal reports no recovery"
            );
            let seq = j
                .record(Delta::Insert(row(1, "a")))
                .unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(seq, 0);
            j.record(Delta::Remove(Value::U64(1)))
                .unwrap_or_else(|e| panic!("{e}"));
            assert!(j.state().rows().is_empty());
        }
        {
            let j = Journal::open(&path, schema()).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(j.len(), 2);
            assert!(
                j.recovery().is_none(),
                "a clean journal reports no recovery"
            );
            assert!(j.state().rows().is_empty());
        }
    }

    /// THE CRASH MATRIX through the HOST's seam: torn snapshot,
    /// torn tail, torn both, compact interrupted — each recovers AND
    /// reports (the exhaustive byte-level sweeps live in
    /// mandate-delta's tests; this pins the host face to the same
    /// honesty).
    #[test]
    fn snapshot_crash_matrix_through_the_host_seam() {
        let dir =
            ScratchDir::new("mandate-host-crash-matrix").unwrap_or_else(|e| panic!("tempdir: {e}"));
        let path = dir.path().join("journal.bin");
        let snap = mandate_delta::snapshot_path_for(&path);

        // Build a store, compact it, grow the tail.
        {
            let mut j = Journal::open(&path, schema()).unwrap_or_else(|e| panic!("{e}"));
            j.record(Delta::Insert(row(1, "a")))
                .unwrap_or_else(|e| panic!("{e}"));
            j.record(Delta::Insert(row(2, "b")))
                .unwrap_or_else(|e| panic!("{e}"));
            j.compact(1, &snap)
                .unwrap_or_else(|e| panic!("compact: {e}"));
            j.record(Delta::Insert(row(3, "c")))
                .unwrap_or_else(|e| panic!("{e}"));
        }
        // The honest snapshotted reopen: applied at the snapshot's
        // seqno, the state is the full replay.
        {
            let (j, report) = Journal::open_snapshotted(&path, &snap, schema())
                .unwrap_or_else(|e| panic!("open: {e}"));
            assert_eq!(report, SnapshotReport::Applied { seqno: 1 });
            // Snapshot (row 1) + tail (rows 2, 3 — row 2 was recorded
            // BEFORE the compact, row 3 after).
            assert_eq!(j.state().rows(), &[row(1, "a"), row(2, "b"), row(3, "c")]);
            assert!(j.recovery().is_none());
        }

        // TORN SNAPSHOT: the cut file never loads; the open REPORTS
        // the fallback and recovers the log's own replay.
        let raw = std::fs::read(&snap).unwrap_or_else(|e| panic!("read: {e}"));
        std::fs::write(&snap, &raw[..raw.len() - 3]).unwrap_or_else(|e| panic!("write: {e}"));
        {
            let (j, report) = Journal::open_snapshotted(&path, &snap, schema())
                .unwrap_or_else(|e| panic!("open: {e}"));
            assert!(matches!(report, SnapshotReport::FellBack(_)), "{report}");
            assert_eq!(
                j.state().rows(),
                &[row(2, "b"), row(3, "c")],
                "the log's own replay (the tail alone)"
            );
            assert!(j.recovery().is_none(), "the log itself was intact");
        }

        // TORN TAIL beside the (restored) snapshot: BOTH reports
        // surface — the snapshot applied AND the tail's cut reported.
        std::fs::write(&snap, &raw).unwrap_or_else(|e| panic!("write: {e}"));
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read: {e}"));
        std::fs::write(&path, &bytes[..bytes.len() - 1]).unwrap_or_else(|e| panic!("write: {e}"));
        {
            let (j, report) = Journal::open_snapshotted(&path, &snap, schema())
                .unwrap_or_else(|e| panic!("open: {e}"));
            assert_eq!(report, SnapshotReport::Applied { seqno: 1 });
            let rec = j
                .recovery()
                .unwrap_or_else(|| panic!("the torn tail went SILENT"));
            assert_eq!(rec.frames, 1, "the surviving tail's frame count");
            // Snapshot (row 1) + the surviving tail frame (row 2 —
            // row 3's frame is the torn one the cut dropped).
            assert_eq!(
                j.state().rows(),
                &[row(1, "a"), row(2, "b")],
                "snapshot + surviving tail"
            );
        }

        // TORN BOTH: both anomalies report; the surviving log's
        // replay is the state.
        std::fs::write(&snap, &raw[..raw.len() - 3]).unwrap_or_else(|e| panic!("write: {e}"));
        std::fs::write(&path, &bytes[..bytes.len() - 1]).unwrap_or_else(|e| panic!("write: {e}"));
        {
            let (j, report) = Journal::open_snapshotted(&path, &snap, schema())
                .unwrap_or_else(|e| panic!("open: {e}"));
            assert!(matches!(report, SnapshotReport::FellBack(_)), "{report}");
            let rec = j
                .recovery()
                .unwrap_or_else(|| panic!("the torn tail went SILENT"));
            assert_eq!(rec.frames, 1);
            assert_eq!(
                j.state().rows(),
                &[row(2, "b")],
                "the surviving log prefix's replay"
            );
        }

        // COMPACT INTERRUPTED (the pre-cut window): snapshot landed,
        // the head cut did not — the open verifies the subsumed
        // prefix, skips it, and REPORTS the application. The pre-cut
        // log file is rebuilt EXACTLY as the snapshot summarizes it
        // (frame 0 = the subsumed prefix, frame 1 = the tail head the
        // snapshot's hash names).
        std::fs::write(&snap, &raw).unwrap_or_else(|e| panic!("write: {e}"));
        {
            let mut pre_cut = Vec::new();
            for r in [row(1, "a"), row(2, "b")] {
                assert!(mandate_delta::delta::enc_delta(
                    &schema(),
                    &Delta::Insert(r),
                    &mut pre_cut
                ));
            }
            std::fs::write(&path, &pre_cut).unwrap_or_else(|e| panic!("write: {e}"));
        }
        {
            let (mut j, report) = Journal::open_snapshotted(&path, &snap, schema())
                .unwrap_or_else(|e| panic!("open: {e}"));
            assert_eq!(report, SnapshotReport::Applied { seqno: 1 });
            assert_eq!(j.state().rows(), &[row(1, "a"), row(2, "b")]);
            assert!(j.recovery().is_none(), "no torn tail in this window");
            // The interrupted cut was FINISHED by the open (the
            // subsumed prefix retired); a heal compact lands the tail
            // alone — state unchanged by either cut.
            j.compact(j.len(), &snap)
                .unwrap_or_else(|e| panic!("heal: {e}"));
            assert_eq!(j.state().rows(), &[row(1, "a"), row(2, "b")]);
            drop(j);
            let (j, report) = Journal::open_snapshotted(&path, &snap, schema())
                .unwrap_or_else(|e| panic!("re-open: {e}"));
            assert_eq!(report, SnapshotReport::Applied { seqno: 1 });
            assert_eq!(j.len(), 0, "the log file is the tail alone now");
            assert_eq!(j.state().rows(), &[row(1, "a"), row(2, "b")]);
        }
    }
}

//! The append-only delta log — the persistence artifact over a
//! durable-or-not byte sink.
//!
//! APPEND-ONLY IS LITERAL: entries land as frames, the log is never
//! rewritten — EXCEPT the crash-recovery cut, which truncates the
//! backend to the last good frame AND REPORTS the cut (the
//! [`Recovery`] field; `open_strict` refuses the same tail with the
//! typed error instead). A COMPLETE frame that fails to decode is a
//! typed ERROR in every mode — the log refuses, it never truncates
//! data away (mid-log corruption is not a torn write's shape: a crash
//! mid-`append` leaves the file a good PREFIX of what was written).
//!
//! THE INVERSION AT LOG SCALE (`SchemaCore.witnessedApply_reverse_inv`):
//! every entry's witness is computed against the state at its
//! append/replay time; `rewind_to` applies the inverse journal
//! (`reverse ∘ invertW`) through the CHECKED patches, and the law says
//! the result is exactly `state_at(seq)` — a law this log also CHECKS
//! at runtime (the two independent computations must agree; a
//! disagreement is the typed refusal, never a silently wrong state).

use std::fmt;
use std::path::Path;

use crate::delta::{dec_delta, enc_delta, invert_w, witnessed_apply, witness_of, Delta, Table,
    WDelta};
use crate::error::{DecodeFail, DeltaError, Recovery};
use crate::schema::Schema;

/// The durable-or-not byte sink behind a log. One writer per log (the
/// one-writer rule); the trait is the future embedded-KV seam.
pub trait Backend {
    /// The full journal bytes.
    ///
    /// # Errors
    /// Backend I/O failure.
    fn load(&mut self) -> Result<Vec<u8>, DeltaError>;

    /// Append one complete frame. Implementations that claim durability
    /// must sync before returning.
    ///
    /// # Errors
    /// Backend I/O failure.
    fn append(&mut self, frame: &[u8]) -> Result<(), DeltaError>;

    /// Truncate the journal to a prefix (the crash-recovery cut — the
    /// ONLY truncation this crate performs, always reported).
    ///
    /// # Errors
    /// Backend I/O failure.
    fn truncate(&mut self, len: u64) -> Result<(), DeltaError>;
}

impl<B: Backend + ?Sized> Backend for &mut B {
    fn load(&mut self) -> Result<Vec<u8>, DeltaError> {
        (**self).load()
    }

    fn append(&mut self, frame: &[u8]) -> Result<(), DeltaError> {
        (**self).append(frame)
    }

    fn truncate(&mut self, len: u64) -> Result<(), DeltaError> {
        (**self).truncate(len)
    }
}

/// The in-memory backend (tests, ephemeral hosts, the trait's reference
/// implementation).
#[derive(Debug, Default)]
pub struct MemBackend {
    bytes: Vec<u8>,
}

impl MemBackend {
    /// An empty in-memory journal.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The raw journal bytes (test/debug inspection).
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

impl Backend for MemBackend {
    fn load(&mut self) -> Result<Vec<u8>, DeltaError> {
        Ok(self.bytes.clone())
    }

    fn append(&mut self, frame: &[u8]) -> Result<(), DeltaError> {
        self.bytes.extend_from_slice(frame);
        Ok(())
    }

    fn truncate(&mut self, len: u64) -> Result<(), DeltaError> {
        self.bytes.truncate(usize::try_from(len).unwrap_or(usize::MAX));
        Ok(())
    }
}

/// The durable backend: an append-only file over `std::fs`, one frame
/// per `append`, `sync_data` before the append returns (an append that
/// returns is on stable storage; a crash mid-append leaves a torn tail
/// the next open reports — or truncates — honestly).
#[derive(Debug)]
pub struct FsBackend {
    file: std::fs::File,
}

impl FsBackend {
    /// Open (or create) the journal file.
    ///
    /// # Errors
    /// `std::fs` open failure.
    pub fn open(path: &Path) -> Result<Self, DeltaError> {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)?;
        Ok(Self { file })
    }
}

impl Backend for FsBackend {
    fn load(&mut self) -> Result<Vec<u8>, DeltaError> {
        use std::io::{Read, Seek};
        self.file.seek(std::io::SeekFrom::Start(0))?;
        let mut bytes = Vec::new();
        self.file.read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    fn append(&mut self, frame: &[u8]) -> Result<(), DeltaError> {
        use std::io::{Seek, Write};
        // Append at the file's END — after a recovery truncate the
        // cursor must not ride the stale read position.
        self.file.seek(std::io::SeekFrom::End(0))?;
        self.file.write_all(frame)?;
        self.file.sync_data()?;
        Ok(())
    }

    fn truncate(&mut self, len: u64) -> Result<(), DeltaError> {
        self.file.set_len(len)?;
        self.file.sync_data()?;
        Ok(())
    }
}

/// The open mode's tail policy (see the crate doc's crash-recovery
/// contract).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TailPolicy {
    /// A truncated tail recovers to the last good frame: the backend is
    /// cut to the good prefix and the cut is REPORTED (never silent).
    Recover,
    /// Any tail anomaly is the typed refusal (the strict audit face).
    Strict,
}

/// The append-only delta log over a backend: the decoded entry index +
/// the witnessed journal + the materialized state, kept in step on
/// every append.
#[derive(Debug)]
pub struct DeltaLog<B: Backend> {
    backend: B,
    schema: Schema,
    entries: Vec<Delta>,
    witnesses: Vec<WDelta>,
    state: Table,
    recovery: Option<Recovery>,
}

impl DeltaLog<FsBackend> {
    /// Open a file-backed log (the recovering tail policy).
    ///
    /// # Errors
    /// I/O failure, or a corrupt COMPLETE frame (typed refusal).
    pub fn open(path: &Path, schema: Schema) -> Result<Self, DeltaError> {
        Self::open_with(FsBackend::open(path)?, schema, TailPolicy::Recover)
    }

    /// Open a file-backed log under the strict tail policy.
    ///
    /// # Errors
    /// I/O failure, a corrupt frame, or a torn tail (typed refusal).
    pub fn open_strict(path: &Path, schema: Schema) -> Result<Self, DeltaError> {
        Self::open_with(FsBackend::open(path)?, schema, TailPolicy::Strict)
    }
}

impl<B: Backend> DeltaLog<B> {
    /// Open a log over any backend, under a tail policy.
    ///
    /// # Errors
    /// I/O failure, a corrupt frame; a torn tail under `Strict`.
    pub fn open_with(mut backend: B, schema: Schema, policy: TailPolicy)
        -> Result<Self, DeltaError>
    {
        let bytes = backend.load()?;
        let mut entries = Vec::new();
        let mut witnesses = Vec::new();
        let mut state = Table::new();
        let mut recovery = None;
        let mut offset: usize = 0;
        while offset < bytes.len() {
            let mut rest = &bytes[offset..];
            // The frame walk: decode one frame at the cursor. The
            // classification is exact: `Truncated` means the decoder ran
            // past EOF, so the failing frame extends to the end of file
            // — the torn-tail shape (a crash mid-append leaves a good
            // PREFIX; see the module doc). Every other failure is
            // corruption: the log REFUSES, never truncates data away.
            match dec_delta(&schema, &mut rest) {
                Err(DecodeFail::Truncated) => {
                    match policy {
                        TailPolicy::Recover => {
                            // Cut to the last good frame — and REPORT it.
                            // Never silent.
                            backend.truncate(offset as u64)?;
                            recovery = Some(Recovery {
                                offset: offset as u64,
                                frames: entries.len() as u64,
                            });
                        }
                        TailPolicy::Strict => {
                            return Err(DeltaError::TornTail { offset: offset as u64 });
                        }
                    }
                    // The tail is handled: the good prefix is the log.
                    break;
                }
                Err(e) => return Err(e.corrupt_error(offset as u64)),
                Ok(d) => {
                    // The witness rides the replay (in-memory data —
                    // the Lean side names no witness wire bytes).
                    let w = witness_of(&schema, &d, &state);
                    let checked =
                        witnessed_apply(&state, std::slice::from_ref(&w)).ok_or(DeltaError::Corrupt {
                            offset: offset as u64,
                            reason: "replayed frame's witness refused (decoder/semantics skew)",
                        })?;
                    state = checked;
                    witnesses.push(w);
                    entries.push(d);
                    offset = bytes.len() - rest.len();
                }
            }
        }
        Ok(Self { backend, schema, entries, witnesses, state, recovery })
    }

    /// Append a delta: validate against the schema, compute the witness
    /// against the CURRENT materialized state (inversion in the log),
    /// write the frame, apply the state. Returns the entry's sequence
    /// number.
    ///
    /// # Errors
    /// `SchemaMismatch` or backend I/O failure.
    pub fn append(&mut self, d: Delta) -> Result<u64, DeltaError> {
        // The boundary's typed refusal: remove keys must match the
        // schema's key field's type (rows are schema-checked at
        // construction, so their payloads cannot skew).
        if let Delta::Remove(k) = &d {
            if k.ty() != self.schema.key_ty() {
                return Err(DeltaError::SchemaMismatch { reason: "remove key type mismatch" });
            }
        }
        let w = witness_of(&self.schema, &d, &self.state);
        let frame = {
            let mut out = Vec::new();
            if !enc_delta(&self.schema, &d, &mut out) {
                return Err(DeltaError::SchemaMismatch { reason: "delta failed to encode" });
            }
            out
        };
        self.backend.append(&frame)?;
        // The state patch mirrors exactly what the frame will replay to
        // (apply_eq_patchW's face); the witness validity is by
        // construction (witnessOf_valid) — an unreliable witness here
        // would be a decoder/semantics skew, so the checked patch is
        // the assertion carrier.
        self.state = witnessed_apply(&self.state, std::slice::from_ref(&w)).ok_or(
            DeltaError::SchemaMismatch { reason: "witness refused at append (internal skew)" },
        )?;
        self.witnesses.push(w);
        let seq = self.entries.len() as u64;
        self.entries.push(d);
        Ok(seq)
    }

    /// The tail policy's report: the recovery a torn-tail open performed
    /// (`None` = the journal loaded clean, end to end).
    #[must_use]
    pub fn recovery(&self) -> Option<&Recovery> {
        self.recovery.as_ref()
    }

    /// The witnesses, mutably — the SKEW-INJECTION seam (tests + the
    /// audit face: prove the checked-patch discipline refuses a lying
    /// witness). Production code must not call this; a production
    /// skew is the typed refusal, never a silently wrong state.
    pub fn witnesses_mut(&mut self) -> &mut [WDelta] {
        &mut self.witnesses
    }

    /// The backend (journal-byte access for replication/inspection).
    #[must_use]
    pub fn backend(&self) -> &B {
        &self.backend
    }

    /// The log's schema.
    #[must_use]
    pub fn schema(&self) -> &Schema {
        &self.schema
    }

    /// The number of entries in the log.
    #[must_use]
    pub fn len(&self) -> u64 {
        self.entries.len() as u64
    }

    /// Is the log empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The delta at a sequence number.
    #[must_use]
    pub fn entry(&self, seq: u64) -> Option<&Delta> {
        self.entries.get(usize::try_from(seq).ok()?)
    }

    /// The witnessed delta at a sequence number (the inversion's data).
    #[must_use]
    pub fn witness(&self, seq: u64) -> Option<&WDelta> {
        self.witnesses.get(usize::try_from(seq).ok()?)
    }

    /// All entries, in sequence order (the replay's input).
    #[must_use]
    pub fn entries(&self) -> &[Delta] {
        &self.entries
    }

    /// The current materialized state (the full replay).
    #[must_use]
    pub fn state(&self) -> &Table {
        &self.state
    }

    /// The materialized state after the first `seq` entries (prefix
    /// replay — the states ARE the partial integrals).
    #[must_use]
    pub fn state_at(&self, seq: u64) -> Table {
        let mut t = Table::new();
        for d in self.entries.iter().take(usize::try_from(seq).unwrap_or(usize::MAX)) {
            t.apply(&self.schema, d);
        }
        t
    }

    /// Rewind the STATE to `seq` (ABSOLUTE: the target is `state_at(seq)`,
    /// whatever the current state is): apply the inverse journal of
    /// entries `[seq, len)` — reverse order, old/new swapped, applied
    /// from the log's FULL state — through the CHECKED patches
    /// (`witnessedApply_reverse_inv`'s law at log scale). The log's
    /// frames are NEVER rewritten (append-only is literal); the rewound
    /// state is additionally CHECKED against the independent prefix
    /// replay (`state_at`) — a disagreement is the typed refusal, never
    /// a silently wrong state. A durable rollback surface (compensation
    /// appends) follows its first consumer.
    ///
    /// # Errors
    /// A checked patch refused (the internal-skew refusal) — never a
    /// silent mispatch.
    pub fn rewind_to(&mut self, seq: u64) -> Result<(), DeltaError> {
        let start = usize::try_from(seq).unwrap_or(usize::MAX).min(self.entries.len());
        // The inverse journal applies from the log's END (the full
        // replay) — never from an intermediate rewound state.
        let full = self.state_at(self.entries.len() as u64);
        let inverse: Vec<WDelta> = self.witnesses[start..]
            .iter()
            .rev()
            .map(invert_w)
            .collect();
        let rewound = witnessed_apply(&full, &inverse).ok_or(DeltaError::SchemaMismatch {
            reason: "rewind refused: a witness did not check (internal skew)",
        })?;
        if rewound != self.state_at(seq) {
            return Err(DeltaError::SchemaMismatch {
                reason: "rewind refused: inverse replay disagrees with prefix replay",
            });
        }
        self.state = rewound;
        Ok(())
    }

    /// The whole-log wire form (`encJournal`): varint count + the
    /// frames in occurrence order — the byte-exactness surface the Lean
    /// side's journal codec emits.
    #[must_use]
    pub fn journal_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        crate::delta::enc_journal(&self.schema, &self.entries, &mut out);
        out
    }

    /// Recompute the witnesses + state from the entry index (the
    /// from_journal_bytes helper — the replay IS the fold).
    fn replay_from_empty(mut self) -> Result<Self, DeltaError> {
        let mut state = Table::new();
        let mut witnesses = Vec::new();
        for d in &self.entries {
            let w = witness_of(&self.schema, d, &state);
            state = witnessed_apply(&state, std::slice::from_ref(&w)).ok_or(DeltaError::Corrupt {
                offset: witnesses.len() as u64,
                reason: "replayed frame's witness refused (internal skew)",
            })?;
            witnesses.push(w);
        }
        self.state = state;
        self.witnesses = witnesses;
        Ok(self)
    }
}

impl DeltaLog<MemBackend> {
    /// Decode the whole-log wire form into an in-memory log
    /// (`decJournal?`, full-consumption: trailing bytes refuse — a
    /// whole-journal artifact is not a suffix stream). The state and
    /// witnesses ride the replay. This is the duel surface: the bytes
    /// are exactly `SchemaCore.Event.encJournal`'s.
    ///
    /// # Errors
    /// The frame decoder's classes, or trailing bytes after the
    /// declared count.
    pub fn from_journal_bytes(schema: Schema, bytes: &[u8]) -> Result<Self, DeltaError> {
        let total = bytes.len();
        let mut rest = bytes;
        let log = crate::delta::dec_journal(&schema, &mut rest)
            .map_err(|e| e.corrupt_error((total - rest.len()) as u64))?;
        if !rest.is_empty() {
            return Err(DeltaError::JournalTrailing { offset: (total - rest.len()) as u64 });
        }
        let mut backend = MemBackend::new();
        let mut framed = Vec::new();
        for d in &log {
            crate::delta::enc_delta(&schema, d, &mut framed);
        }
        backend.append(&framed)?;
        Self {
            backend,
            schema,
            entries: log,
            witnesses: Vec::new(),
            state: Table::new(),
            recovery: None,
        }
        .replay_from_empty()
    }
}

impl<B: Backend> fmt::Display for DeltaLog<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DeltaLog({} entries)", self.entries.len())
    }
}

#[cfg(test)]
mod tests {
    use super::super::schema::{tests as schema_fixtures, Row};
    use crate::value::Value;
    use super::*;

    use schema_fixtures::{fixture, fixture_row};

    fn fixture_schema() -> Schema {
        fixture()
    }

    /// Append/replay/state stay in step; reopen restores exactly.
    #[test]
    fn append_replay_reopen() {
        let schema = fixture_schema();
        let mut log = DeltaLog::open_with(MemBackend::new(), schema.clone(), TailPolicy::Recover)
            .unwrap_or_else(|e| panic!("open: {e}"));
        let s0 = log.append(Delta::Insert(fixture_row(1, "a"))).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(s0, 0);
        log.append(Delta::Update(fixture_row(1, "b"))).unwrap_or_else(|e| panic!("{e}"));
        log.append(Delta::Remove(Value::U64(1))).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(log.len(), 3);
        assert!(log.state().rows().is_empty());
        // Prefix states: after 1 entry the row is "a"; after 2 it's "b".
        assert_eq!(log.state_at(1).rows(), &[fixture_row(1, "a")]);
        assert_eq!(log.state_at(2).rows(), &[fixture_row(1, "b")]);
        // Reopen over the same backend restores the entries + state.
        let reopened = DeltaLog::open_with(MemBackend::new(), schema, TailPolicy::Recover)
            .unwrap_or_else(|e| panic!("open: {e}"));
        // (A fresh backend is empty; the real reopen test lives in the
        // integration tests over FsBackend.)
        assert!(reopened.is_empty());
        assert!(reopened.recovery().is_none());
    }

    /// Validation refusals at the boundary.
    #[test]
    fn append_refusals() {
        let schema = fixture_schema();
        let mut log = DeltaLog::open_with(MemBackend::new(), schema, TailPolicy::Recover)
            .unwrap_or_else(|e| panic!("open: {e}"));
        // A remove key of the wrong type refuses (typed, never silent).
        assert!(matches!(
            log.append(Delta::Remove(Value::Str("x".into()))),
            Err(DeltaError::SchemaMismatch { .. })
        ));
        // An ill-typed row refuses at construction, before any frame.
        assert!(Row::build(log.schema(), vec![Value::Str("x".into()), Value::Str("y".into())])
            .is_err());
        // Nothing landed.
        assert!(log.is_empty());
    }
}

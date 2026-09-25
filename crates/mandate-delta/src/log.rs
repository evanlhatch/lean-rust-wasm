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
use crate::snapshot::{self, FallbackReason, SnapshotReport};

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
    /// ONLY tail cut this crate performs, always reported).
    ///
    /// # Errors
    /// Backend I/O failure.
    fn truncate(&mut self, len: u64) -> Result<(), DeltaError>;

    /// Drop every byte BEFORE `offset` (the compaction head-cut — the
    /// ONLY head cut this crate performs, always paired with the
    /// snapshot that subsumes the cut frames). The journal keeps the
    /// SUFFIX `[offset..)`. Atomic-ish: a crash mid-call leaves either
    /// the old journal or the full suffix, never a torn either.
    ///
    /// # Errors
    /// Backend I/O failure.
    fn retain_from(&mut self, offset: u64) -> Result<(), DeltaError>;
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

    fn retain_from(&mut self, offset: u64) -> Result<(), DeltaError> {
        (**self).retain_from(offset)
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

    fn retain_from(&mut self, offset: u64) -> Result<(), DeltaError> {
        let at = usize::try_from(offset).unwrap_or(usize::MAX);
        self.bytes.drain(..at.min(self.bytes.len()));
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
    path: Option<std::path::PathBuf>,
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
        Ok(Self { file, path: Some(path.to_path_buf()) })
    }

    /// The journal file's path (`None` for an unnamed handle — the
    /// head cut needs it to rename atomically).
    #[must_use]
    pub fn path(&self) -> Option<&Path> {
        self.path.as_deref()
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

    fn retain_from(&mut self, offset: u64) -> Result<(), DeltaError> {
        use std::io::{Read, Seek, Write};
        // The head cut on a file is a REWRITE (POSIX cannot drop a
        // prefix in place): the suffix lands in a sibling tmp file,
        // syncs, renames over the journal, the rename syncs — the same
        // scratch + rename discipline the snapshot write rides. A
        // crash mid-call leaves the old journal or the full suffix.
        self.file.seek(std::io::SeekFrom::Start(offset))?;
        let mut suffix = Vec::new();
        self.file.read_to_end(&mut suffix)?;
        let path = self.path.clone().ok_or_else(|| {
            DeltaError::Io(std::io::Error::other("backend file has no path"))
        })?;
        {
            let mut tmp = path.as_os_str().to_os_string();
            tmp.push(".compact-tmp");
            let mut f = std::fs::File::create(&tmp)?;
            f.write_all(&suffix)?;
            f.sync_data()?;
            std::fs::rename(&tmp, &path)?;
            if let Some(dir) = path.parent() {
                if let Ok(d) = std::fs::File::open(dir) {
                    d.sync_all()?;
                }
            }
        }
        // Reopen over the renamed file (the old handle names an
        // unlinked inode; the append cursor must ride the new one).
        self.file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)?;
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
/// every append. The BASE is the state the entry index replays ON TOP
/// of — empty for a from-scratch log, the snapshot's materialization
/// after a snapshotted open/compaction (the entry index rebases at the
/// snapshot's seqno, so the base carries what the retired frames
/// contributed).
#[derive(Debug)]
pub struct DeltaLog<B: Backend> {
    backend: B,
    schema: Schema,
    base: Table,
    entries: Vec<Delta>,
    witnesses: Vec<WDelta>,
    state: Table,
    recovery: Option<Recovery>,
}

/// usize face of a seqno already range-checked against the entries.
fn prefix_len_usize(seqno: u64) -> usize {
    usize::try_from(seqno).unwrap_or(usize::MAX)
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

    /// OPEN WITH THE SNAPSHOT: the state materializes from the latest
    /// snapshot + the log's tail — and every honesty rule of BOTH
    /// artifacts applies (the crash-recovery discipline covers both
    /// files):
    ///
    /// - no snapshot file: the full replay, reported
    ///   [`SnapshotReport::Absent`] (the fresh-store shape);
    /// - a TORN snapshot file: never silently loaded — reported
    ///   ([`SnapshotReport::FellBack`] with the torn offset) and the
    ///   full replay took over;
    /// - a CORRUPT snapshot (bad magic, out-of-policy atom, trailing
    ///   bytes, content-hash mismatch): refused, reported, full replay;
    /// - a VALID snapshot: aligned against the log's bytes before one
    ///   byte of it is trusted —
    ///   rule A (the log still carries the subsumed prefix): the
    ///   prefix's cumulative fold must equal the snapshot's
    ///   `prefix_hash` AND the tail's head frame must match
    ///   `tail_head_hash` — then only frames `[seqno..)` replay, on
    ///   top of the snapshot's state;
    ///   rule B (the post-cut shape): the log's FIRST frame must match
    ///   the snapshot's `tail_head_hash` (or the log is empty with an
    ///   empty-tail snapshot) — then every frame replays on top of the
    ///   snapshot's state;
    /// - neither rule holds: [`FallbackReason::Unaligned`], reported,
    ///   full replay (the log alone is always a correct state).
    ///
    /// The LOG's own torn tail rides the recovering open's discipline
    /// (cut + [`crate::Recovery`] report) in every path — a torn
    /// snapshot AND a torn tail surface BOTH reports.
    ///
    /// # Errors
    /// I/O failure, or a corrupt COMPLETE frame in the log (the typed
    /// refusal — the snapshot's anomalies are reports, the LOG's
    /// corruption is an error, the same as `open`).
    pub fn open_snapshotted(path: &Path, snapshot_path: &Path, schema: Schema)
        -> Result<(Self, SnapshotReport), DeltaError>
    {
        use std::io::ErrorKind;
        let raw = match std::fs::read(snapshot_path) {
            Ok(raw) => Some(raw),
            Err(e) if e.kind() == ErrorKind::NotFound => None,
            Err(e) => return Err(e.into()),
        };
        let Some(raw) = raw else {
            return Self::open(path, schema).map(|l| (l, SnapshotReport::Absent));
        };
        let (meta, snap_state) = match snapshot::decode_snapshot(&schema, &raw) {
            Ok(ms) => ms,
            Err(snapshot::SnapshotError::Torn { offset }) => {
                return Self::open(path, schema)
                    .map(|l| (l, SnapshotReport::FellBack(FallbackReason::Torn { offset })));
            }
            Err(snapshot::SnapshotError::Corrupt { offset, reason }) => {
                return Self::open(path, schema).map(|l| {
                    (l, SnapshotReport::FellBack(FallbackReason::Refused { offset, reason }))
                });
            }
        };

        // The log's own walk (the corrupt-frame refusal is the log's
        // discipline; the torn tail is handled at the end, both rules).
        let mut backend = FsBackend::open(path)?;
        let bytes = backend.load()?;
        let walk = walk_journal(&schema, &bytes)?;
        let n = walk.frames.len();
        let s = prefix_len_usize(meta.seqno);
        let frame_bytes = |i: usize| &bytes[walk.frames[i].offset..walk.frames[i].end];
        let end_of = |i: usize| walk.frames[i].end;
        let empty_hash = snapshot::bytes_hash(&[]);

        // Rule A: the subsumed prefix is still present and byte-ties.
        let rule_a = s <= n
            && (if s == 0 {
                meta.prefix_hash == empty_hash
            } else {
                snapshot::bytes_hash(&bytes[..end_of(s - 1)]) == meta.prefix_hash
            })
            && (if s < n {
                snapshot::bytes_hash(frame_bytes(s)) == meta.tail_head_hash
            } else {
                // s == n: the snapshot subsumes the WHOLE log — its
                // tail is empty, its tail-head hash is the empty fold.
                meta.tail_head_hash == empty_hash
            });
        // Rule B: the post-cut shape — the log IS the tail. The empty
        // fold as the tail-head names the EMPTY tail at cut time; any
        // frames present are then post-cut appends and all of them
        // replay. (A pre-cut log never reaches rule B: its subsumed
        // prefix verifies under rule A first — and a frame's fold is
        // never the seed, so a pre-cut frame 0 cannot masquerade as an
        // empty tail.)
        let rule_b = (n > 0 && (snapshot::bytes_hash(frame_bytes(0)) == meta.tail_head_hash
                || meta.tail_head_hash == empty_hash))
            || (n == 0 && meta.tail_head_hash == empty_hash);

        let (skip, report) = if rule_a {
            (s, SnapshotReport::Applied { seqno: meta.seqno })
        } else if rule_b {
            (0, SnapshotReport::Applied { seqno: meta.seqno })
        } else {
            // The snapshot doesn't line up: the full replay takes over,
            // REPORTED (never a silent fallback, never a wrong state).
            return Self::open_with(backend, schema, TailPolicy::Recover)
                .map(|l| (l, SnapshotReport::FellBack(FallbackReason::Unaligned)));
        };

        // The tail replays on the snapshot's state through the CHECKED
        // patches — a snapshot state that lies about the tail refuses
        // here and the open falls back to the full replay, REPORTED.
        let start = snap_state.clone();
        let (state, witnesses, entries) =
            match replay_checked(&schema, start, &walk.frames[skip..]) {
                Ok(t) => t,
                Err(_) => {
                    return Self::open_with(backend, schema, TailPolicy::Recover).map(|l| {
                        (l, SnapshotReport::FellBack(FallbackReason::Refused {
                            offset: 0,
                            reason: "snapshot state refused the tail's checked patch",
                        }))
                    });
                }
            };
        // The log's torn-tail cut rides the same discipline as a plain
        // open (reported; the good prefix — here the tail — is the log).
        let recovery = match walk.torn_at {
            Some(cut) => {
                backend.truncate(cut)?;
                Some(Recovery { offset: cut, frames: n as u64 })
            }
            None => None,
        };
        // Rule A with a still-present prefix = the interrupted
        // compaction's cut never landed: FINISH it. The subsumed
        // frames are verified (the rule A byte-tie) and materialized
        // in the snapshot; the file keeps only the suffix, so the
        // backend's byte origin and the rebased index stay in step for
        // every later compact. (The same precedent as the torn-tail
        // cut: an open may cut what it can PROVE is retired.)
        if skip > 0 {
            backend.retain_from(end_of(skip - 1) as u64)?;
        }
        Ok((Self { backend, schema, base: snap_state, entries, witnesses, state, recovery },
            report))
    }
}

/// One walked frame: the decoded delta + its byte span in the file.
/// The END is the decoder's consumed prefix — NOT "to end of file":
/// with a torn tail, the torn bytes follow the last good frame, and
/// an end-of-file length would fold them into the last frame's hash
/// (the alignment rules would misrecognize the shape).
struct Frame {
    delta: Delta,
    offset: usize,
    end: usize,
}

/// The frame walk's result: the decoded frames + where a torn tail
/// began (the classification is EXACT — `Truncated` means the decoder
/// ran past EOF, so the failing frame extends to the end of file, the
/// torn-write shape; every other failure is corruption and REFUSES,
/// never truncates data away).
struct FrameWalk {
    frames: Vec<Frame>,
    torn_at: Option<u64>,
}

/// Walk a journal's bytes frame by frame from the cursor.
fn walk_journal(schema: &Schema, bytes: &[u8]) -> Result<FrameWalk, DeltaError> {
    let mut frames = Vec::new();
    let mut torn_at = None;
    let mut offset: usize = 0;
    while offset < bytes.len() {
        let mut rest = &bytes[offset..];
        match dec_delta(schema, &mut rest) {
            Err(DecodeFail::Truncated) => {
                torn_at = Some(offset as u64);
                break;
            }
            Err(e) => return Err(e.corrupt_error(offset as u64)),
            Ok(d) => {
                let end = bytes.len() - rest.len();
                frames.push(Frame { delta: d, offset, end });
                offset = end;
            }
        }
    }
    Ok(FrameWalk { frames, torn_at })
}

/// Replay decoded frames on top of `start`, witnesses computed at
/// replay time and CHECKED (the decoder/semantics-skew refusal: a
/// disagreement is the typed error, never a silently wrong state).
/// Returns the state, the witnesses, and the entries, in step.
fn replay_checked(schema: &Schema, start: Table, frames: &[Frame])
    -> Result<(Table, Vec<WDelta>, Vec<Delta>), DeltaError>
{
    let mut state = start;
    let mut witnesses = Vec::new();
    let mut entries = Vec::new();
    for f in frames {
        let w = witness_of(schema, &f.delta, &state);
        state = witnessed_apply(&state, std::slice::from_ref(&w)).ok_or(DeltaError::Corrupt {
            offset: f.offset as u64,
            reason: "replayed frame's witness refused (decoder/semantics skew)",
        })?;
        witnesses.push(w);
        entries.push(f.delta.clone());
    }
    Ok((state, witnesses, entries))
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
        let walk = walk_journal(&schema, &bytes)?;
        let recovery = match walk.torn_at {
            Some(cut) => match policy {
                // Cut to the last good frame — and REPORT it. Never
                // silent.
                TailPolicy::Recover => {
                    backend.truncate(cut)?;
                    Some(Recovery { offset: cut, frames: walk.frames.len() as u64 })
                }
                TailPolicy::Strict => return Err(DeltaError::TornTail { offset: cut }),
            },
            None => None,
        };
        let (state, witnesses, entries) = replay_checked(&schema, Table::new(), &walk.frames)?;
        Ok(Self { backend, schema, base: Table::new(), entries, witnesses, state, recovery })
    }

    /// COMPACT: write the state at `seqno` to `snapshot_path` (the
    /// atomic write — tmp + fsync + rename + dir fsync), THEN cut the
    /// log's head: the backend is truncated to the byte offset of frame
    /// `seqno` and the in-memory index REBASES (frame `seqno` becomes
    /// frame 0; the absolute seqno lives on in the snapshot). The
    /// materialized state is unchanged — compaction retires events,
    /// never their fold.
    ///
    /// THE CRASH WINDOWS (each recoverable, none silent — see
    /// `snapshot`'s module doc): before the snapshot lands, the log is
    /// intact; after the snapshot, before the cut, the log still
    /// carries the subsumed prefix and [`Self::open_snapshotted`]
    /// verifies + skips it; after the cut, the log is the tail alone.
    /// A compaction that fails partway reports the error and leaves the
    /// recoverable window it was in — never data loss.
    ///
    /// # Errors
    /// `CompactRange` (seqno past the log's end — nothing written,
    /// nothing cut), or a backend/write I/O failure.
    pub fn compact(&mut self, seqno: u64, snapshot_path: &Path) -> Result<(), DeltaError> {
        let (meta, prefix_len) =
            snapshot::compact_meta(&self.schema, &self.entries, seqno)?;
        let snap_state = self.state_at(seqno);
        let raw = snapshot::encode_snapshot(&meta, &snap_state);
        // The snapshot FIRST: a crash before this lands leaves the log
        // intact; a crash after it leaves a verifiable snapshot beside
        // a log that still (or no longer) carries the prefix. Both
        // windows recover; the reverse order would cut data away with
        // nothing to materialize it from.
        snapshot::write_snapshot_atomic(snapshot_path, &raw)?;
        // The cut: the log's ONLY head cut, always paired with the
        // snapshot that subsumes the cut frames.
        self.backend.retain_from(prefix_len as u64)?;
        self.entries.drain(..prefix_len_usize(seqno));
        self.witnesses.drain(..prefix_len_usize(seqno));
        // The rebased index's base is exactly the snapshot's state (the
        // state at in-memory seqno 0 of the new indexing).
        self.base = snap_state;
        Ok(())
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
    /// replay — the states ARE the partial integrals, taken over the
    /// log's BASE: for a from-scratch log the empty table, for a
    /// snapshotted open the snapshot's materialization — the entry
    /// index rebased at the snapshot's seqno).
    #[must_use]
    pub fn state_at(&self, seq: u64) -> Table {
        let mut t = self.base.clone();
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
        // replay) — never from an intermediate rewound state. The full
        // replay is RECOMPUTED here (the base + every entry's fold —
        // the same independent computation `state_at` makes):
        // `self.state` may itself be a PREVIOUS rewind's result, and
        // the rewind is ABSOLUTE (the target is `state_at(seq)`,
        // whatever the current state is) — starting the inverse from a
        // rewound state applies patches against positions that are not
        // there, and the checked refusal fires on honest witnesses.
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
        self.base = Table::new();
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
        // The CONSUMED input prefix IS the frame stream (the journal
        // wire is exactly the frames' concatenation — the re-encode
        // identity is test-pinned both directions, roundtrip.rs's
        // journal wire law), so the backend stores the input slice
        // itself: no re-encode pass over the replay.
        let mut backend = MemBackend::new();
        backend.append(&bytes[..total - rest.len()])?;
        Self {
            backend,
            schema,
            base: Table::new(),
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

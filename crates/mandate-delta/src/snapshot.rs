//! The state-at-seqno snapshot — the compaction face over the
//! append-only log (notes/v3/15-patterns.md #7: the snapshot IS THE
//! INTEGRAL — the log's frames are the events, the materialized state
//! is the fold; compaction writes the fold down and retires the events
//! it subsumes).
//!
//! WHY THIS FORMAT IS THE DELTA CRATE'S OWN: the Lean universe snapshot
//! (`SchemaCore.Snapshot`) is the REGISTRY's serialization — items,
//! fields, `tyText` — not the keyed table the journal folds into. No
//! Lean codec covers the app state, so this module builds the snapshot
//! as the AGGREGATE of the crate's own value codec (the documented
//! instantiation of the journal codec's `encR` parameter): the wire
//! invents no atom —
//!
//! ```text
//! snapshot := "MDL1"                      -- magic + format version
//!           ++ varint(seqno)              -- SchemaCore.Codec varint
//!           ++ varint(row count)
//!           ++ enc_row(row)*              -- the rows in TABLE order
//!           ++ le64(prefix_hash)          -- Kit.Emit.bytesHash's fold
//!           ++ le64(tail_head_hash)       --   over the named bytes
//!           ++ le64(content_hash)         -- over ALL preceding bytes
//! ```
//!
//! `enc_row`/`varint` are the same byte-exact codecs the frames ride
//! (the duel vectors pin them); the hashes are the tree's ONE hash
//! recurrence ([`bytes_hash`] — the LCG fold of `Kit.Emit.bytesHash`,
//! the twin `mandate_host::bytes_hash` pins from the consumer side).
//! The fixed-width LE tails keep the file self-delimiting: a torn
//! write (a crash mid-write leaves a PREFIX) is ALWAYS detectable as
//! truncation, never as a valid shorter snapshot.
//!
//! THE HONESTY METADATA: the snapshot carries its `seqno` (the number
//! of log frames it materializes) and binds itself to the log's BYTES —
//! `prefix_hash` folds frames `[0..seqno)` of the log file,
//! `tail_head_hash` folds frame `seqno`'s bytes (the seed for an empty
//! tail). A loader therefore never trusts a bare state blob: it checks
//! the snapshot against the log it claims to summarize (the alignment
//! rules on [`DeltaLog::open_snapshotted`]). Hashes establish IDENTITY,
//! not correctness (notes/v3/03 §5) — the threat is the torn write,
//! never the forger; adversarial tampering is the host fault lane's
//! row, not this codec's.
//!
//! CRASH WINDOWS (compaction = snapshot write, THEN the log's head
//! cut — the scratch + rename discipline, [`write_snapshot_atomic`]):
//!
//! - crash BEFORE the snapshot lands: no snapshot, log intact — the
//!   plain replay face;
//! - crash AFTER the snapshot, BEFORE the cut: the log still carries
//!   the subsumed prefix — alignment rule A verifies it byte-for-byte
//!   and skips exactly `seqno` frames;
//! - crash AFTER the cut: the log is the tail alone — alignment rule B
//!   recognizes the tail's head hash and replays everything on top of
//!   the snapshot state.
//!
//! Every window recovers; nothing is silent; the full replay (the log
//! alone) is always the fallback of last resort and it is always
//! CORRECT — the snapshot is an optimization over it, never a
//! dependency of it.

use std::fmt;
use std::path::{Path, PathBuf};

use crate::delta::{Table, enc_delta};
use crate::error::DeltaError;
use crate::schema::{Schema, dec_row, enc_row};
use crate::value::{dec_varint, enc_varint};

/// The snapshot magic: format + version (a v2 would change the tag —
/// reordering the layout is a WIRE-BREAKING change, the frames' rule).
pub const MAGIC: [u8; 4] = *b"MDL1";

/// The LCG seed (TestingKit.lcg's stream seed — `Kit.Emit.bytesHash`'s
/// fold base; the twin `mandate_host::bytes_hash` pins the same
/// constants from the host side).
const LCG_SEED: u64 = 1442695040888963407;
/// The LCG multiplier (Knuth 64 — the ONE recurrence; never a
/// hand-copied table).
const LCG_MULT: u64 = 6364136223846793005;
/// The LCG increment (same constant as the seed — Knuth 64's shape).
const LCG_INC: u64 = 1442695040888963407;

/// The binary content hash — the consumer-side twin of
/// `Kit.Emit.bytesHash`: the bytes folded through the LCG, one step
/// per byte (`h' = (h + b) * MULT + INC`, wrapping u64). The SAME
/// recurrence `mandate_host::bytes_hash` pins against the committed
/// sidecars — sharing the code was impossible (the atom's home is the
/// Lean emission; Rust consumes), so the twin is kept lockstep by the
/// known-answer pins below.
#[must_use]
pub fn bytes_hash(bs: &[u8]) -> u64 {
    bs.iter().fold(LCG_SEED, |h, &b| {
        (h.wrapping_add(b as u64))
            .wrapping_mul(LCG_MULT)
            .wrapping_add(LCG_INC)
    })
}

/// The snapshot's honesty metadata: what the loader verifies against
/// the log before trusting the state bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotMeta {
    /// The number of log frames the snapshot materializes (the log's
    /// ABSOLUTE frame count at compaction time — after a compaction the
    /// log's index rebases to 0 at this seqno).
    pub seqno: u64,
    /// `bytes_hash` over the log file's frames `[0..seqno)` — the
    /// prefix the snapshot subsumes, byte-tied.
    pub prefix_hash: u64,
    /// `bytes_hash` over frame `seqno`'s bytes (the tail's first
    /// frame), or [`bytes_hash`] of the empty slice when the tail is
    /// empty — the post-cut shape's recognizer.
    pub tail_head_hash: u64,
}

/// The snapshot file's decode failures. The CLASSIFICATION is the
/// crash-recovery discipline's: a torn write leaves a PREFIX (truncation
/// — [`SnapshotError::Torn`]); anything else is corruption
/// ([`SnapshotError::Corrupt`], which a torn write cannot produce).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SnapshotError {
    /// The input ran out — the torn-write shape (never a valid shorter
    /// snapshot: the fixed-width hash tails make truncation exact).
    Torn {
        /// Byte offset where the good prefix ends.
        offset: u64,
    },
    /// Complete bytes, invalid content (bad magic, out-of-policy atom,
    /// trailing bytes, content-hash mismatch). Never loaded.
    Corrupt {
        /// Byte offset of the offending region.
        offset: u64,
        /// What failed.
        reason: &'static str,
    },
}

impl fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Torn { offset } => {
                write!(f, "snapshot torn at {offset} (the torn-write shape)")
            }
            Self::Corrupt { offset, reason } => {
                write!(f, "snapshot at {offset}: corrupt ({reason})")
            }
        }
    }
}

impl std::error::Error for SnapshotError {}

/// Why a snapshot open fell back to the full replay. EVERY variant is a
/// report (never silent): the fallback is the honest recovery, the
/// caller sees exactly why it happened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FallbackReason {
    /// The snapshot file is a torn write — cut to the good prefix's
    /// end, the full replay took over.
    Torn {
        /// Byte offset where the snapshot's good prefix ends.
        offset: u64,
    },
    /// The snapshot's bytes are complete but refused (bad magic,
    /// out-of-policy atom, trailing bytes, content-hash mismatch).
    Refused {
        /// Byte offset of the offending region.
        offset: u64,
        /// What failed.
        reason: &'static str,
    },
    /// A valid snapshot that does not line up with this log's frames
    /// (neither the subsumed prefix nor the tail's head matches the
    /// log's bytes). The full replay took over.
    Unaligned,
}

/// The snapshot side of a snapshotted open's report. The LOG's own
/// torn-tail recovery rides [`crate::log::DeltaLog::recovery`]
/// separately — a load can carry BOTH reports (torn snapshot AND torn
/// log), and neither is ever swallowed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SnapshotReport {
    /// No snapshot file: the full replay (the fresh-store shape).
    Absent,
    /// The snapshot verified against the log's bytes; the state came
    /// from the snapshot + the tail's replay (only the tail's frames
    /// were folded). `seqno` is the snapshot's materialization point.
    Applied {
        /// The snapshot's seqno (see [`SnapshotMeta::seqno`]).
        seqno: u64,
    },
    /// The snapshot could not be trusted; the open fell back to the
    /// FULL replay — never a silent fallback, never a wrong state.
    FellBack(FallbackReason),
}

impl fmt::Display for SnapshotReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Absent => write!(f, "snapshot: none present (full replay)"),
            Self::Applied { seqno } => {
                write!(f, "snapshot applied at seqno {seqno} (tail replayed on top)")
            }
            Self::FellBack(reason) => match reason {
                FallbackReason::Torn { offset } => {
                    write!(f, "snapshot torn at {offset}: fell back to the full replay")
                }
                FallbackReason::Refused { offset, reason } => write!(
                    f,
                    "snapshot refused at {offset} ({reason}): fell back to the full replay"
                ),
                FallbackReason::Unaligned => write!(
                    f,
                    "snapshot does not line up with the log's frames: \
                     fell back to the full replay"
                ),
            },
        }
    }
}

/// The snapshot file's path for a log at `log_path`: the log's path
/// with `.snapshot` appended (`journal.bin` → `journal.bin.snapshot` —
/// ONE derivation, the host consumes it, never re-derives).
#[must_use]
pub fn snapshot_path_for(log_path: &Path) -> PathBuf {
    let mut s = log_path.as_os_str().to_os_string();
    s.push(".snapshot");
    PathBuf::from(s)
}

/// THE SNAPSHOT ENCODER: the layout the module doc pins, byte for
/// byte. Infallible — the rows are schema-checked at construction (a
/// `Table` cannot carry an ill-typed row), so no arm can fail.
#[must_use]
pub fn encode_snapshot(meta: &SnapshotMeta, state: &Table) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&MAGIC);
    enc_varint(meta.seqno, &mut out);
    enc_varint(state.rows().len() as u64, &mut out);
    for r in state.rows() {
        enc_row(r, &mut out);
    }
    out.extend_from_slice(&meta.prefix_hash.to_le_bytes());
    out.extend_from_slice(&meta.tail_head_hash.to_le_bytes());
    // The content hash rides LAST, over everything before it — the
    // file's own integrity tie (any flipped byte or truncated tail
    // refuses).
    let content = bytes_hash(&out);
    out.extend_from_slice(&content.to_le_bytes());
    out
}

/// Map the atom decoders' failure classes onto the snapshot's (the
/// torn/corrupt classification is the SAME dispatch the log's
/// recovery makes).
fn snap_fail(e: crate::error::DecodeFail, offset: u64) -> SnapshotError {
    match e {
        crate::error::DecodeFail::Truncated => SnapshotError::Torn { offset },
        crate::error::DecodeFail::Corrupt(reason) => SnapshotError::Corrupt { offset, reason },
    }
}

/// THE SNAPSHOT DECODER: full consumption — a whole-file artifact is
/// not a suffix stream, so trailing bytes refuse, and the fixed-width
/// hash tails make any truncation classify as [`SnapshotError::Torn`].
///
/// # Errors
/// [`SnapshotError::Torn`] for the torn-write shape,
/// [`SnapshotError::Corrupt`] for complete-but-invalid bytes.
pub fn decode_snapshot(schema: &Schema, bytes: &[u8]) -> Result<(SnapshotMeta, Table), SnapshotError>
{
    if bytes.len() < MAGIC.len() {
        return Err(SnapshotError::Torn { offset: 0 });
    }
    if bytes[..MAGIC.len()] != MAGIC {
        return Err(SnapshotError::Corrupt { offset: 0, reason: "snapshot magic" });
    }
    let mut rest = &bytes[MAGIC.len()..];
    let at = |rest: &[u8]| (bytes.len() - rest.len()) as u64;

    let seqno = dec_varint(&mut rest).map_err(|e| snap_fail(e, at(rest)))?;
    let count = dec_varint(&mut rest).map_err(|e| snap_fail(e, at(rest)))?;
    let mut state = Table::new();
    for _ in 0..count {
        // dec_row is schema-checked (arity + types): the snapshot's
        // rows ride the SAME decoder the frames' payloads ride.
        let row = dec_row(schema, &mut rest).map_err(|e| snap_fail(e, at(rest)))?;
        state.keyed_upsert(schema, row);
    }

    // The three fixed-width LE tails: prefix hash, tail-head hash,
    // content hash. Fewer than 24 bytes left = the torn-write shape
    // (a crash during the hash tails); more = corruption (a torn
    // write never ADDS bytes).
    let tails = 8 + 8 + 8;
    if rest.len() < tails {
        return Err(SnapshotError::Torn { offset: at(rest) });
    }
    if rest.len() > tails {
        return Err(SnapshotError::Corrupt {
            offset: at(rest) + tails as u64,
            reason: "trailing bytes",
        });
    }
    let le = |b: &[u8]| u64::from_le_bytes(b.try_into().expect("8 bytes"));
    let prefix_hash = le(&rest[0..8]);
    let tail_head_hash = le(&rest[8..16]);
    let content_hash = le(&rest[16..24]);

    let body_len = bytes.len() - 8;
    if bytes_hash(&bytes[..body_len]) != content_hash {
        return Err(SnapshotError::Corrupt {
            offset: body_len as u64,
            reason: "content hash mismatch",
        });
    }
    Ok((
        SnapshotMeta { seqno, prefix_hash, tail_head_hash },
        state,
    ))
}

/// THE ATOMIC WRITE (the scratch + rename discipline): the bytes land
/// in a sibling `.tmp` file, `sync_data` makes THEM durable, the rename
/// swaps the snapshot atomically (a reader sees the old file or the new
/// one, never a half-written either), and the parent directory's sync
/// makes the RENAME durable. A crash anywhere leaves the previous
/// snapshot intact or the new one complete — never a torn snapshot
/// under this path.
///
/// # Errors
/// `std::fs` failure (typed [`DeltaError::Io`]).
pub fn write_snapshot_atomic(path: &Path, raw: &[u8]) -> Result<(), DeltaError> {
    use std::io::Write;
    let mut tmp = path.as_os_str().to_os_string();
    tmp.push(".tmp");
    let tmp = PathBuf::from(tmp);
    {
        let mut f = std::fs::File::create(&tmp)?;
        f.write_all(raw)?;
        f.sync_data()?;
    }
    std::fs::rename(&tmp, path)?;
    // The rename's durability: sync the directory entry too (the file's
    // own sync does not cover the parent's metadata).
    if let Some(dir) = path.parent() {
        match std::fs::File::open(dir) {
            Ok(d) => d.sync_all()?,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }
    }
    Ok(())
}

/// The compaction's snapshot computation for a log's frames
/// `[0..seqno)`: the prefix bytes (exactly the log file's first
/// `prefix_len` bytes — the journal wire IS the frames' concatenation,
/// the round-trip law's identity), the tail-head hash, and the seqno.
pub fn compact_meta(schema: &Schema, frames: &[crate::Delta], seqno: u64)
    -> Result<(SnapshotMeta, usize), DeltaError>
{
    let s = usize::try_from(seqno).map_err(|_| DeltaError::CompactRange {
        seqno,
        len: frames.len() as u64,
    })?;
    if s > frames.len() {
        return Err(DeltaError::CompactRange { seqno, len: frames.len() as u64 });
    }
    // The log FILE is the frames' CONCATENATION (self-delimiting
    // frames, no header — the open's walk starts at byte 0), so the
    // prefix bytes are the frames emitted one by one — NOT
    // `enc_journal`, whose count varint would be a byte the file never
    // carries.
    let mut prefix = Vec::new();
    for d in &frames[..s] {
        if !enc_delta(schema, d, &mut prefix) {
            return Err(DeltaError::SchemaMismatch {
                reason: "delta failed to encode (compaction prefix walk)",
            });
        }
    }
    let tail_head_hash = match frames.get(s) {
        Some(d) => {
            let mut frame = Vec::new();
            if !enc_delta(schema, d, &mut frame) {
                return Err(DeltaError::SchemaMismatch {
                    reason: "delta failed to encode (compaction prefix walk)",
                });
            }
            bytes_hash(&frame)
        }
        // The empty tail's head is the empty bytes' fold (the seed).
        None => bytes_hash(&[]),
    };
    Ok((SnapshotMeta { seqno, prefix_hash: bytes_hash(&prefix), tail_head_hash }, prefix.len()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::delta::{Delta, enc_journal, witnessed_apply, witness_of};
    use crate::schema::fixtures::{fixture, fixture_row};
    use crate::value::Value;

    /// `bytes_hash`'s known answers — the SAME pins the host side's
    /// twin carries (one recurrence, two consumers, both pinned).
    #[test]
    fn bytes_hash_known_answers() {
        fn lcg(h: u64) -> u64 {
            h.wrapping_add(0).wrapping_mul(LCG_MULT).wrapping_add(LCG_INC)
        }
        assert_eq!(bytes_hash(&[]), LCG_SEED);
        assert_eq!(bytes_hash(&[0]), lcg(LCG_SEED));
        assert_eq!(bytes_hash(&[0, 0]), lcg(lcg(LCG_SEED)));
    }

    /// The snapshot wire's known answer: magic + varints + rows, every
    /// atom a Lean-pinned emission (u64 300 = [0xAC, 0x02]; "hi" =
    /// [2, 104, 105] — Codec.lean's pins), the hash tails LE.
    #[test]
    fn snapshot_known_answer() {
        let schema = fixture();
        let mut state = Table::new();
        state.apply(&schema, &Delta::Insert(fixture_row(300, "hi")));
        let meta = SnapshotMeta { seqno: 5, prefix_hash: 0x0102030405060708, tail_head_hash: 99 };
        let raw = encode_snapshot(&meta, &state);
        assert_eq!(
            raw,
            [
                b'M', b'D', b'L', b'1', //
                5, // seqno varint
                1, // row count varint
                2, 0xAC, 0x02, 2, 104, 105, // enc_row
                0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, // prefix hash LE
                99, 0, 0, 0, 0, 0, 0, 0, // tail-head hash LE
            ]
            .iter()
            .copied()
            .chain(bytes_hash(&raw[..raw.len() - 8]).to_le_bytes())
            .collect::<Vec<u8>>()
        );
        // And the decoder takes it back exactly.
        let (meta2, state2) =
            decode_snapshot(&schema, &raw).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(meta2, meta);
        assert_eq!(state2, state);
    }

    /// The torn/corrupt classification at the byte level: every
    /// truncation is Torn (never a valid shorter snapshot); a flipped
    /// byte, trailing bytes, and bad magic are Corrupt.
    #[test]
    fn snapshot_torn_vs_corrupt() {
        let schema = fixture();
        let mut state = Table::new();
        state.apply(&schema, &Delta::Insert(fixture_row(300, "hi")));
        let meta = SnapshotMeta { seqno: 1, prefix_hash: 7, tail_head_hash: 9 };
        let raw = encode_snapshot(&meta, &state);

        // Every prefix is Torn — the torn write's shape.
        for cut in 0..raw.len() {
            match decode_snapshot(&schema, &raw[..cut]) {
                Err(SnapshotError::Torn { .. }) => {}
                other => panic!("cut {cut}: expected Torn, got {other:?}"),
            }
        }
        // A flipped state byte (complete file) = the content hash
        // refuses it — corruption, never loaded.
        let mut bad = raw.clone();
        let mid = raw.len() / 2;
        bad[mid] ^= 0x01;
        match decode_snapshot(&schema, &bad) {
            Err(SnapshotError::Corrupt { reason: "content hash mismatch", .. }) => {}
            other => panic!("flipped byte: expected hash refusal, got {other:?}"),
        }
        // Bad magic (complete file) refuses.
        let mut bad = raw.clone();
        bad[0] = b'X';
        match decode_snapshot(&schema, &bad) {
            Err(SnapshotError::Corrupt { offset: 0, reason: "snapshot magic" }) => {}
            other => panic!("bad magic: expected refusal, got {other:?}"),
        }
        // Trailing bytes refuse (a whole-file artifact is not a suffix
        // stream).
        let mut bad = raw.clone();
        bad.push(0);
        match decode_snapshot(&schema, &bad) {
            Err(SnapshotError::Corrupt { reason: "trailing bytes", .. }) => {}
            other => panic!("trailing: expected refusal, got {other:?}"),
        }
        // NON-CONTROL: the honest bytes decode (the negative controls
        // above never pass on a valid file).
        assert!(decode_snapshot(&schema, &raw).is_ok());
    }

    /// The metadata's computation: the prefix hash folds exactly the
    /// log-file bytes the snapshot subsumes; the tail-head hash folds
    /// frame `seqno`'s bytes (the seed for an empty tail).
    #[test]
    fn compact_meta_binds_the_log_bytes() {
        let schema = fixture();
        let frames = vec![
            Delta::Insert(fixture_row(1, "a")),
            Delta::Update(fixture_row(1, "b")),
            Delta::Remove(Value::U64(1)),
        ];
        let mut file = Vec::new();
        enc_journal(&schema, &frames, &mut file);

        let (meta, prefix_len) =
            compact_meta(&schema, &frames, 2).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(meta.seqno, 2);
        // Journal count varint (1) + insert frame (5) + update frame (5)
        // — the FILE carries no count byte, the prefix must not either.
        assert_eq!(prefix_len, 10, "frames 0..2 only (no journal count byte)");
        // The log FILE is `file[1..]` (enc_journal's count byte is not
        // on the disk); the tail-head hash folds the log file's last
        // frame.
        let log_file = &file[1..];
        assert_eq!(meta.tail_head_hash, bytes_hash(&log_file[prefix_len..]));

        // The empty tail's head hash is the seed (the empty fold).
        let (meta0, len0) = compact_meta(&schema, &frames, 3).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(len0, log_file.len());
        assert_eq!(meta0.tail_head_hash, bytes_hash(&[]));
        assert_eq!(meta0.prefix_hash, bytes_hash(log_file));

        // Past the end refuses (typed, nothing invented).
        assert!(matches!(
            compact_meta(&schema, &frames, 4),
            Err(DeltaError::CompactRange { seqno: 4, len: 3 })
        ));
    }

    /// The snapshot state's decode is a LIVE state: the tail's frames
    /// replay on top through the CHECKED patches (the loader's rule A
    /// face, exercised at the codec level).
    #[test]
    fn snapshot_state_accepts_the_tail() {
        let schema = fixture();
        let mut state = Table::new();
        state.apply(&schema, &Delta::Insert(fixture_row(1, "a")));
        let meta = SnapshotMeta { seqno: 1, prefix_hash: 7, tail_head_hash: 9 };
        let raw = encode_snapshot(&meta, &state);
        let (_, decoded) = decode_snapshot(&schema, &raw).unwrap_or_else(|e| panic!("{e}"));
        // The tail: update then remove — the checked patches accept.
        let tail = vec![Delta::Update(fixture_row(1, "b")), Delta::Remove(Value::U64(1))];
        let mut ws = Vec::new();
        let mut st = decoded;
        for d in &tail {
            let w = witness_of(&schema, d, &st);
            st = witnessed_apply(&st, std::slice::from_ref(&w))
                .unwrap_or_else(|| panic!("checked patch refused"));
            ws.push(w);
        }
        assert!(st.rows().is_empty());
        assert_eq!(ws.len(), 2);
    }
}

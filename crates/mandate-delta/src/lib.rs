//! mandate-delta — the host's persistence lane: the append-only delta
//! log over SchemaCore's delta/journal model.
//!
//! OWNERSHIP (notes/v3/13-interfaces.md, the delta-log row): Lean owns
//! meaning; the wire format is the LEAN side's codec, ported byte-exact.
//! This crate invents no format — every byte this crate writes is a byte
//! SchemaCore emits:
//!
//! - the delta frame is `SchemaCore.Event.encDelta`/`decDelta?`: ONE tag
//!   byte in CTOR ORDER (0 = insert, 1 = update, 2 = remove — the
//!   EnumWire rule: reordering the ctors is a WIRE-BREAKING change)
//!   followed by the self-delimiting payload (`enc_row` for
//!   insert/update, `enc_key` for remove). Frames are APPEND-FORM
//!   (decoding yields the delta AND the unconsumed suffix), which is
//!   what makes the on-disk log a decodable frame stream;
//! - the atoms are `SchemaCore.Codec`'s: bool = one byte (0/1, any
//!   other byte refuses); u64 = the canonical-minimal LEB128 varint;
//!   i64 = the varint of the zigzag; string = varint length + one
//!   varint code point per char (NOT UTF-8 — the char-varint wire is
//!   the Lean-provable atom); every out-of-policy byte refuses, never a
//!   silent misparse;
//! - the row/key encodings are the documented instantiation of the Lean
//!   journal codec's `encR`/`encK` PARAMETERS (`SchemaCore.Event` leaves
//!   them polymorphic): a row is `SchemaCore.encList`'s shape — varint
//!   field count + one `encVal` per field in schema order; a key is
//!   `SchemaCore.Codec.encKey` verbatim. The full spec lives in
//!   README.md; the duel vectors (tests/duel/) are the journal duel
//!   emitter `SchemaCore.Emit.Journal`'s artifacts — this exact
//!   instantiation, byte-tied;
//! - the whole-log wire is `SchemaCore.Event.encJournal`/`decJournal?`:
//!   varint count + the frames in occurrence order ([`log::DeltaLog::
//!   journal_bytes`] / [`log::DeltaLog::from_journal_bytes`]).
//!
//! THE INVERSION is the Lean witnessed delta (`SchemaCore.Delta`'s
//! `WDelta`/`witnessOf`/`invertW`/`patchW?`), not a second scheme: each
//! entry's witness (position + OLD row + NEW row) is computed against
//! the materialized state at append/replay time, the inverse journal is
//! `reverse ∘ invertW`, and every patch is CHECKED — a lying witness
//! refuses (`patchW?`'s discipline: the delta does not lie; the round
//! trip `witnessedApply_reverse_inv` holds unconditionally). The
//! witnesses are IN-MEMORY data (Lean names no witness wire bytes —
//! `SchemaCore.Delta`'s declared exclusion), so the on-disk format stays
//! exactly the Lean journal codec's.
//!
//! CRASH RECOVERY (the honest handling of a torn/corrupt tail): the log
//! is a frame stream; `open` walks it frame by frame. A TRUNCATED tail
//! (the decode ran out of input — the only shape a torn write can
//! produce at the tail) recovers to the last good frame: the backend is
//! truncated to the good prefix AND the recovery is REPORTED (the
//! [`log::DeltaLog::recovery`] field) — never a silent truncation.
//! `open_strict` refuses the same tail with the typed error instead. A
//! COMPLETE frame that fails to decode (unknown tag, invalid payload —
//! mid-log corruption, which a torn write cannot produce) is a typed
//! ERROR in every mode: the log refuses, it never truncates data away.
//!
//! SNAPSHOT / COMPACT (the long-lived app's face — the log is
//! append-only, so an app that never compacts replays forever): the
//! state-at-seqno SNAPSHOT ([`snapshot`]) materializes the fold and
//! retires the frames that produced it. The snapshot carries its
//! seqno + a content hash + its alignment hashes against the log's
//! bytes; [`log::DeltaLog::compact`] writes it atomically (tmp +
//! fsync + rename + dir fsync) THEN cuts the log's head;
//! [`log::DeltaLog::open_snapshotted`] loads snapshot + tail, with
//! every anomaly — torn snapshot, corrupt snapshot, snapshot/log
//! misalignment, torn log tail — reported and fallen back from the
//! full replay, never silently wrong. The Lean universe snapshot
//! (`SchemaCore.Snapshot`) serializes the REGISTRY, not the keyed
//! table, so the snapshot's aggregate rides this crate's own value
//! codec (the same Lean-tied atoms the frames ride — no new atom,
//! no new semantics).
//!
//! ERROR DISCIPLINE: typed errors end to end ([`error::DeltaError`]),
//! no panics on error paths, `#![forbid(unsafe_code)]`. ONE dependency:
//! the atom codec's single home is the generated crate
//! (`schema-generated` — byte-tied to `SchemaCore.Codec` by the gates
//! + the duel vectors); this crate consumes it, never mirrors it.

#![forbid(unsafe_code)]
#![deny(missing_docs)]

pub mod delta;
pub mod error;
pub mod log;
pub mod manifest;
pub mod schema;
pub mod scratch;
pub mod snapshot;
pub mod value;

pub use delta::{Delta, WDelta};
pub use error::{DecodeFail, DeltaError, Recovery};
pub use log::{Backend, DeltaLog, FsBackend, MemBackend};
pub use manifest::{DuelManifest, DuelRow, ManifestError, parse_duel_manifest};
pub use schema::{Field, Row, Schema};
pub use scratch::ScratchDir;
pub use snapshot::{FallbackReason, SnapshotError, SnapshotMeta, SnapshotReport,
    snapshot_path_for};
pub use value::{Ty, Value};

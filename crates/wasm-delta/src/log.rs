//! The append-only delta log — the event-sourcing rule as a host
//! artifact: DELTAS AT THE BOUNDARY, INVERSION IN THE LOG. Every
//! appended entry carries its inverse (computed against the
//! materialized state at append time — `delta::invert`, the
//! `Dbsp.ChangeSpec.ChangeInversion` law); `rewind_to` replays the
//! stored inverses tail-first as COMPENSATION APPENDS (the log itself
//! is never rewritten — append-only is literal).
//!
//! The journal record format is assembled ONLY from the Lean codec's
//! combinators (no new format invention):
//!
//! ```text
//! record  := encEnvelope(VERSION, fingerprint, payload)      -- Codec.lean
//! payload := encString table ++ encChange change ++ encChange inverse
//! encChange := encEnum tag ++ (encRowVals row | encodeValue key)
//!            -- tags: insert = 0, update = 1, remove = 2 (Delta.lean
//!            -- declaration order)
//! encString := the string codec (varint char count + codepoint varints)
//! ```
//!
//! The envelope's truncation rejection (the `decBytes?` overrun check,
//! proved Lean-side) is the crash-recovery mechanism: a partial write
//! leaves a record whose payload length overruns the file, the recovery
//! scan stops there, and the backend truncates to the last complete
//! record — the consistent tail.

use std::collections::BTreeMap;
use std::fmt;
use std::path::Path;

use crate::codec::{self, DecFail};
use crate::delta::{self, Change, Table};
use crate::row::{Schema, dec_row, enc_row};
use crate::value::{Ty, Value, dec_value, enc_value};

/// The journal format version (the envelope's first field).
pub const VERSION: u64 = 1;

/// Every error the log surfaces. Data, not strings (the cedar
/// discipline): rendering is `Display`'s job.
#[derive(Debug)]
pub enum DeltaError {
    /// The durable backend failed.
    Io(std::io::Error),
    /// A delta named a table the schema set doesn't know.
    UnknownTable(String),
    /// A delta's payload doesn't match its table's schema (arity,
    /// field types, key type, or a key-less schema).
    SchemaMismatch {
        /// The table the delta targeted.
        table: String,
        /// What mismatched.
        reason: &'static str,
    },
    /// A journal record's envelope version isn't `VERSION` (complete
    /// envelope, wrong version — a format change, NOT a torn tail; the
    /// log refuses rather than truncate data away).
    WrongVersion {
        /// Byte offset of the offending record.
        offset: u64,
        /// The version found.
        found: u64,
    },
    /// A journal record's envelope fingerprint isn't the schema set's.
    FingerprintMismatch {
        /// Byte offset of the offending record.
        offset: u64,
    },
    /// A complete envelope whose payload doesn't decode as an entry
    /// (mid-log corruption; a torn write cannot produce this — see the
    /// module docs' prefix argument).
    Corrupt {
        /// Byte offset of the offending record.
        offset: u64,
        /// What failed.
        reason: &'static str,
    },
}

impl fmt::Display for DeltaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => write!(f, "io: {e}"),
            Self::UnknownTable(t) => write!(f, "unknown table {t:?}"),
            Self::SchemaMismatch { table, reason } => {
                write!(f, "schema mismatch on {table:?}: {reason}")
            }
            Self::WrongVersion { offset, found } => {
                write!(f, "journal record at {offset}: version {found}, expected {VERSION}")
            }
            Self::FingerprintMismatch { offset } => {
                write!(f, "journal record at {offset}: schema fingerprint mismatch")
            }
            Self::Corrupt { offset, reason } => {
                write!(f, "journal record at {offset}: corrupt ({reason})")
            }
        }
    }
}

impl std::error::Error for DeltaError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for DeltaError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

/// The named schema set: table name → schema. The decoder argument
/// (schema-out-of-band) and the envelope fingerprint's basis.
#[derive(Clone, Debug, Default)]
pub struct SchemaSet {
    tables: BTreeMap<String, Schema>,
}

impl SchemaSet {
    /// An empty set.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a table schema (name ↔ schema must be 1:1 with the
    /// guest's registry; re-registration replaces).
    pub fn register(&mut self, table: &str, schema: Schema) {
        self.tables.insert(table.to_owned(), schema);
    }

    /// Look up a table's schema.
    #[must_use]
    pub fn get(&self, table: &str) -> Option<&Schema> {
        self.tables.get(table)
    }

    /// The schema-set fingerprint (the envelope's second field): FNV-1a
    /// over the canonical encoding of (table, field, type) triples.
    /// Host-side identity only — it pins "this journal was written
    /// against this schema set", nothing more.
    #[must_use]
    pub fn fingerprint(&self) -> u64 {
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        let mut mix = |bytes: &[u8]| {
            for &b in bytes {
                h ^= u64::from(b);
                h = h.wrapping_mul(0x0000_0100_0000_01b3);
            }
        };
        for (name, schema) in &self.tables {
            mix(name.as_bytes());
            for f in schema.fields() {
                mix(f.name.as_bytes());
                let mut tyb = Vec::new();
                enc_ty_tag(&f.ty, &mut tyb);
                mix(&tyb);
            }
        }
        h
    }
}

/// Structural type tags for the fingerprint (NOT a wire encoding — the
/// fingerprint is host-local identity data).
fn enc_ty_tag(ty: &Ty, out: &mut Vec<u8>) {
    match ty {
        Ty::Bool => out.push(1),
        Ty::U8 => out.push(2),
        Ty::U16 => out.push(3),
        Ty::U32 => out.push(4),
        Ty::U64 => out.push(5),
        Ty::I8 => out.push(6),
        Ty::I16 => out.push(7),
        Ty::I32 => out.push(8),
        Ty::I64 => out.push(9),
        Ty::Str => out.push(10),
        Ty::Bytes => out.push(11),
        Ty::Opt(t) => {
            out.push(12);
            enc_ty_tag(t, out);
        }
        Ty::Res(ok, err) => {
            out.push(13);
            enc_ty_tag(ok, out);
            enc_ty_tag(err, out);
        }
        Ty::List(t) => {
            out.push(14);
            enc_ty_tag(t, out);
        }
    }
}

/// One logged delta with its inverse (`DeltaEntry`). The inverse is
/// the event-sourcing rule made literal: INVERSION IN THE LOG.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeltaEntry {
    /// The table the change targets.
    pub table: String,
    /// The change that was appended.
    pub change: Change,
    /// Its inverse, computed against the state at append time.
    pub inverse: Change,
}

/// The string codec (`CodecValue`'s `Ty.string` arm) for the table name.
fn enc_string(s: &str, out: &mut Vec<u8>) {
    enc_value(&Ty::Str, &Value::Str(s.to_owned()), out);
}

fn dec_string(bs: &[u8]) -> codec::Dec<String> {
    let (v, u) = dec_value(&Ty::Str, bs)?;
    match v {
        Value::Str(s) => Ok((s, u)),
        _ => Err(DecFail::Corrupt),
    }
}

/// `encChange`: tag varint (Delta.lean declaration order) + payload.
fn enc_change(schema: &Schema, change: &Change, out: &mut Vec<u8>) -> bool {
    codec::enc_varnat(change.tag(), out);
    match change {
        Change::Insert(r) | Change::Update(r) => enc_row(schema, r, out),
        Change::Remove(k) => {
            // Reaching here with an ill-typed key is a caller bug; the
            // log validates before encoding, so the bool is defensive.
            return crate::row::enc_key(schema, k, out);
        }
    }
    true
}

fn dec_change(schema: &Schema, bs: &[u8]) -> codec::Dec<Change> {
    let (tag, u) = codec::dec_varnat(bs)?;
    match tag {
        0 | 1 => {
            let (row, used) = dec_row(schema, &bs[u..])?;
            let change = if tag == 0 { Change::Insert(row) } else { Change::Update(row) };
            Ok((change, u + used))
        }
        2 => {
            let key_field = schema.key().ok_or(DecFail::Corrupt)?;
            let (key, used) = dec_value(&key_field.ty, &bs[u..])?;
            Ok((Change::Remove(key), u + used))
        }
        _ => Err(DecFail::Corrupt),
    }
}

/// The entry payload (the envelope's payload): table, change, inverse.
fn enc_entry_payload(schemas: &SchemaSet, entry: &DeltaEntry, out: &mut Vec<u8>) -> bool {
    let Some(schema) = schemas.get(&entry.table) else { return false };
    enc_string(&entry.table, out);
    enc_change(schema, &entry.change, out) && enc_change(schema, &entry.inverse, out)
}

/// Decode one entry payload; the payload must be FULLY consumed
/// (trailing garbage inside an envelope is corruption).
fn dec_entry_payload(schemas: &SchemaSet, payload: &[u8]) -> Option<DeltaEntry> {
    let (table, u1) = dec_string(payload).ok()?;
    let schema = schemas.get(&table)?;
    let (change, u2) = dec_change(schema, &payload[u1..]).ok()?;
    let (inverse, u3) = dec_change(schema, &payload[u1 + u2..]).ok()?;
    if u1 + u2 + u3 != payload.len() {
        return None;
    }
    Some(DeltaEntry { table, change, inverse })
}

/// The durable-or-not byte sink behind a log. One writer per log (the
/// one-writer rule); the trait is the sled/redb seam.
pub trait Backend {
    /// The full journal bytes.
    ///
    /// # Errors
    /// Backend I/O failure.
    fn load(&mut self) -> Result<Vec<u8>, DeltaError>;

    /// Append one complete record. Implementations that claim
    /// durability must sync before returning.
    ///
    /// # Errors
    /// Backend I/O failure.
    fn append(&mut self, record: &[u8]) -> Result<(), DeltaError>;

    /// Truncate the journal to a prefix (recovery from a torn tail).
    ///
    /// # Errors
    /// Backend I/O failure.
    fn truncate(&mut self, len: u64) -> Result<(), DeltaError>;
}

/// The in-memory backend (tests, ephemeral hosts, the trait's
/// reference implementation).
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

    fn append(&mut self, record: &[u8]) -> Result<(), DeltaError> {
        self.bytes.extend_from_slice(record);
        Ok(())
    }

    fn truncate(&mut self, len: u64) -> Result<(), DeltaError> {
        self.bytes
            .truncate(usize::try_from(len).unwrap_or(usize::MAX));
        Ok(())
    }
}

/// The durable backend: an append-only file over `std::fs`, one record
/// per `append`, `sync_data` before the append returns (an append that
/// returns is on stable storage; a crash mid-append leaves a torn tail
/// the next `open` truncates).
///
/// The named follow-up: an embedded-KV backend (sled or redb) behind
/// the same `Backend` trait — neither is in the workspace's offline
/// dependency tree today, so v1 is this file backend.
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
        use std::io::Read;
        use std::io::Seek;
        self.file.seek(std::io::SeekFrom::Start(0))?;
        let mut bytes = Vec::new();
        self.file.read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    fn append(&mut self, record: &[u8]) -> Result<(), DeltaError> {
        use std::io::Write;
        self.file.write_all(record)?;
        self.file.sync_data()?;
        Ok(())
    }

    fn truncate(&mut self, len: u64) -> Result<(), DeltaError> {
        self.file.set_len(len)?;
        self.file.sync_data()?;
        Ok(())
    }
}

/// The append-only delta log over a backend: decoded entry index +
/// materialized per-table state, kept in step on every append.
#[derive(Debug)]
pub struct DeltaLog<B: Backend> {
    backend: B,
    schemas: SchemaSet,
    entries: Vec<DeltaEntry>,
    states: BTreeMap<String, Table>,
}

impl DeltaLog<FsBackend> {
    /// Open a file-backed log, recovering from a torn tail (the
    /// crash-recovery rule: the file is truncated to the last complete
    /// record; a complete-but-invalid record is an error, never silent
    /// truncation).
    ///
    /// # Errors
    /// I/O failure, wrong version, fingerprint mismatch, mid-log
    /// corruption.
    pub fn open(path: &Path, schemas: SchemaSet) -> Result<Self, DeltaError> {
        Self::open_with(FsBackend::open(path)?, schemas)
    }
}

impl<B: Backend> DeltaLog<B> {
    /// Open a log over any backend (the MemBackend lane + the future
    /// sled/redb lane).
    ///
    /// # Errors
    /// See `DeltaLog::open`.
    pub fn open_with(mut backend: B, schemas: SchemaSet) -> Result<Self, DeltaError> {
        let bytes = backend.load()?;
        let fingerprint = schemas.fingerprint();
        let mut entries = Vec::new();
        let mut offset: usize = 0;
        while offset < bytes.len() {
            let rec = &bytes[offset..];
            match codec::dec_envelope_prefix(rec) {
                Err(DecFail::Torn) => {
                    // Crash recovery: partial write at the tail. Cut it.
                    #[allow(clippy::cast_possible_truncation, reason = "journal offsets fit u64 on 64-bit hosts")]
                    backend.truncate(offset as u64)?;
                    break;
                }
                Err(DecFail::Corrupt) => {
                    return Err(DeltaError::Corrupt {
                        offset: offset as u64,
                        reason: "malformed envelope header",
                    });
                }
                Ok(env) => {
                    if env.version != VERSION {
                        return Err(DeltaError::WrongVersion {
                            offset: offset as u64,
                            found: env.version,
                        });
                    }
                    if env.fingerprint != fingerprint {
                        return Err(DeltaError::FingerprintMismatch {
                            offset: offset as u64,
                        });
                    }
                    let entry = dec_entry_payload(&schemas, env.payload).ok_or(
                        DeltaError::Corrupt {
                            offset: offset as u64,
                            reason: "entry payload undecodable",
                        },
                    )?;
                    entries.push(entry);
                    offset += env.len;
                }
            }
        }
        let mut log = Self {
            backend,
            schemas,
            entries,
            states: BTreeMap::new(),
        };
        log.rebuild_states();
        Ok(log)
    }

    /// Append a delta: validate against the table's schema, compute the
    /// inverse against the CURRENT materialized state (inversion in the
    /// log), write the record, patch the state. Returns the entry's
    /// sequence number.
    ///
    /// # Errors
    /// `UnknownTable`, `SchemaMismatch`, or backend I/O failure.
    pub fn append(&mut self, table: &str, change: Change) -> Result<u64, DeltaError> {
        let schema = self
            .schemas
            .get(table)
            .ok_or_else(|| DeltaError::UnknownTable(table.to_owned()))?;
        self.validate(table, schema, &change)?;
        let key = change
            .key_bytes(schema)
            .ok_or(DeltaError::SchemaMismatch { table: table.to_owned(), reason: "no key" })?;
        let pre = self
            .states
            .get(table)
            .and_then(|t| t.get(&key))
            .cloned();
        let inverse = delta::invert(schema, &change, pre.as_ref()).ok_or(
            DeltaError::SchemaMismatch { table: table.to_owned(), reason: "not invertible" },
        )?;
        let entry = DeltaEntry {
            table: table.to_owned(),
            change,
            inverse,
        };
        let mut payload = Vec::new();
        if !enc_entry_payload(&self.schemas, &entry, &mut payload) {
            return Err(DeltaError::SchemaMismatch {
                table: table.to_owned(),
                reason: "entry failed to encode",
            });
        }
        let mut record = Vec::new();
        codec::enc_envelope(VERSION, self.schemas.fingerprint(), &payload, &mut record);
        self.backend.append(&record)?;
        let seq = self.entries.len() as u64;
        self.states
            .entry(table.to_owned())
            .or_insert_with(Table::new)
            .patch(schema, &entry.change);
        self.entries.push(entry);
        Ok(seq)
    }

    /// Validate a change against a schema (the `RowVals` discipline at
    /// the boundary).
    fn validate(&self, table: &str, schema: &Schema, change: &Change) -> Result<(), DeltaError> {
        let mismatch = |reason: &'static str| DeltaError::SchemaMismatch {
            table: table.to_owned(),
            reason,
        };
        match change {
            Change::Insert(r) | Change::Update(r) => {
                if schema.key().is_none() {
                    return Err(mismatch("key-less schema has no change type (Delta.lean)"));
                }
                if !schema.check(r.values()) {
                    return Err(mismatch("row arity/type mismatch"));
                }
                Ok(())
            }
            Change::Remove(k) => match schema.key() {
                None => Err(mismatch("key-less schema has no change type (Delta.lean)")),
                Some(f) if crate::value::value_ty_matches(&f.ty, k) => Ok(()),
                Some(_) => Err(mismatch("remove key type mismatch")),
            },
        }
    }

    /// Rebuild the materialized states from the entry index (open).
    fn rebuild_states(&mut self) {
        self.states.clear();
        for e in &self.entries {
            if let Some(schema) = self.schemas.get(&e.table) {
                self.states
                    .entry(e.table.clone())
                    .or_insert_with(Table::new)
                    .patch(schema, &e.change);
            }
        }
    }

    /// The backend (journal-byte access for replication/inspection).
    #[must_use]
    pub fn backend(&self) -> &B {
        &self.backend
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

    /// The entry at a sequence number.
    #[must_use]
    pub fn entry(&self, seq: u64) -> Option<&DeltaEntry> {
        self.entries.get(seq as usize)
    }

    /// All entries, in sequence order (replay's input).
    pub fn entries(&self) -> impl Iterator<Item = &DeltaEntry> {
        self.entries.iter()
    }

    /// The current materialized state of a table.
    #[must_use]
    pub fn state(&self, table: &str) -> Option<&Table> {
        self.states.get(table)
    }

    /// The materialized state of a table after the first `seq`
    /// entries (prefix replay — the oracle's fold view,
    /// `Trace.tickTrace`).
    #[must_use]
    pub fn state_at(&self, table: &str, seq: u64) -> Option<Table> {
        let schema = self.schemas.get(table)?;
        let mut t = Table::new();
        for e in self.entries.iter().take(seq as usize) {
            if e.table == table {
                t.patch(schema, &e.change);
            }
        }
        Some(t)
    }

    /// Rewind to a sequence number: replay the stored inverses of
    /// entries `[seq, len)` tail-first AS COMPENSATION APPENDS (the
    /// log stays append-only; iterated `correct_invert` —
    /// `Machines.Rewind`'s `revert := patch ∘ invert`, at log scale).
    /// After `rewind_to(k)`, the current state equals `state_at(k)`.
    ///
    /// # Errors
    /// Backend I/O failure during a compensation append.
    pub fn rewind_to(&mut self, seq: u64) -> Result<(), DeltaError> {
        let start = usize::try_from(seq).unwrap_or(usize::MAX).min(self.entries.len());
        let compensations: Vec<(String, Change)> = self.entries[start..]
            .iter()
            .rev()
            .map(|e| (e.table.clone(), e.inverse.clone()))
            .collect();
        for (table, inverse) in compensations {
            self.append(&table, inverse)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::row::{Field, Row};

    fn schemas() -> SchemaSet {
        let mut s = SchemaSet::new();
        s.register(
            "user",
            Schema::new(vec![
                Field { name: "id".into(), ty: Ty::U64 },
                Field { name: "name".into(), ty: Ty::Str },
            ]),
        );
        s
    }

    fn user_schema() -> Schema {
        Schema::new(vec![
            Field { name: "id".into(), ty: Ty::U64 },
            Field { name: "name".into(), ty: Ty::Str },
        ])
    }

    fn user(id: u64, name: &str) -> Row {
        match Row::new(&user_schema(), vec![Value::U64(id), Value::Str(name.into())]) {
            Some(r) => r,
            None => panic!("test row must check"),
        }
    }

    #[test]
    fn append_replay_rewind() {
        let mut log = match DeltaLog::open_with(MemBackend::new(), schemas()) {
            Ok(l) => l,
            Err(e) => panic!("open: {e}"),
        };
        let r0 = match log.append("user", Change::Insert(user(1, "a"))) {
            Ok(s) => s,
            Err(e) => panic!("append: {e}"),
        };
        assert_eq!(r0, 0);
        let _ = log.append("user", Change::Update(user(1, "b")));
        let _ = log.append("user", Change::Remove(Value::U64(1)));
        assert_eq!(log.len(), 3);
        // Inverses captured: insert→remove, update→restore "a", remove→insert "b".
        assert_eq!(
            log.entry(0).map(|e| &e.inverse),
            Some(&Change::Remove(Value::U64(1)))
        );
        assert_eq!(
            log.entry(1).map(|e| &e.inverse),
            Some(&Change::Update(user(1, "a")))
        );
        assert_eq!(
            log.entry(2).map(|e| &e.inverse),
            Some(&Change::Insert(user(1, "b")))
        );
        // Current state: empty. state_at(1): the inserted row.
        assert_eq!(log.state("user").map(Table::rows).map(|mut r| r.next()), Some(None));
        let at1 = log.state_at("user", 1);
        assert_eq!(
            at1.as_ref().map(|t| t.rows().count()),
            Some(1)
        );
        // Rewind to 1: compensation appends invert entries 2 and 1.
        if let Err(e) = log.rewind_to(1) {
            panic!("rewind: {e}");
        }
        assert_eq!(log.state("user"), log.state_at("user", 1).as_ref());
        // Unknown table + bad payloads reject.
        assert!(matches!(
            log.append("nope", Change::Remove(Value::U64(1))),
            Err(DeltaError::UnknownTable(_))
        ));
        assert!(matches!(
            log.append("user", Change::Remove(Value::Str("x".into()))),
            Err(DeltaError::SchemaMismatch { .. })
        ));
    }
}

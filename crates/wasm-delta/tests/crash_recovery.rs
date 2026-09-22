//! Crash recovery over the durable backend: a partial write leaves a
//! torn tail; reopening must truncate to the last complete record and
//! yield a consistent log — never an error, never a partial entry.
//!
//! The sweep truncates the journal at EVERY byte offset (the strongest
//! form of "partial write": the crash can land anywhere) plus targeted
//! mid-record points, and checks:
//!   - reopen succeeds,
//!   - the recovered entries are exactly a prefix of the original,
//!   - the recovered state equals the prefix replay,
//!   - the log is still appendable after recovery.
//! Negative controls: a wrong-version record and a mid-log corrupted
//! payload are ERRORS (not silent truncation).

use std::path::PathBuf;

mod common;

use common::{Lcg, row, schemas, tempdir};
use wasm_delta::{Change, DeltaError, DeltaLog, FsBackend, Schema, Value};

/// Write a journal of `n` entries through the file backend; return the
/// path + the full byte content + per-record end offsets.
fn write_journal(dir: &PathBuf, n: u32) -> (PathBuf, Vec<u8>, Vec<usize>) {
    let path = dir.join("journal.bin");
    let mut log = DeltaLog::open(&path, schemas()).unwrap_or_else(|e| panic!("open: {e}"));
    let schema = schemas()
        .get("t")
        .unwrap_or_else(|| panic!("registered"))
        .clone();
    let mut r = Lcg(0xc0ffee);
    for i in 0..n {
        let key = r.below(6);
        let change = match r.below(3) {
            0 => Change::Insert(row(
                &schema,
                key,
                &format!("inserted-{i}-with-some-payload-bytes"),
            )),
            1 => Change::Update(row(&schema, key, &format!("updated-{i}"))),
            _ => Change::Remove(Value::U64(key)),
        };
        log.append("t", change)
            .unwrap_or_else(|e| panic!("append: {e}"));
    }
    drop(log);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read: {e}"));
    // Recompute the record boundaries by scanning with a fresh log open
    // per prefix — but cheaper: the offsets are where reopen stops.
    (path, bytes, Vec::new())
}

/// The reference: entries of a log opened over the complete journal.
fn open_entries(path: &PathBuf) -> Vec<wasm_delta::DeltaEntry> {
    let log = DeltaLog::open(path, schemas()).unwrap_or_else(|e| panic!("open: {e}"));
    log.entries().cloned().collect()
}

/// THE crash-recovery sweep: every truncation point.
#[test]
fn torn_tail_at_every_offset() {
    let dir = tempdir("sweep");
    let (path, bytes, _) = write_journal(&dir, 24);
    let reference = open_entries(&path);
    assert_eq!(reference.len(), 24);
    let tmp = dir.join("cut.bin");
    let mut recovered_any = 0u32;
    for cut in 0..=bytes.len() {
        std::fs::write(&tmp, &bytes[..cut]).unwrap_or_else(|e| panic!("write: {e}"));
        let log = DeltaLog::open(&tmp, schemas())
            .unwrap_or_else(|e| panic!("reopen at cut {cut} must succeed: {e}"));
        let got: Vec<_> = log.entries().cloned().collect();
        // The recovered log is exactly a prefix of the reference.
        assert!(
            got.len() <= reference.len(),
            "cut {cut}: recovered MORE entries than written"
        );
        for (i, e) in got.iter().enumerate() {
            assert_eq!(e, &reference[i], "cut {cut}: entry {i} diverged");
        }
        // State = prefix replay (an untouched table reads as empty).
        let k = got.len() as u64;
        assert_eq!(
            log.state("t").cloned().unwrap_or_default(),
            log.state_at("t", k).unwrap_or_default(),
            "cut {cut}: state != replay"
        );
        // The recovered log is still appendable.
        if got.len() < reference.len() {
            recovered_any += 1;
        }
        let schema = schemas()
            .get("t")
            .unwrap_or_else(|| panic!("registered"))
            .clone();
        log_post_recovery_append(&tmp, &schema);
    }
    assert!(
        recovered_any > 0,
        "vacuous: no truncation ever dropped an entry"
    );
    std::fs::remove_dir_all(&dir).unwrap_or_else(|e| panic!("cleanup: {e}"));
}

/// After recovery, one more append must land and re-open cleanly.
fn log_post_recovery_append(path: &PathBuf, schema: &Schema) {
    let mut log = DeltaLog::open(path, schemas()).unwrap_or_else(|e| panic!("reopen: {e}"));
    let before = log.len();
    log.append("t", Change::Insert(row(schema, 999, "post-recovery")))
        .unwrap_or_else(|e| panic!("post-recovery append: {e}"));
    drop(log);
    let log = DeltaLog::open(path, schemas()).unwrap_or_else(|e| panic!("re-reopen: {e}"));
    assert_eq!(log.len(), before + 1);
    assert_eq!(
        log.entry(before).map(|e| &e.change),
        Some(&Change::Insert(row(schema, 999, "post-recovery")))
    );
}

/// Targeted mid-record cuts: the crash lands inside the envelope header
/// (mid-varint), inside the payload length, and inside the payload.
#[test]
fn targeted_mid_record_cuts() {
    let dir = tempdir("targeted");
    let (path, bytes, _) = write_journal(&dir, 6);
    let reference = open_entries(&path);
    // Find the last record's start: the longest strict prefix that
    // reopens with 5 entries. Probe by deletion.
    let mut last_start = 0usize;
    for cut in (0..bytes.len()).rev() {
        let tmp = dir.join("probe.bin");
        std::fs::write(&tmp, &bytes[..cut]).unwrap_or_else(|e| panic!("write: {e}"));
        let log = DeltaLog::open(&tmp, schemas()).unwrap_or_else(|e| panic!("open: {e}"));
        if log.len() == 5 {
            last_start = cut;
            break;
        }
    }
    assert!(last_start > 0, "record boundary probe failed");
    // Every cut strictly inside the last record recovers exactly 5.
    for cut in (last_start + 1)..bytes.len() {
        let tmp = dir.join("probe2.bin");
        std::fs::write(&tmp, &bytes[..cut]).unwrap_or_else(|e| panic!("write: {e}"));
        let log = DeltaLog::open(&tmp, schemas())
            .unwrap_or_else(|e| panic!("mid-record cut {cut} must succeed: {e}"));
        assert_eq!(log.len(), 5, "mid-record cut {cut}: wrong prefix length");
        for (i, e) in log.entries().enumerate() {
            assert_eq!(e, &reference[i], "cut {cut}: entry {i} diverged");
        }
    }
    std::fs::remove_dir_all(&dir).unwrap_or_else(|e| panic!("cleanup: {e}"));
}

/// NEGATIVE CONTROL: a complete envelope with the wrong VERSION is an
/// error, never silent truncation (format change ≠ crash).
#[test]
fn wrong_version_is_an_error() {
    let dir = tempdir("neg-version");
    let (path, mut bytes, _) = write_journal(&dir, 3);
    // First byte is the version varint of the first record (VERSION=1).
    bytes[0] = 2;
    std::fs::write(&path, &bytes).unwrap_or_else(|e| panic!("write: {e}"));
    match DeltaLog::<FsBackend>::open(&path, schemas()) {
        Err(DeltaError::WrongVersion { found: 2, .. }) => {}
        Err(e) => panic!("expected WrongVersion, got {e}"),
        Ok(_) => panic!("wrong-version journal must not open"),
    }
    std::fs::remove_dir_all(&dir).unwrap_or_else(|e| panic!("cleanup: {e}"));
}

/// NEGATIVE CONTROL: a mid-log corrupted entry payload (complete
/// envelope, undecodable entry) is an error, not truncation.
#[test]
fn mid_log_corruption_is_an_error() {
    let dir = tempdir("neg-corrupt");
    let (path, bytes, _) = write_journal(&dir, 6);
    // Corrupt the FIRST record's payload in a way that stays a complete
    // envelope: record 0 starts at 0; header = version(1B) +
    // fingerprint varint + payload-length varint. Find the payload
    // start by decoding the header manually: version is 1 byte ("01");
    // walk varints.
    let varint_len = |bs: &[u8]| bs.iter().position(|b| *b < 128).map(|p| p + 1);
    let Some(vlen) = varint_len(&bytes) else {
        panic!("header")
    };
    let Some(flen) = varint_len(&bytes[vlen..]) else {
        panic!("header")
    };
    let Some(llen) = varint_len(&bytes[vlen + flen..]) else {
        panic!("header")
    };
    let payload_start = vlen + flen + llen;
    // Flip the table-name tag byte of the entry payload (payload[0] is
    // the table string's char-count varint; 24 chars → 0x18; a huge
    // count overruns the payload → undecodable entry).
    let mut bad = bytes.clone();
    bad[payload_start] = 0x7f;
    std::fs::write(&path, &bad).unwrap_or_else(|e| panic!("write: {e}"));
    match DeltaLog::<FsBackend>::open(&path, schemas()) {
        Err(DeltaError::Corrupt { offset: 0, .. }) => {}
        Err(e) => panic!("expected Corrupt at 0, got {e}"),
        Ok(_) => panic!("mid-log corruption must not open cleanly"),
    }
    std::fs::remove_dir_all(&dir).unwrap_or_else(|e| panic!("cleanup: {e}"));
}

//! The crash-recovery suite: a torn tail is honest (last-good-frame
//! recovery + the REPORTED cut, or the strict typed refusal); a corrupt
//! complete frame is refused in every mode; the recovered log is
//! exactly a prefix and stays appendable.

use mandate_delta::delta::Delta;
use mandate_delta::error::DeltaError;
use mandate_delta::log::DeltaLog;
use mandate_delta::schema::{Field, Row, Schema};
use mandate_delta::value::{Ty, Value};

fn fixture_schema() -> Schema {
    Schema::build(
        vec![
            Field { name: "id".into(), ty: Ty::U64 },
            Field { name: "name".into(), ty: Ty::Str },
        ],
        "id",
    )
    .unwrap_or_else(|e| panic!("fixture schema: {e}"))
}

fn fixture_row(id: u64, name: &str) -> Row {
    Row::build(&fixture_schema(), vec![Value::U64(id), Value::Str(name.into())])
        .unwrap_or_else(|e| panic!("fixture row: {e}"))
}

/// A per-test temp dir (std-only: no tempfile dep).
struct TempDir {
    path: std::path::PathBuf,
    stamp: String,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        let stamp = format!(
            "mandate-delta-{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        );
        let path = std::env::temp_dir().join(&stamp);
        std::fs::create_dir_all(&path).unwrap_or_else(|e| panic!("tempdir: {e}"));
        Self { path, stamp }
    }

    fn join(&self, name: &str) -> std::path::PathBuf {
        self.path.join(name)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.path).unwrap_or_else(|e| panic!("cleanup {}: {e}", self.stamp));
    }
}

/// Write a journal of `n` entries through the FILE backend; return the
/// path + the full byte content.
fn write_journal(dir: &TempDir, n: u64) -> (std::path::PathBuf, Vec<u8>) {
    let path = dir.join("journal.bin");
    let mut log = DeltaLog::open(&path, fixture_schema())
        .unwrap_or_else(|e| panic!("open: {e}"));
    for i in 0..n {
        let d = match i % 3 {
            0 => Delta::Insert(fixture_row(i, &format!("row-{i}-with-some-payload-bytes"))),
            1 => Delta::Update(fixture_row(i, &format!("updated-{i}"))),
            _ => Delta::Remove(Value::U64(i)),
        };
        log.append(d).unwrap_or_else(|e| panic!("append: {e}"));
    }
    drop(log);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read: {e}"));
    (path, bytes)
}

/// The reference: a log opened over the complete journal.
fn open_entries(path: &std::path::Path) -> Vec<Delta> {
    let log = DeltaLog::open(path, fixture_schema()).unwrap_or_else(|e| panic!("open: {e}"));
    log.entries().to_vec()
}

/// THE crash-recovery sweep: the journal truncated at EVERY byte offset
/// (the strongest form of "the crash landed anywhere"). Each cut must:
/// recover to exactly a prefix of the reference, present the prefix
/// replay's state, REPORT the cut (never silent), and stay appendable.
#[test]
fn torn_tail_at_every_offset() {
    let dir = TempDir::new("sweep");
    let (reference_path, bytes) = write_journal(&dir, 24);
    let reference = open_entries(&reference_path);
    assert_eq!(reference.len(), 24);

    let tmp = dir.join("cut.bin");
    // The frame boundaries of the reference journal (the frames are
    // self-delimiting — walk them): a cut ON a boundary is a clean
    // shorter journal (no recovery); a cut INSIDE a frame is the torn
    // tail (recovery + report).
    let mut boundaries: Vec<usize> = vec![0];
    {
        let mut rest: &[u8] = &bytes;
        while !rest.is_empty() {
            mandate_delta::delta::dec_delta(&fixture_schema(), &mut rest)
                .unwrap_or_else(|e| panic!("reference walk: {e:?}"));
            boundaries.push(bytes.len() - rest.len());
        }
    }
    let mut dropped_any = false;
    for cut in 0..=bytes.len() {
        std::fs::write(&tmp, &bytes[..cut]).unwrap_or_else(|e| panic!("write {cut}: {e}"));
        // The recovering open SUCCEEDS on every cut.
        let mut log = DeltaLog::open(&tmp, fixture_schema())
            .unwrap_or_else(|e| panic!("reopen at cut {cut}: {e}"));
        let got = log.entries().to_vec();
        // The recovered log is exactly a prefix of the reference.
        assert!(
            got.len() <= reference.len(),
            "cut {cut}: recovered MORE entries than written"
        );
        for (i, e) in got.iter().enumerate() {
            assert_eq!(e, &reference[i], "cut {cut}: entry {i} diverged");
        }
        // State = prefix replay.
        let k = got.len() as u64;
        assert_eq!(*log.state(), log.state_at(k), "cut {cut}: state != replay");
        // The cut is REPORTED exactly when it tore a frame (an interior
        // cut) — never silent. A cut ON a frame boundary is a clean
        // shorter journal (no recovery, no report); the empty file is
        // the fresh-journal shape (a crash before the first byte landed
        // is indistinguishable from no write at all).
        let interior = !boundaries.contains(&cut);
        if interior {
            dropped_any = true;
            let rec = log
                .recovery()
                .unwrap_or_else(|| panic!("cut {cut}: truncation was SILENT"));
            assert_eq!(rec.frames, k, "cut {cut}: recovery report's frame count");
            // The cut lands at the last good frame's boundary — at or
            // before the crash point (the torn frame itself never
            // survives).
            assert!(rec.offset as usize <= cut, "cut {cut}: recovery past the crash");
        } else {
            assert!(log.recovery().is_none(), "cut {cut}: phantom recovery report");
        }
        // The recovered log is still appendable, and the append survives
        // a reopen.
        let before = log.len();
        log.append(Delta::Insert(fixture_row(999, "post-recovery")))
            .unwrap_or_else(|e| panic!("cut {cut}: post-recovery append: {e}"));
        drop(log);
        let log = DeltaLog::open(&tmp, fixture_schema())
            .unwrap_or_else(|e| panic!("cut {cut}: re-reopen: {e}"));
        assert_eq!(log.len(), before + 1, "cut {cut}: post-recovery append lost");
        assert_eq!(
            log.entry(before),
            Some(&Delta::Insert(fixture_row(999, "post-recovery")))
        );
    }
    assert!(dropped_any, "vacuous: no truncation ever dropped a frame tail");
}

/// The STRICT face: the same torn cuts are the typed refusal — the
/// honest alternative to recovery, never a silent anything.
#[test]
fn strict_open_refuses_torn_tails() {
    let dir = TempDir::new("strict");
    let (reference_path, bytes) = write_journal(&dir, 6);
    let reference = open_entries(&reference_path);
    let tmp = dir.join("cut.bin");
    let mut refused_any = false;
    for cut in 0..bytes.len() {
        std::fs::write(&tmp, &bytes[..cut]).unwrap_or_else(|e| panic!("write {cut}: {e}"));
        match DeltaLog::open_strict(&tmp, fixture_schema()) {
            Err(DeltaError::TornTail { offset }) => {
                // The torn offset is the last good frame's boundary — at
                // or before the crash point.
                assert!(offset as usize <= cut, "cut {cut}: torn offset {offset} past the crash");
                refused_any = true;
            }
            Ok(log) => {
                // A cut that lands exactly on a frame boundary is NOT
                // torn — the strict open succeeds with the full prefix.
                let full = DeltaLog::open(&tmp, fixture_schema())
                    .unwrap_or_else(|e| panic!("open at cut {cut}: {e}"));
                assert_eq!(log.len(), full.len(), "cut {cut}: strict/recover skew");
                assert_eq!(
                    log.entries(),
                    &reference[..full.len() as usize],
                    "cut {cut}: entries"
                );
                assert!(log.recovery().is_none());
            }
            Err(e) => panic!("cut {cut}: unexpected error {e}"),
        }
    }
    assert!(refused_any, "vacuous: no cut ever tore a frame");
}

/// NEGATIVE CONTROL: a mid-log corrupted frame (a COMPLETE frame with
/// bad bytes — a shape no torn write can produce) is a typed ERROR in
/// every mode. Never truncation, never a silent skip.
#[test]
fn mid_log_corruption_is_an_error() {
    let dir = TempDir::new("neg-corrupt");
    let (path, bytes) = write_journal(&dir, 6);
    // Corrupt the FIRST frame's tag byte (0x00 insert → 0x05: a tag no
    // ctor claims). The file stays complete — every byte is present.
    let mut bad = bytes.clone();
    assert_eq!(bad[0], 0x00, "fixture: first byte must be the insert tag");
    bad[0] = 0x05;
    std::fs::write(&path, &bad).unwrap_or_else(|e| panic!("write: {e}"));
    for (name, open) in [
        ("recover", DeltaLog::open(&path, fixture_schema())),
        ("strict", DeltaLog::open_strict(&path, fixture_schema())),
    ] {
        match open {
            Err(DeltaError::Corrupt { offset: 0, reason }) => {
                assert!(reason.contains("tag"), "corrupt reason names the tag: {reason}");
            }
            Err(e) => panic!("{name}: expected Corrupt at 0, got {e}"),
            Ok(_) => panic!("{name}: mid-log corruption must not open cleanly"),
        }
    }
}

/// NEGATIVE CONTROL: corruption INSIDE a frame's payload — a complete
/// frame whose atom bytes are out of policy (a non-canonical varint in
/// the row) refuses with the typed error, never a silent misparse.
#[test]
fn corrupt_atom_inside_frame_is_an_error() {
    let dir = TempDir::new("neg-atom");
    let (path, bytes) = write_journal(&dir, 4);
    // Frame 0: tag(1) + row count(1) + u64 varint + string. Flip the
    // string's char-count varint to the non-canonical 0x80 0x00.
    let mut bad = bytes.clone();
    // Find the string count: tag@0, count@1 (=2), u64 varint next
    // (row-{i} id < 128 for i<8 → 1 byte), so the string count is at
    // offset 3.
    assert_eq!(bad[1], 2, "fixture: field count");
    bad[3] = 0x80;
    bad.insert(4, 0x00);
    std::fs::write(&path, &bad).unwrap_or_else(|e| panic!("write: {e}"));
    match DeltaLog::open(&path, fixture_schema()) {
        Err(DeltaError::Corrupt { offset: 0, .. }) => {}
        Err(e) => panic!("expected Corrupt at 0, got {e}"),
        Ok(_) => panic!("a non-canonical varint must not decode"),
    }
}

/// The frame stream's prefix argument, exercised: corrupting the LAST
/// frame's tag still refuses (it's a complete frame with bad bytes, not
/// a torn write) — the recovery cut only ever applies to byte shapes a
/// torn write can produce.
#[test]
fn last_frame_corruption_refuses() {
    let dir = TempDir::new("neg-last");
    let (path, bytes) = write_journal(&dir, 3);
    let mut bad = bytes.clone();
    let last = bad.len() - 1;
    // The last frame is a remove: tag + varint key. Corrupt its tag.
    bad[last - 1] = 0x09;
    std::fs::write(&path, &bad).unwrap_or_else(|e| panic!("write: {e}"));
    match DeltaLog::open(&path, fixture_schema()) {
        Err(DeltaError::Corrupt { offset, .. }) => {
            assert!(offset > 0, "the corruption is in the LAST frame");
        }
        Err(e) => panic!("expected Corrupt, got {e}"),
        Ok(_) => panic!("last-frame corruption must not open cleanly"),
    }
}

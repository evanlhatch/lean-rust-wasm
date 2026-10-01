//! The snapshot/compaction suite: snapshot + tail ≡ full replay (the
//! PROPERTY, swept over the tree's LCG stream); the crash teeth (torn
//! snapshot, torn tail, torn both, compact interrupted — each recovers
//! AND reports); the byte-tie (the snapshot's atoms are the log's
//! atoms).

use mandate_delta::delta::{Delta, Table};
use mandate_delta::error::DeltaError;
use mandate_delta::log::DeltaLog;
use mandate_delta::schema::fixtures::{fixture, fixture_row};
use mandate_delta::scratch::ScratchDir;
use mandate_delta::snapshot::{self, FallbackReason, SnapshotReport};
use mandate_delta::value::Value;

fn fixture_schema() -> mandate_delta::Schema {
    fixture()
}

fn temp_dir(tag: &str) -> ScratchDir {
    ScratchDir::new(&format!("mandate-delta-snap-{tag}")).unwrap_or_else(|e| panic!("tempdir: {e}"))
}

/// THE LCG STREAM (the tree's one recurrence — TestingKit.lcg, Knuth 64,
/// the same constants `bytes_hash` pins): the sweep's op stream. No
/// fixture file, no RNG crate — the stream IS the discipline's fixture.
const LCG_MULT: u64 = 6364136223846793005;
const LCG_INC: u64 = 1442695040888963407;

fn lcg_next(state: &mut u64) -> u64 {
    *state = state.wrapping_mul(LCG_MULT).wrapping_add(LCG_INC);
    *state
}

/// A deterministic op stream of `n` deltas over the fixture schema,
/// swept from the LCG stream (insert/update/remove in a fixed rotation
/// keyed on the stream — the ids stay in a small window so updates and
/// removes actually hit).
fn op_stream(seed: u64, n: usize) -> Vec<Delta> {
    let mut st = seed;
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let r = lcg_next(&mut st);
        let id = r % 7;
        let name = format!("row-{id}-{i}");
        out.push(match (r >> 8) % 3 {
            0 => Delta::Insert(fixture_row(id, &name)),
            1 => Delta::Update(fixture_row(id, &name)),
            _ => Delta::Remove(Value::U64(id)),
        });
    }
    out
}

/// The reference full replay (the log alone — always the correct state).
fn full_replay(schema: &mandate_delta::Schema, ops: &[Delta]) -> Table {
    let mut t = Table::new();
    for d in ops {
        t.apply(schema, d);
    }
    t
}

/// THE PROPERTY: snapshot + tail ≡ full replay — swept over (seed,
/// length, compact point). After compact(S), a snapshotted open's state
/// is the full replay's, its entries are exactly ops[S..], and the
/// rebased log stays appendable.
#[test]
fn snapshot_plus_tail_equals_full_replay_sweep() {
    let dir = temp_dir("sweep");
    let schema = fixture_schema();
    let mut checked_any = false;
    for (case, (seed, n, s)) in [
        (0u32, (1u64, 1usize, 0usize)),
        (1, (2, 1, 1)),
        (2, (3, 8, 0)),
        (3, (4, 8, 4)),
        (4, (5, 8, 8)),
        (5, (0xDEAD_BEEF, 40, 17)),
        (6, (0xCAFE_F00D, 40, 39)),
        (7, (0x5EED_1234, 40, 40)),
    ] {
        let ops = op_stream(seed, n);
        let reference = full_replay(&schema, &ops);
        let log_path = dir.path().join(format!("case{case}.bin"));
        let snap_path = snapshot::snapshot_path_for(&log_path);
        {
            let mut log = DeltaLog::open(&log_path, schema.clone())
                .unwrap_or_else(|e| panic!("case {case}: open: {e}"));
            for (i, d) in ops.iter().enumerate() {
                log.append(d.clone())
                    .unwrap_or_else(|e| panic!("case {case}: append {i}: {e}"));
            }
            log.compact(s as u64, &snap_path)
                .unwrap_or_else(|e| panic!("case {case}: compact: {e}"));
            // In memory, compaction changes the INDEX, never the state.
            assert_eq!(
                *log.state(),
                reference,
                "case {case}: state changed by compact"
            );
            assert_eq!(log.len(), (n - s) as u64, "case {case}: rebased length");
            assert_eq!(log.entries(), &ops[s..], "case {case}: rebased entries");
        }
        // Reopen: snapshot + tail = the full replay.
        let (mut log, report) = DeltaLog::open_snapshotted(&log_path, &snap_path, schema.clone())
            .unwrap_or_else(|e| panic!("case {case}: reopen: {e}"));
        assert_eq!(
            report,
            SnapshotReport::Applied { seqno: s as u64 },
            "case {case}: report"
        );
        assert_eq!(*log.state(), reference, "case {case}: reopened state");
        assert_eq!(log.entries(), &ops[s..], "case {case}: reopened entries");
        // The rebased log stays appendable and honest.
        log.append(Delta::Insert(fixture_row(777, "post")))
            .unwrap_or_else(|e| panic!("case {case}: post-append: {e}"));
        drop(log);
        let (log, _) = DeltaLog::open_snapshotted(&log_path, &snap_path, schema.clone())
            .unwrap_or_else(|e| panic!("case {case}: re-reopen: {e}"));
        let mut expect = reference;
        expect.apply(&schema, &Delta::Insert(fixture_row(777, "post")));
        assert_eq!(*log.state(), expect, "case {case}: post-append state");
        checked_any = true;
    }
    assert!(checked_any, "vacuous: the sweep never ran");
}

/// The recovery matrix's tooth — TORN SNAPSHOT: the snapshot file cut
/// at EVERY byte offset never silently loads; every open falls back to
/// the full replay with the torn report, and the log survives intact.
/// The fallback's state is the LOG's own replay — after a completed
/// compaction that is the tail's replay (the snapshot was the only
/// carrier of the retired prefix; losing it is REPORTED, never
/// silent, and the state is never WRONG).
#[test]
fn torn_snapshot_at_every_offset_falls_back_and_reports() {
    let dir = temp_dir("torn-snap");
    let schema = fixture_schema();
    let ops = op_stream(42, 9);
    // The tail's replay: the full replay of the post-cut log.
    let reference = full_replay(&schema, &ops[4..]);
    let log_path = dir.path().join("j.bin");
    let snap_path = snapshot::snapshot_path_for(&log_path);
    {
        let mut log = DeltaLog::open(&log_path, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
        for d in &ops {
            log.append(d.clone()).unwrap_or_else(|e| panic!("{e}"));
        }
        log.compact(4, &snap_path).unwrap_or_else(|e| panic!("{e}"));
    }
    let raw = std::fs::read(&snap_path).unwrap_or_else(|e| panic!("read: {e}"));
    assert!(raw.len() > 8, "vacuous fixture");
    let cut_path = dir.path().join("cut.snapshot");
    let mut torn_any = false;
    for cut in 0..raw.len() {
        std::fs::write(&cut_path, &raw[..cut]).unwrap_or_else(|e| panic!("write {cut}: {e}"));
        let (log, report) = DeltaLog::open_snapshotted(&log_path, &cut_path, schema.clone())
            .unwrap_or_else(|e| panic!("cut {cut}: open: {e}"));
        match &report {
            SnapshotReport::FellBack(FallbackReason::Torn { .. }) => torn_any = true,
            other => panic!("cut {cut}: expected a torn report, got {other}"),
        }
        // The fallback is the LOG's full replay — never a wrong state.
        assert_eq!(*log.state(), reference, "cut {cut}: fallback state");
        assert_eq!(log.entries(), &ops[4..], "cut {cut}: fallback entries");
        assert!(log.recovery().is_none(), "cut {cut}: phantom log recovery");
        drop(log);
    }
    // The intact file still applies (the negative control).
    std::fs::write(&cut_path, &raw).unwrap_or_else(|e| panic!("write: {e}"));
    let (log, report) = DeltaLog::open_snapshotted(&log_path, &cut_path, schema.clone())
        .unwrap_or_else(|e| panic!("open: {e}"));
    assert_eq!(report, SnapshotReport::Applied { seqno: 4 });
    // The APPLIED path recovers the FULL state (snapshot + tail) — the
    // torn fallbacks above recovered only the tail's replay, REPORTED.
    assert_eq!(*log.state(), full_replay(&schema, &ops));
    assert!(torn_any, "vacuous: no cut ever tore the snapshot");
}

/// The tooth — CORRUPT SNAPSHOT: complete bytes that refuse (a flipped
/// content-hash byte, a flipped state byte, bad magic) never load.
#[test]
fn corrupt_snapshot_never_loads() {
    let dir = temp_dir("corrupt-snap");
    let schema = fixture_schema();
    let ops = op_stream(7, 6);
    // The log's own replay (post-cut: the tail alone).
    let reference = full_replay(&schema, &ops[3..]);
    let log_path = dir.path().join("j.bin");
    let snap_path = snapshot::snapshot_path_for(&log_path);
    {
        let mut log = DeltaLog::open(&log_path, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
        for d in &ops {
            log.append(d.clone()).unwrap_or_else(|e| panic!("{e}"));
        }
        log.compact(3, &snap_path).unwrap_or_else(|e| panic!("{e}"));
    }
    let raw = std::fs::read(&snap_path).unwrap_or_else(|e| panic!("read: {e}"));
    let bad_path = dir.path().join("bad.snapshot");
    type Mutator = fn(&mut Vec<u8>);
    let mutators: &[(&str, Mutator)] = &[
        ("hash-byte", |b| {
            let n = b.len() - 1;
            b[n] ^= 0x01;
        }),
        ("state-byte", |b| {
            let m = b.len() / 2;
            b[m] ^= 0x01;
        }),
        ("magic", |b| b[0] = b'X'),
        ("trailing", |b| b.push(0)),
    ];
    for (name, mutate) in mutators.iter().copied() {
        let mut bad = raw.clone();
        mutate(&mut bad);
        std::fs::write(&bad_path, &bad).unwrap_or_else(|e| panic!("write {name}: {e}"));
        let (log, report) = DeltaLog::open_snapshotted(&log_path, &bad_path, schema.clone())
            .unwrap_or_else(|e| panic!("{name}: open: {e}"));
        match &report {
            SnapshotReport::FellBack(FallbackReason::Refused { .. }) => {}
            other => panic!("{name}: expected a refused report, got {other}"),
        }
        assert_eq!(*log.state(), reference, "{name}: fallback state");
        assert_eq!(log.entries(), &ops[3..], "{name}: fallback entries");
    }
}

/// The tooth — TORN TAIL (the log's) beside a snapshot: the tail's cut
/// is reported AND the snapshot still applies over the surviving
/// prefix; the state is the surviving replay, never more.
#[test]
fn torn_log_tail_beside_snapshot_recovers_and_reports() {
    let dir = temp_dir("torn-tail");
    let schema = fixture_schema();
    let ops = op_stream(9, 10);
    let log_path = dir.path().join("j.bin");
    let snap_path = snapshot::snapshot_path_for(&log_path);
    {
        let mut log = DeltaLog::open(&log_path, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
        for d in &ops {
            log.append(d.clone()).unwrap_or_else(|e| panic!("{e}"));
        }
        log.compact(4, &snap_path).unwrap_or_else(|e| panic!("{e}"));
        // Two more frames AFTER the compaction (the tail grew).
        log.append(Delta::Insert(fixture_row(50, "x")))
            .unwrap_or_else(|e| panic!("{e}"));
        log.append(Delta::Insert(fixture_row(51, "y")))
            .unwrap_or_else(|e| panic!("{e}"));
    }
    let bytes = std::fs::read(&log_path).unwrap_or_else(|e| panic!("read: {e}"));
    // Tear the tail: cut the file mid-last-frame.
    let torn = &bytes[..bytes.len() - 1];
    std::fs::write(&log_path, torn).unwrap_or_else(|e| panic!("write: {e}"));
    let (log, report) = DeltaLog::open_snapshotted(&log_path, &snap_path, schema.clone())
        .unwrap_or_else(|e| panic!("open: {e}"));
    // The snapshot applies (rule B: the log is the tail) AND the log's
    // own cut is reported. BOTH reports surface.
    assert_eq!(
        report,
        SnapshotReport::Applied { seqno: 4 },
        "snapshot report"
    );
    let rec = log
        .recovery()
        .unwrap_or_else(|| panic!("the torn tail went SILENT"));
    // Surviving frames: 6 post-cut + 2 post-appends - 1 torn = 7.
    assert_eq!(rec.frames, 7, "the good prefix's frame count");
    // The state: snapshot + surviving tail (one post-append frame).
    let mut expect = full_replay(&schema, &ops);
    expect.apply(&schema, &Delta::Insert(fixture_row(50, "x")));
    assert_eq!(*log.state(), expect, "state = snapshot + surviving tail");
    assert_eq!(log.len(), 7);
}

/// The tooth — TORN BOTH: a torn snapshot AND a torn log tail. Each
/// reports its own anomaly; the full replay of the surviving log
/// prefix takes over (the always-correct fallback).
#[test]
fn torn_both_recovers_and_reports_twice() {
    let dir = temp_dir("torn-both");
    let schema = fixture_schema();
    let ops = op_stream(11, 6);
    // Survivors: the post-cut tail (ops[3..], 3 frames) torn mid-last
    // frame — 2 frames' worth of state, both anomalies REPORTED.
    let reference = full_replay(&schema, &ops[3..5]);
    let log_path = dir.path().join("j.bin");
    let snap_path = snapshot::snapshot_path_for(&log_path);
    {
        let mut log = DeltaLog::open(&log_path, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
        for d in &ops {
            log.append(d.clone()).unwrap_or_else(|e| panic!("{e}"));
        }
        log.compact(3, &snap_path).unwrap_or_else(|e| panic!("{e}"));
    }
    // Torn snapshot: cut mid-file.
    let snap_raw = std::fs::read(&snap_path).unwrap_or_else(|e| panic!("read: {e}"));
    std::fs::write(&snap_path, &snap_raw[..snap_raw.len() - 2])
        .unwrap_or_else(|e| panic!("write: {e}"));
    // Torn log: cut mid-last-frame.
    let log_raw = std::fs::read(&log_path).unwrap_or_else(|e| panic!("read: {e}"));
    std::fs::write(&log_path, &log_raw[..log_raw.len() - 1])
        .unwrap_or_else(|e| panic!("write: {e}"));
    let (log, report) = DeltaLog::open_snapshotted(&log_path, &snap_path, schema.clone())
        .unwrap_or_else(|e| panic!("open: {e}"));
    assert!(
        matches!(
            report,
            SnapshotReport::FellBack(FallbackReason::Torn { .. })
        ),
        "the torn snapshot must be reported: {report}"
    );
    let rec = log
        .recovery()
        .unwrap_or_else(|| panic!("the torn log tail went SILENT"));
    assert_eq!(rec.frames, 2, "the surviving log prefix");
    assert_eq!(*log.state(), reference, "state = surviving replay");
}

/// The tooth — COMPACT INTERRUPTED (the pre-cut window): the snapshot
/// landed, the log's head cut did NOT happen. The open verifies the
/// subsumed prefix (rule A) and skips exactly its frames; a later
/// compact heals the dead prefix.
#[test]
fn compact_interrupted_before_the_cut() {
    let dir = temp_dir("interrupted");
    let schema = fixture_schema();
    let ops = op_stream(13, 8);
    let reference = full_replay(&schema, &ops);
    let log_path = dir.path().join("j.bin");
    let snap_path = snapshot::snapshot_path_for(&log_path);

    // Simulate the interrupted compaction: full log + a snapshot
    // computed FROM that log at seqno 5 (exactly what compact leaves
    // between the snapshot write and the cut).
    let mut log = DeltaLog::open(&log_path, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
    for d in &ops {
        log.append(d.clone()).unwrap_or_else(|e| panic!("{e}"));
    }
    {
        let frames = log.entries();
        let (m, l) = snapshot::compact_meta(&schema, frames, 5).unwrap_or_else(|e| panic!("{e}"));
        // The prefix bytes must tie the log FILE's own bytes (the file
        // is the frames' concatenation — the walk starts at byte 0).
        let file = std::fs::read(&log_path).unwrap_or_else(|e| panic!("read: {e}"));
        assert_eq!(l, rest_len(&schema, frames, 5));
        assert_eq!(m.prefix_hash, snapshot::bytes_hash(&file[..l]));
    }
    let (meta, _) =
        snapshot::compact_meta(&schema, log.entries(), 5).unwrap_or_else(|e| panic!("{e}"));
    let raw = snapshot::encode_snapshot(&meta, &log.state_at(5));
    snapshot::write_snapshot_atomic(&snap_path, &raw).unwrap_or_else(|e| panic!("{e}"));
    drop(log);

    // The open: rule A verifies the still-present prefix, skips it.
    let (mut log, report) = DeltaLog::open_snapshotted(&log_path, &snap_path, schema.clone())
        .unwrap_or_else(|e| panic!("open: {e}"));
    assert_eq!(report, SnapshotReport::Applied { seqno: 5 });
    assert_eq!(
        *log.state(),
        reference,
        "state after the interrupted compact"
    );
    assert_eq!(log.len(), 3, "the dead prefix still sits in the file");
    // A later compact heals it (the real cut this time).
    log.compact(3, &snap_path)
        .unwrap_or_else(|e| panic!("heal compact: {e}"));
    drop(log);
    let (log, report) = DeltaLog::open_snapshotted(&log_path, &snap_path, schema.clone())
        .unwrap_or_else(|e| panic!("re-open: {e}"));
    assert_eq!(report, SnapshotReport::Applied { seqno: 3 });
    assert_eq!(log.len(), 0, "the log file is the tail alone now");
    assert_eq!(*log.state(), reference);
}

/// The bytes of frames [0..s) as the FILE carries them (the frames
/// after the journal count byte) — the test's own re-derivation of the
/// prefix length (independent of compact_meta's).
fn rest_len(schema: &mandate_delta::Schema, frames: &[Delta], s: usize) -> usize {
    let mut n = 0;
    let mut buf = Vec::new();
    for d in &frames[..s] {
        buf.clear();
        assert!(mandate_delta::delta::enc_delta(schema, d, &mut buf));
        n += buf.len();
    }
    n
}

/// The tooth — UNALIGNED: a snapshot written against a DIFFERENT log
/// (foreign lineage) never loads silently; the open reports the
/// misalignment and full-replays the log it actually has.
#[test]
fn foreign_snapshot_refuses_to_align() {
    let dir = temp_dir("foreign");
    let schema = fixture_schema();
    // Log A: the snapshot's lineage.
    let log_a = dir.path().join("a.bin");
    let snap_a = snapshot::snapshot_path_for(&log_a);
    let mut la = DeltaLog::open(&log_a, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
    for d in op_stream(21, 5) {
        la.append(d).unwrap_or_else(|e| panic!("{e}"));
    }
    la.compact(2, &snap_a).unwrap_or_else(|e| panic!("{e}"));
    drop(la);
    // Log B: a different lineage (different ops entirely).
    let log_b = dir.path().join("b.bin");
    let mut lb = DeltaLog::open(&log_b, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
    for d in op_stream(99, 4) {
        lb.append(d).unwrap_or_else(|e| panic!("{e}"));
    }
    let reference_b = full_replay(&schema, &op_stream(99, 4));
    drop(lb);
    // Open B against A's snapshot: unaligned, reported, full replay.
    let (log, report) = DeltaLog::open_snapshotted(&log_b, &snap_a, schema.clone())
        .unwrap_or_else(|e| panic!("open: {e}"));
    assert_eq!(report, SnapshotReport::FellBack(FallbackReason::Unaligned));
    assert_eq!(
        *log.state(),
        reference_b,
        "the fallback is B's own full replay"
    );
}

/// The byte-tie: the snapshot's ATOMS are the log's atoms — a
/// non-canonical varint in the snapshot's seqno refuses with the SAME
/// typed corruption the frames refuse with (the generated codec's
/// policy), never a silent misparse.
#[test]
fn snapshot_atoms_refuse_out_of_policy_bytes() {
    let schema = fixture_schema();
    // varint 0x80 0x00 = non-canonical zero — the atoms' refusal.
    let mut raw = b"MDL1".to_vec();
    raw.extend_from_slice(&[0x80, 0x00]); // seqno: non-canonical
    raw.extend_from_slice(&[0]); // row count
    raw.extend_from_slice(&8u64.to_le_bytes()); // prefix hash
    raw.extend_from_slice(&9u64.to_le_bytes()); // tail-head hash
    raw.extend_from_slice(
        &mandate_delta::snapshot::bytes_hash(&{
            let mut b = b"MDL1".to_vec();
            b.extend_from_slice(&[0x80, 0x00, 0]);
            b.extend_from_slice(&8u64.to_le_bytes());
            b.extend_from_slice(&9u64.to_le_bytes());
            b
        })
        .to_le_bytes(),
    );
    match snapshot::decode_snapshot(&schema, &raw) {
        Err(snapshot::SnapshotError::Corrupt {
            reason: "non-canonical varint",
            ..
        }) => {}
        other => panic!("expected the atom refusal, got {other:?}"),
    }
}

/// The range refusal: compaction past the log's end is a typed error,
/// and NOTHING is written or cut (the atomicity's boundary).
#[test]
fn compact_range_refusal_writes_nothing() {
    let dir = temp_dir("range");
    let schema = fixture_schema();
    let log_path = dir.path().join("j.bin");
    let snap_path = snapshot::snapshot_path_for(&log_path);
    let mut log = DeltaLog::open(&log_path, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
    log.append(Delta::Insert(fixture_row(1, "a")))
        .unwrap_or_else(|e| panic!("{e}"));
    assert!(matches!(
        log.compact(5, &snap_path),
        Err(DeltaError::CompactRange { seqno: 5, len: 1 })
    ));
    assert!(!snap_path.exists(), "the refused compact wrote a snapshot");
    let file = std::fs::read(&log_path).unwrap_or_else(|e| panic!("read: {e}"));
    assert_eq!(log.len(), 1);
    drop(log);
    let log = DeltaLog::open(&log_path, schema).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(log.len(), 1, "the log file was never cut");
    let _ = file;
}

/// The plain-open face over a compacted store: `open` (no snapshot)
/// full-replays the tail-only log — the snapshot is an optimization,
/// never a dependency.
#[test]
fn plain_open_ignores_the_snapshot() {
    let dir = temp_dir("plain");
    let schema = fixture_schema();
    let ops = op_stream(31, 6);
    let log_path = dir.path().join("j.bin");
    let snap_path = snapshot::snapshot_path_for(&log_path);
    {
        let mut log = DeltaLog::open(&log_path, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
        for d in &ops {
            log.append(d.clone()).unwrap_or_else(|e| panic!("{e}"));
        }
        log.compact(4, &snap_path).unwrap_or_else(|e| panic!("{e}"));
    }
    let log = DeltaLog::open(&log_path, schema.clone()).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(log.len(), 2);
    // The plain open sees the TAIL alone (the snapshot file is a
    // sibling it never reads — this is WHY the host opens snapshotted;
    // the honest consequence of compaction, never a wrong state).
    assert_eq!(*log.state(), full_replay(&schema, &ops[4..]));
    assert!(log.recovery().is_none());
    assert_eq!(
        DeltaLog::open_snapshotted(&log_path, &snap_path, fixture_schema())
            .unwrap_or_else(|e| panic!("{e}"))
            .1,
        SnapshotReport::Applied { seqno: 4 }
    );
}

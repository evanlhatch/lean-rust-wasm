//! The crash-recovery DUEL (design-wave-30 A5): the Lean model's
//! crash-recovery ≡ the Rust recovery over the LCG-seeded crash
//! scenarios.
//!
//! THE SCENARIOS ARE SHARED: the Lean side (`SchemaTests.DeltaLog` —
//! `SchemaCore.DeltaLog`'s walk over `SchemaCore.Emit.Journal`'s codec
//! instantiation) pins each scenario cut's outcome as a value-level
//! theorem (`scenarioFaces_pin`, kernel-computed); THIS test replays
//! the SAME seed through the SAME recurrence (the tree's ONE LCG,
//! `TestingKit.lcg` — the constants below are its Knuth-64 pair) and
//! the REAL `DeltaLog` recovery must land on the SAME faces: the same
//! surviving frame counts, the same torn offsets, the same torn/clean
//! classification. A model/Rust skew fails HERE or there.
//!
//! THE MODEL FACE (`SchemaCore.DeltaLog`): the recovery = the LONGEST
//! VALID PREFIX of the written journal (the torn frame is not a
//! frame), the cut is REPORTED exactly when a frame straddles the
//! crash point (never silent, never phantom), the report's offset is
//! the torn frame's START (never past the crash), and the recovered
//! state is the recovered journal's replay (the log's invariant
//! restored — the recovered log stays appendable). Every property
//! below is one of the model's theorems, exercised through the real
//! implementation.

use mandate_delta::delta::{enc_delta, Delta};
use mandate_delta::error::DeltaError;
use mandate_delta::log::DeltaLog;
use mandate_delta::schema::fixtures::{fixture, fixture_row};
use mandate_delta::scratch::ScratchDir;
use mandate_delta::value::Value;

/// THE LCG (the tree's one recurrence — `TestingKit.lcg`, Knuth 64;
/// the same constants `tests/snapshot.rs` carries).
const LCG_MULT: u64 = 6364136223846793005;
const LCG_INC: u64 = 1442695040888963407;

fn lcg_next(state: &mut u64) -> u64 {
    *state = state.wrapping_mul(LCG_MULT).wrapping_add(LCG_INC);
    *state
}

/// THE SHARED SCENARIO GENERATOR (`SchemaTests.DeltaLog.drawDelta`):
/// one draw drives kind (`(r >> 8) % 3`: insert/update/remove) and key
/// (`r % 7`, the small window so updates/removes hit); the payload is
/// the FIXED row `[id = key, name = "row"]`.
fn op(r: u64) -> Delta {
    let id = r % 7;
    match (r >> 8) % 3 {
        0 => Delta::Insert(fixture_row(id, "row")),
        1 => Delta::Update(fixture_row(id, "row")),
        _ => Delta::Remove(Value::U64(id)),
    }
}

/// The op stream (`drawOps`): n draws from the seed.
fn op_stream(seed: u64, n: usize) -> Vec<Delta> {
    let mut st = seed;
    (0..n).map(|_| op(lcg_next(&mut st))).collect()
}

/// The scenario's journal: 12 ops at seed 0x5EED
/// (`SchemaTests.DeltaLog.scenarioOps`).
const SCENARIO_SEED: u64 = 0x5EED;
const SCENARIO_N: usize = 12;
const SCENARIO_CUTS: usize = 6;

/// THE DUEL'S EXPECTED FACES (`SchemaTests.DeltaLog.scenarioFaces_pin`,
/// kernel-computed on the Lean side): per scenario cut, in cut order —
/// (surviving frames, torn offset (0 = clean), torn?).
const SCENARIO_FACES: [(u64, u64, bool); SCENARIO_CUTS] = [
    (5, 30, true),
    (11, 62, true),
    (5, 30, true),
    (11, 62, true),
    (8, 51, true),
    (7, 44, true),
];

fn fixture_schema() -> mandate_delta::Schema {
    fixture()
}

/// A per-test temp dir (the shared scratch face).
fn temp_dir(tag: &str) -> ScratchDir {
    ScratchDir::new(&format!("mandate-delta-{tag}"))
        .unwrap_or_else(|e| panic!("tempdir: {e}"))
}

/// The scenario journal's bytes (the bare frame stream — the log's
/// durable wire, no count prefix; the same bytes the Lean model's
/// `logWire` computes through the landed codec).
fn journal_bytes(schema: &mandate_delta::Schema, ops: &[Delta]) -> Vec<u8> {
    let mut out = Vec::new();
    for d in ops {
        assert!(enc_delta(schema, d, &mut out), "scenario op must encode");
    }
    out
}

/// THE DUEL: every LCG-seeded crash scenario's REAL recovery lands on
/// the Lean model's pinned face — the surviving frames, the torn
/// offset, the torn/clean classification — and every model law holds
/// through the implementation (the prefix replay, the report's
/// honesty, the post-recovery appendability).
#[test]
fn crash_duel_faces() {
    let dir = temp_dir("duel");
    let schema = fixture_schema();
    let ops = op_stream(SCENARIO_SEED, SCENARIO_N);
    assert_eq!(ops.len(), 12, "the scenario is real (Lean pin: 12 ops)");
    let bytes = journal_bytes(&schema, &ops);
    assert!(!bytes.is_empty(), "the scenario wire is nonempty");

    // The cut stream (`drawCuts`): the LCG state resumes after the ops.
    let mut st = SCENARIO_SEED;
    for _ in 0..SCENARIO_N {
        lcg_next(&mut st);
    }
    let l = bytes.len() as u64;
    let cuts: Vec<u64> = (0..SCENARIO_CUTS)
        .map(|_| lcg_next(&mut st) % (l + 1))
        .collect();

    let tmp = dir.path().join("cut.bin");
    let mut torn_any = false;
    for (i, &cut) in cuts.iter().enumerate() {
        let (want_frames, want_offset, want_torn) = SCENARIO_FACES[i];
        std::fs::write(&tmp, &bytes[..cut as usize])
            .unwrap_or_else(|e| panic!("cut {cut}: write: {e}"));
        // The recovering open SUCCEEDS on every cut (the model's openAt
        // is total over the torn-write shapes).
        let mut log = DeltaLog::open(&tmp, schema.clone())
            .unwrap_or_else(|e| panic!("cut {cut}: open: {e}"));
        assert_eq!(
            log.len(),
            want_frames,
            "cut {cut}: surviving frames ≠ the model's face"
        );
        // The recovered entries are exactly the prefix (the model's
        // prefix law).
        let got = log.entries().to_vec();
        assert_eq!(
            got,
            ops[..want_frames as usize].to_vec(),
            "cut {cut}: recovered entries ≠ the longest valid prefix"
        );
        // The recovered state is the prefix's replay (the model's
        // state law): state == state_at(frames).
        assert_eq!(
            *log.state(),
            log.state_at(want_frames),
            "cut {cut}: state ≠ the prefix replay"
        );
        // The report fires EXACTLY when the face says torn — never
        // silent, never phantom — and names the model's offset.
        match (want_torn, log.recovery()) {
            (true, Some(rec)) => {
                torn_any = true;
                assert_eq!(
                    rec.frames, want_frames,
                    "cut {cut}: report's frame count ≠ the model's"
                );
                assert_eq!(
                    rec.offset, want_offset,
                    "cut {cut}: report's offset ≠ the model's (the torn frame's start)"
                );
                assert!(
                    rec.offset <= cut,
                    "cut {cut}: the report claims a cut PAST the crash point"
                );
            }
            (false, None) => {}
            (true, None) => panic!("cut {cut}: the model says torn — the cut was SILENT"),
            (false, Some(rec)) => panic!(
                "cut {cut}: PHANTOM report at {} — the model says clean",
                rec.offset
            ),
        }
        // The recovered log stays appendable, and the append survives
        // a reopen (the model's invariant-restored law).
        let before = log.len();
        log.append(Delta::Insert(fixture_row(999, "post-recovery")))
            .unwrap_or_else(|e| panic!("cut {cut}: post-recovery append: {e}"));
        drop(log);
        let log = DeltaLog::open(&tmp, schema.clone())
            .unwrap_or_else(|e| panic!("cut {cut}: re-reopen: {e}"));
        assert_eq!(log.len(), before + 1, "cut {cut}: post-recovery append lost");
        assert_eq!(
            log.entry(before),
            Some(&Delta::Insert(fixture_row(999, "post-recovery")))
        );
    }
    assert!(torn_any, "vacuous duel: no scenario cut ever tore a frame");
}

/// THE MODEL'S SNAPSHOT DISCIPLINE, exercised (the fallback face): a
/// TORN snapshot never loads — the full log replay takes over and the
/// fallback is REPORTED; torn LOG tail and torn snapshot surface BOTH
/// reports. (The byte-level alignment rules are the codec's; this is
/// the model's outcome algebra — `SnapOutcome::fellBack` — at the
/// runtime face.)
#[test]
fn snapshot_fallback_reports_and_replays_the_log() {
    use mandate_delta::snapshot::SnapshotReport;

    let dir = temp_dir("duel-snap");
    let schema = fixture_schema();
    let ops = op_stream(SCENARIO_SEED, SCENARIO_N);
    let log_path = dir.path().join("journal.bin");
    let snap_path = mandate_delta::snapshot::snapshot_path_for(&log_path);
    {
        let mut log = DeltaLog::open(&log_path, schema.clone())
            .unwrap_or_else(|e| panic!("open: {e}"));
        for d in &ops {
            log.append(d.clone()).unwrap_or_else(|e| panic!("append: {e}"));
        }
        log.compact(6, &snap_path)
            .unwrap_or_else(|e| panic!("compact: {e}"));
    }
    let snap_bytes =
        std::fs::read(&snap_path).unwrap_or_else(|e| panic!("read snap: {e}"));
    assert!(!snap_bytes.is_empty());

    // TORN SNAPSHOT: cut the snapshot mid-file — the open falls back to
    // the FULL log replay and REPORTS the torn reason (never silent,
    // never the snapshot's state through a fallback).
    let torn_snap = dir.path().join("torn-snap.bin");
    std::fs::write(&torn_snap, &snap_bytes[..snap_bytes.len() / 2])
        .unwrap_or_else(|e| panic!("write torn snap: {e}"));
    let torn_log = dir.path().join("torn-snap-journal.bin");
    std::fs::copy(&log_path, &torn_log).unwrap_or_else(|e| panic!("copy: {e}"));
    let (log, report) = DeltaLog::open_snapshotted(&torn_log, &torn_snap, schema.clone())
        .unwrap_or_else(|e| panic!("open with torn snapshot must fall back, not fail: {e}"));
    match report {
        SnapshotReport::FellBack(_) => {} // the reason is REPORTED, as data
        other => panic!("torn snapshot must fall back REPORTED, got {other:?}"),
    }
    // The fallback's state is the LOG's own replay — the log AS IT IS
    // on disk (post-compaction: the tail alone; the model's fallback
    // law names the LOG's replay, never the snapshot's state).
    let mut expect = mandate_delta::delta::Table::new();
    for d in &ops[6..] {
        expect.apply(&schema, d);
    }
    assert_eq!(*log.state(), expect, "a fallback's state is the LOG's replay");

    // TORN BOTH: a torn log tail BESIDE the torn snapshot — the open
    // surfaces BOTH reports (the snapshot's fallback AND the log's
    // recovery), and the state is still the log's honest prefix replay.
    let both_log = dir.path().join("torn-both-journal.bin");
    let full = std::fs::read(&log_path).unwrap_or_else(|e| panic!("read log: {e}"));
    std::fs::write(&both_log, &full[..full.len() - 1])
        .unwrap_or_else(|e| panic!("write torn log: {e}"));
    let (log, report) = DeltaLog::open_snapshotted(&both_log, &torn_snap, schema.clone())
        .unwrap_or_else(|e| panic!("open torn-both: {e}"));
    assert!(
        matches!(report, SnapshotReport::FellBack(_)),
        "torn-both: the snapshot's fallback must be reported, got {report:?}"
    );
    let rec = log
        .recovery()
        .unwrap_or_else(|| panic!("torn-both: the log's torn-tail cut was SILENT"));
    assert!(rec.frames < ops.len() as u64, "torn-both: the torn frame survived?");
    // The state is the SURVIVING prefix's replay — the log AS IT IS on
    // disk (post-compaction: frames ops[6..], so rec.frames counts
    // THOSE; the model's prefix law, at the snapshot open).
    let mut expect_prefix = mandate_delta::delta::Table::new();
    for d in &ops[6..6 + rec.frames as usize] {
        expect_prefix.apply(&schema, d);
    }
    assert_eq!(
        *log.state(),
        expect_prefix,
        "torn-both: state ≠ the surviving prefix's replay"
    );
}

/// THE STRICT REFUSAL, model-tied: the model's torn classification is
/// the strict open's typed error — the same faces, the refusal's
/// offset is the model's (the torn frame's start, never past the
/// crash point).
#[test]
fn strict_refusal_offsets_match_the_model() {
    let dir = temp_dir("duel-strict");
    let schema = fixture_schema();
    let ops = op_stream(SCENARIO_SEED, SCENARIO_N);
    let bytes = journal_bytes(&schema, &ops);
    let mut st = SCENARIO_SEED;
    for _ in 0..SCENARIO_N {
        lcg_next(&mut st);
    }
    let l = bytes.len() as u64;
    let tmp = dir.path().join("cut.bin");
    let mut refused_any = false;
    for (i, _) in (0..SCENARIO_CUTS).enumerate() {
        let cut = lcg_next(&mut st) % (l + 1);
        let (want_frames, want_offset, want_torn) = SCENARIO_FACES[i];
        std::fs::write(&tmp, &bytes[..cut as usize])
            .unwrap_or_else(|e| panic!("cut {cut}: write: {e}"));
        match DeltaLog::open_strict(&tmp, schema.clone()) {
            Err(DeltaError::TornTail { offset }) => {
                refused_any = true;
                assert!(want_torn, "cut {cut}: the model says clean — the strict refusal is a PHANTOM");
                assert_eq!(
                    offset, want_offset,
                    "cut {cut}: the refusal's offset ≠ the model's torn-frame start"
                );
                assert!(offset <= cut, "cut {cut}: refusal past the crash point");
                // And the recovering open over the SAME bytes lands on
                // the model's face — the two policies agree with the
                // model exactly.
                let log = DeltaLog::open(&tmp, schema.clone())
                    .unwrap_or_else(|e| panic!("cut {cut}: recover: {e}"));
                assert_eq!(log.len(), want_frames, "cut {cut}: policy skew");
            }
            Err(e) => panic!("cut {cut}: unexpected error {e}"),
            Ok(log) => {
                assert!(!want_torn, "cut {cut}: the model says torn — the strict open passed it");
                assert_eq!(log.len(), want_frames, "cut {cut}: boundary-cut frames ≠ the model's");
                assert!(log.recovery().is_none(), "cut {cut}: phantom recovery report");
            }
        }
    }
    assert!(refused_any, "vacuous: no scenario cut ever tore a frame");
}


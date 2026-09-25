//! The append/replay round trips over the durable backend: the log is
//! exactly its frames; a reopen restores the entries, the witnesses,
//! and the state; the whole-log wire round-trips byte-identically.

use mandate_delta::delta::{Delta, Table};
use mandate_delta::log::{DeltaLog, MemBackend, TailPolicy};
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

/// The replay law at log scale: the state after entries 0..n is the
/// fold of the deltas — the SAME fold a fresh replay performs (the
/// open's decode-and-apply IS the replay; the state_at faces agree).
#[test]
fn append_replay_state_faces_agree() {
    let schema = fixture_schema();
    let mut log = DeltaLog::open_with(MemBackend::new(), schema.clone(), TailPolicy::Recover)
        .unwrap_or_else(|e| panic!("open: {e}"));
    let deltas = vec![
        Delta::Insert(fixture_row(1, "a")),
        Delta::Insert(fixture_row(2, "b")),
        Delta::Update(fixture_row(1, "a2")),
        Delta::Remove(Value::U64(2)),
    ];
    for (i, d) in deltas.iter().enumerate() {
        let seq = log.append(d.clone()).unwrap_or_else(|e| panic!("append {i}: {e}"));
        assert_eq!(seq, i as u64);
    }
    assert_eq!(log.len(), 4);
    assert_eq!(log.state().rows(), &[fixture_row(1, "a2")]);
    for k in 0..=4u64 {
        // state_at(k) = the prefix replay — equals the state a log of
        // the first k entries presents.
        let mut prefix = Table::new();
        for d in &deltas[..k as usize] {
            prefix.apply(&schema, d);
        }
        assert_eq!(log.state_at(k), prefix, "state_at({k}) diverged");
    }
    // The entries survive verbatim.
    assert_eq!(log.entries(), &deltas);
}

/// The whole-log wire round-trips byte-identically, and a from-wire log
/// re-derives the same entries + state + witnesses.
#[test]
fn journal_wire_round_trip() {
    let schema = fixture_schema();
    let mut log = DeltaLog::open_with(MemBackend::new(), schema.clone(), TailPolicy::Recover)
        .unwrap_or_else(|e| panic!("open: {e}"));
    log.append(Delta::Insert(fixture_row(1, "a"))).unwrap_or_else(|e| panic!("{e}"));
    log.append(Delta::Update(fixture_row(1, "b"))).unwrap_or_else(|e| panic!("{e}"));
    log.append(Delta::Remove(Value::U64(1))).unwrap_or_else(|e| panic!("{e}"));

    let wire = log.journal_bytes();
    let from_wire = DeltaLog::from_journal_bytes(schema.clone(), &wire)
        .unwrap_or_else(|e| panic!("from_journal_bytes: {e}"));
    assert_eq!(from_wire.entries(), log.entries());
    assert_eq!(from_wire.state(), log.state());
    // Witnesses re-derive identically (the inversion's data).
    for seq in 0..log.len() {
        assert_eq!(from_wire.witness(seq), log.witness(seq), "witness {seq} diverged");
    }
    // Re-encoding the decoded journal is byte-identical (both
    // directions of the wire).
    assert_eq!(from_wire.journal_bytes(), wire);
    // An empty log's wire is exactly the varint 0 (the Lean encList
    // shape).
    let empty = DeltaLog::open_with(MemBackend::new(), schema, TailPolicy::Recover)
        .unwrap_or_else(|e| panic!("open: {e}"));
    assert_eq!(empty.journal_bytes(), vec![0]);
}

/// MemBackend byte-level reopen: a log over the SAME backend bytes
/// decodes to the same log (the frames are the artifact).
#[test]
fn frames_reopen_identically() {
    let schema = fixture_schema();
    let mut backend = MemBackend::new();
    {
        let mut log =
            DeltaLog::open_with(&mut backend, schema.clone(), TailPolicy::Recover)
                .unwrap_or_else(|e| panic!("open: {e}"));
        log.append(Delta::Insert(fixture_row(7, "x"))).unwrap_or_else(|e| panic!("{e}"));
        log.append(Delta::Remove(Value::U64(7))).unwrap_or_else(|e| panic!("{e}"));
    }
    // Reopen over the same bytes.
    let reopened =
        DeltaLog::open_with(&mut backend, schema, TailPolicy::Recover)
            .unwrap_or_else(|e| panic!("reopen: {e}"));
    assert_eq!(reopened.len(), 2);
    assert_eq!(reopened.entry(0), Some(&Delta::Insert(fixture_row(7, "x"))));
    assert_eq!(reopened.entry(1), Some(&Delta::Remove(Value::U64(7))));
    assert!(reopened.state().rows().is_empty());
    assert!(reopened.recovery().is_none(), "a clean journal reports no recovery");
}

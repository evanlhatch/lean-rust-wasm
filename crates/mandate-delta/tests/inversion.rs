//! The inversion at log scale: the witnessed journal's round trip
//! (`witnessedApply_reverse_inv`'s law), the validity threading, and
//! the negative controls (a lying witness refuses — in the log's own
//! rewind face too).

use mandate_delta::delta::{invert_w, valid_wb, witnessed_apply, witness_of, Delta, WDelta};
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

/// THE ROUND TRIP at log scale: after `rewind_to(k)`, the state is
/// exactly `state_at(k)` — the inverse journal (reverse + old/new
/// swap) through the CHECKED patches undoes the journal. Every witness
/// recorded along the way was valid when taken (`witnessOf_valid`).
#[test]
fn rewind_to_every_prefix() {
    let schema = fixture_schema();
    let mut log = DeltaLog::open_with(MemBackend::new(), schema, TailPolicy::Recover)
        .unwrap_or_else(|e| panic!("open: {e}"));
    let deltas = vec![
        Delta::Insert(fixture_row(1, "a")),
        Delta::Insert(fixture_row(2, "b")),
        Delta::Update(fixture_row(1, "a2")),
        Delta::Insert(fixture_row(3, "c")),
        Delta::Remove(Value::U64(2)),
        Delta::Remove(Value::U64(99)), // the absent-key no-op
    ];
    for d in deltas {
        log.append(d).unwrap_or_else(|e| panic!("append: {e}"));
    }
    // Every recorded witness validates against the state that produced
    // it (checked at append time; re-checked here against the state
    // BEFORE the entry — reconstruct the prefixes).
    for seq in 0..=log.len() {
        let state_before = log.state_at(seq);
        if let Some(w) = log.witness(seq) {
            assert!(valid_wb(&state_before, w), "witness {seq} invalid");
        }
    }
    // Rewind to EVERY prefix; the result is the prefix replay, and the
    // log's frames are untouched (append-only is literal).
    for k in 0..=log.len() {
        log.rewind_to(k).unwrap_or_else(|e| panic!("rewind_to({k}): {e}"));
        assert_eq!(*log.state(), log.state_at(k), "rewind_to({k}) diverged");
        assert_eq!(log.len(), 6, "rewind_to({k}) touched the log");
    }
}

/// The checked-patch refusal surfaces in the log's own rewind face: a
/// witness that does not check is the typed refusal, never a silently
/// wrong state.
#[test]
fn rewind_refuses_a_skewed_witness() {
    let schema = fixture_schema();
    let mut log = DeltaLog::open_with(MemBackend::new(), schema, TailPolicy::Recover)
        .unwrap_or_else(|e| panic!("open: {e}"));
    log.append(Delta::Insert(fixture_row(1, "a"))).unwrap_or_else(|e| panic!("{e}"));
    // Skew the recorded witness (simulate internal-state skew): the
    // recorded old row must be the absent marker for this insert.
    log.witnesses_mut()[0] = WDelta {
        idx: 0,
        old: Some(fixture_row(1, "a")), // a LIE: the key was absent
        new: Some(fixture_row(1, "a")),
    };
    // The rewind's checked patches REFUSE (the delta does not lie).
    assert!(log.rewind_to(0).is_err(), "a lying witness must refuse the rewind");
}

/// The inversion's four cases at the witnessed-delta level, composed
/// into a journal: witnessed_apply of the inverse journal restores the
/// pre-journal state exactly (`witnessedApply_reverse_inv`).
#[test]
fn inverse_journal_round_trip() {
    let schema = fixture_schema();
    let start = {
        let mut t = mandate_delta::delta::Table::new();
        t.apply(&schema, &Delta::Insert(fixture_row(7, "seed")));
        t
    };
    let journal = vec![
        Delta::Insert(fixture_row(1, "a")),
        Delta::Update(fixture_row(7, "seed2")),
        Delta::Remove(Value::U64(7)),
        Delta::Remove(Value::U64(42)), // the no-op
    ];
    // Replay, witnessing along the way.
    let mut state = start.clone();
    let mut witnesses = Vec::new();
    for d in &journal {
        let w = witness_of(&schema, d, &state);
        state = witnessed_apply(&state, std::slice::from_ref(&w)).unwrap_or_else(|| panic!("witness"));
        witnesses.push(w);
    }
    // The inverse journal: reverse + old/new swap — applied through the
    // CHECKED patches, it restores the start exactly.
    let inverse: Vec<WDelta> = witnesses.iter().rev().map(invert_w).collect();
    let restored = witnessed_apply(&state, &inverse).unwrap_or_else(|| panic!("inverse"));
    assert_eq!(restored, start);
    // The frames' byte-identity is untouched by all this (the inversion
    // is in-memory; the log format stays the Lean journal codec's).
    let mut wire_a = Vec::new();
    mandate_delta::delta::enc_journal(&schema, &journal, &mut wire_a);
    let decoded = {
        let mut rest: &[u8] = &wire_a;
        mandate_delta::delta::dec_journal(&schema, &mut rest).unwrap_or_else(|e| panic!("{e:?}"))
    };
    assert_eq!(decoded, journal);
}

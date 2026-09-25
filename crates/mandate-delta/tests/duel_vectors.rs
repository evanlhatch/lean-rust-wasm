//! The differential: Kit.Duel's consumer contract over the journal/duel
//! vector set (tests/duel/ — manifest + vectors).
//!
//! THE CONTRACT (kit/Kit/Duel.lean's consumer-side contract): read the
//! manifest, skip the 2-line header and the `generator` provenance row,
//! split each row on the tab. A `decode <note>` row names a vector that
//! MUST decode — the decoded value re-encodes byte-identically (the
//! differential's BOTH directions). A `refuse` row names a vector that
//! MUST be refused — a typed error, never a panic, never a silent
//! misparse.
//!
//! THE VECTORS ARE LEAN-EMITTED (the integration step LANDED): the
//! journal duel emitter `SchemaCore.Emit.Journal` computes every byte
//! through the LANDED journal codec (`SchemaCore.Event.encDelta`/
//! `encJournal` over this crate's documented `encR`/`encK`
//! instantiation — `encList`'s row shape + `encKey` verbatim), commits
//! them through the byte-tie (`gates gen-check`'s text + binary lanes,
//! the `.hdr` sidecars naming the byte hashes), and names itself in the
//! manifest's `generator` row. The crate's byte-exactness is
//! mechanically enforced against the Lean kernel's own encodings — the
//! hand-composed fixture era is over; a wire drift fails THIS test, and
//! a generator drift fails the gate.

use mandate_delta::delta::{dec_delta, dec_journal, enc_delta, enc_journal, Delta};
use mandate_delta::schema::{Field, Row, Schema};
use mandate_delta::value::{Ty, Value};

/// The duel manifest, compile-time pinned to the committed artifact.
const MANIFEST: &str = include_str!("duel/manifest.txt");

/// The manifest's repo-root prefix (the rows are repo-root-relative;
/// the test binary's cwd is the crate root).
const CRATE_PREFIX: &str = "crates/mandate-delta/";

/// The fixture schema (the slice's shape): id:u64 keyed, name:string.
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

/// One parsed manifest row: the vector path + the decode note (None =
/// the row expects a typed refusal).
struct Row_ {
    path: String,
    note: Option<String>,
}

/// Kit.Duel's consumer contract: skip the 2-line header and the
/// `generator` provenance row, split each row on the tab.
fn manifest_rows() -> Vec<Row_> {
    MANIFEST
        .lines()
        .skip(2)
        .filter(|line| !line.is_empty() && !line.starts_with("generator\t"))
        .map(|line| {
            let mut parts = line.split('\t');
            let path = parts.next().expect("manifest row: path").to_string();
            let expect = parts.next().expect("manifest row: expectation");
            Row_ { path, note: expect.strip_prefix("decode ").map(str::to_string) }
        })
        .collect()
}

/// Re-base a manifest row's repo-root-relative path to the crate root.
fn crate_path(row_path: &str) -> &str {
    match row_path.strip_prefix(CRATE_PREFIX) {
        Some(p) => p,
        None => row_path,
    }
}

/// The pinned frame from the note (the note IS the value-level pin — a
/// drift from the bytes fails the test loudly).
fn pinned_frame(kind: &str, note: &str) -> Delta {
    match kind {
        "frame-insert" => {
            assert_eq!(note, "id=300 name=hi", "note drift");
            Delta::Insert(fixture_row(300, "hi"))
        }
        "frame-update" => {
            assert_eq!(note, "id=300 name=hi", "note drift");
            Delta::Update(fixture_row(300, "hi"))
        }
        "frame-remove" => {
            assert_eq!(note, "id=300", "note drift");
            Delta::Remove(Value::U64(300))
        }
        other => panic!("unknown frame kind {other}: {note}"),
    }
}

/// The pinned journal from the note: `a|b|c` segments, each
/// `op:key:name` or `op:key`.
fn pinned_journal(note: &str) -> Vec<Delta> {
    note.split('|')
        .map(|seg| {
            let parts: Vec<&str> = seg.splitn(3, ':').collect();
            let id: u64 = parts[1].parse().expect("pinned key");
            match parts[0] {
                "insert" => Delta::Insert(fixture_row(id, parts[2])),
                "update" => Delta::Update(fixture_row(id, parts[2])),
                "remove" => Delta::Remove(Value::U64(id)),
                other => panic!("unknown journal op {other}"),
            }
        })
        .collect()
}

/// THE DUEL: every manifest row's expectation holds.
#[test]
fn duel_rows() {
    let schema = fixture_schema();
    let mut rows_checked = 0;
    for row in manifest_rows() {
        let bytes = std::fs::read(crate_path(&row.path))
            .unwrap_or_else(|e| panic!("{}: read: {e}", row.path));
        match &row.note {
            None => {
                // MUST be refused — a typed error, never a panic.
                let mut rest: &[u8] = &bytes;
                let frame_err = dec_delta(&schema, &mut rest).err();
                let journal_err = dec_journal(&schema, &mut rest).err();
                assert!(
                    frame_err.is_some() || journal_err.is_some(),
                    "{}: vector decoded but must refuse",
                    row.path
                );
            }
            Some(note) => {
                let (kind, value_note) =
                    note.split_once(' ').unwrap_or((note, ""));
                match kind {
                    "journal-empty" => {
                        assert_eq!(value_note, "", "note drift");
                        let mut rest: &[u8] = &bytes;
                        let journal =
                            dec_journal(&schema, &mut rest).unwrap_or_else(|e| {
                                panic!("{}: {e:?}", row.path)
                            });
                        assert!(journal.is_empty(), "{}: expected the empty journal", row.path);
                        assert!(rest.is_empty(), "{}: journal wire must fully consume", row.path);
                        // Both directions: re-encode byte-identically.
                        let mut re = Vec::new();
                        enc_journal(&schema, &journal, &mut re);
                        assert_eq!(re, bytes, "{}: re-encode diverged", row.path);
                    }
                    "journal" => {
                        let mut rest: &[u8] = &bytes;
                        let journal =
                            dec_journal(&schema, &mut rest).unwrap_or_else(|e| {
                                panic!("{}: {e:?}", row.path)
                            });
                        assert!(rest.is_empty(), "{}: journal wire must fully consume", row.path);
                        assert_eq!(journal, pinned_journal(value_note), "{}: value pin", row.path);
                        // Both directions: re-encode byte-identically.
                        let mut re = Vec::new();
                        enc_journal(&schema, &journal, &mut re);
                        assert_eq!(re, bytes, "{}: re-encode diverged", row.path);
                        // The replay pins: insert 300:hi, update 300:ho,
                        // remove 300 — the final state is EMPTY and the
                        // one-entry prefix holds the inserted row.
                        let mut state = mandate_delta::delta::Table::new();
                        for d in &journal {
                            state.apply(&schema, d);
                        }
                        assert!(state.rows().is_empty(), "{}: replay pin", row.path);
                    }
                    _ => {
                        let mut rest: &[u8] = &bytes;
                        let decoded =
                            dec_delta(&schema, &mut rest).unwrap_or_else(|e| {
                                panic!("{}: {e:?}", row.path)
                            });
                        assert_eq!(decoded, pinned_frame(kind, value_note), "{}: value pin", row.path);
                        assert!(rest.is_empty(), "{}: frame must fully consume", row.path);
                        // Both directions: re-encode byte-identically.
                        let mut re = Vec::new();
                        assert!(enc_delta(&schema, &decoded, &mut re));
                        assert_eq!(re, bytes, "{}: re-encode diverged", row.path);
                    }
                }
            }
        }
        rows_checked += 1;
    }
    assert!(rows_checked >= 9, "vacuous duel: {rows_checked} rows");
}

/// The atom pins, at the duel's own level: the bytes the Lean side's
/// kernel reductions emit (`SchemaCore.Codec`'s known-answer pins) are
/// exactly the bytes the Rust port emits — inside the pinned frames'
/// payloads.
#[test]
fn lean_atom_pins_inside_frames() {
    let schema = fixture_schema();
    // u64 300 = [0xAC, 0x02]; "hi" = [2, 104, 105] — Codec.lean's pins.
    let mut out = Vec::new();
    assert!(enc_delta(&schema, &Delta::Insert(fixture_row(300, "hi")), &mut out));
    assert_eq!(out, vec![0x00, 2, 0xAC, 0x02, 2, 104, 105]);
    // i64 pins ride the row positions' type (not in this fixture's
    // schema; the atom-level pins live in value.rs's known-answer test).
}

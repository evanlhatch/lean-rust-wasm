//! The delta variant, its frame codec, the keyed-table semantics, and
//! the witnessed inversion — the byte-exact port of `SchemaCore.Event`'s
//! delta frames + `SchemaCore.Delta`'s semantics and inversion.
//!
//! THE FRAME (Event.lean's `encDelta`/`decDelta?` — the tag byte in
//! CTOR ORDER, reordering is a WIRE-BREAKING change):
//!
//! ```text
//! frame := tag_byte ++ payload
//!   0 ++ enc_row(row)    -- insert (full record, v1 full replacement)
//!   1 ++ enc_row(row)    -- update (full record, v1 full replacement)
//!   2 ++ enc_key(key)    -- remove (the key field's value only)
//! ```
//!
//! Frames are SELF-DELIMITING and APPEND-FORM (`dec_delta` returns the
//! delta AND the unconsumed suffix — the append-form law's shape), so a
//! log is a decodable frame stream and the whole-log wire is exactly
//! `encJournal`: varint count + the frames.
//!
//! THE SEMANTICS (`SchemaCore.deltaApply` on the keyed table): insert/
//! update are keyed UPSERT (replace the FIRST key-matching row, else
//! append); remove erases the FIRST key-matching row. Total — the
//! Option totality lives in the CHECKED carriers below.
//!
//! THE INVERSION (`SchemaCore.Delta`'s witnessed shape): the witness
//! records the position + the OLD row + the NEW row (`WDelta`); the
//! inverse swaps old and new (`invertW`); the patch is CHECKED — a
//! lying witness refuses (`patchW?`: the delta does not lie), which is
//! what makes the round trip (`witnessedApply_reverse_inv`'s law)
//! hold unconditionally.

use crate::error::DecodeFail;
use crate::schema::{dec_key, dec_row, enc_key, enc_row, Row, Schema};
use crate::value::{enc_varint, Value};

/// The delta variant (`SchemaCore.RowDelta`: the accepted net change —
/// never a command, never an event).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Delta {
    /// Insert the full record (keyed upsert).
    Insert(Row),
    /// Update the full record (v1 full replacement — keyed upsert).
    Update(Row),
    /// Remove the row at the key.
    Remove(Value),
}

impl Delta {
    /// The wire tag (Event.lean's ctor order: 0/1/2).
    #[must_use]
    pub fn tag(&self) -> u8 {
        match self {
            Self::Insert(_) => 0,
            Self::Update(_) => 1,
            Self::Remove(_) => 2,
        }
    }
}

/// THE FRAME ENCODER (`encDelta`): the tag byte + the self-delimiting
/// payload. Every byte is the Lean codec's emission.
pub fn enc_delta(schema: &Schema, d: &Delta, out: &mut Vec<u8>) -> bool {
    match d {
        Delta::Insert(r) | Delta::Update(r) => {
            out.push(d.tag());
            enc_row(r, out);
            true
        }
        Delta::Remove(k) => {
            out.push(d.tag());
            enc_key(schema, k, out)
        }
    }
}

/// THE FRAME DECODER (`decDelta?`): the tag byte dispatches; unknown
/// tags refuse; truncation and corruption are CLASSIFIED (the log's
/// recovery discipline dispatches on exactly this). Append-form: the
/// unconsumed suffix rides in `bs` on success.
///
/// # Errors
/// `Truncated` (input exhausted mid-frame) or `Corrupt` (complete
/// input, invalid bytes).
pub fn dec_delta(schema: &Schema, bs: &mut &[u8]) -> Result<Delta, DecodeFail> {
    if bs.is_empty() {
        return Err(DecodeFail::Truncated);
    }
    let tag = bs[0];
    *bs = &bs[1..];
    match tag {
        0 | 1 => {
            let row = dec_row(schema, bs)?;
            Ok(if tag == 0 { Delta::Insert(row) } else { Delta::Update(row) })
        }
        2 => {
            let k = dec_key(schema, bs)?;
            Ok(Delta::Remove(k))
        }
        _ => Err(DecodeFail::Corrupt("unknown delta tag")),
    }
}

/// The whole-log wire ENCODER (`encJournal`): varint count + the frames
/// in occurrence order.
pub fn enc_journal(schema: &Schema, log: &[Delta], out: &mut Vec<u8>) {
    enc_varint(log.len() as u64, out);
    for d in log {
        // Rows are schema-checked at construction, so a frame cannot
        // fail to encode here; a false return is unreachable by
        // construction (Remove keys are schema-typed at decode/build).
        let before = out.len();
        if !enc_delta(schema, d, out) {
            out.truncate(before);
            debug_assert!(false, "schema-checked delta failed to encode");
        }
    }
}

/// The whole-log wire DECODER (`decJournal?`): varint count, then that
/// many frames; truncation refuses (the frame decoder's classes
/// propagate). Append-form at the JOURNAL level too: the unconsumed
/// suffix rides out in `bs`.
///
/// # Errors
/// The frame decoder's classes (truncated / corrupt).
pub fn dec_journal(schema: &Schema, bs: &mut &[u8]) -> Result<Vec<Delta>, DecodeFail> {
    let n = crate::value::dec_varint(bs)?;
    let mut log = Vec::new();
    for _ in 0..n {
        log.push(dec_delta(schema, bs)?);
    }
    Ok(log)
}

/// The keyed table: the rows in insertion order (the `List (RowVals fs)`
/// state — first-match semantics are POSITIONAL, so the order is data).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Table {
    rows: Vec<Row>,
}

impl Table {
    /// The empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The rows, in table order.
    #[must_use]
    pub fn rows(&self) -> &[Row] {
        &self.rows
    }

    /// The row at the key, if present (the FIRST key match).
    #[must_use]
    pub fn get(&self, schema: &Schema, k: &Value) -> Option<&Row> {
        self.rows.iter().find(|r| schema.same_key_img(r, k))
    }

    /// One delta's application (`SchemaCore.deltaApply`) — total:
    /// insert/update ARE upsert, remove erases.
    pub fn apply(&mut self, schema: &Schema, d: &Delta) {
        match d {
            Delta::Insert(r) | Delta::Update(r) => self.keyed_upsert(schema, r.clone()),
            Delta::Remove(k) => self.keyed_erase(schema, k),
        }
    }

    /// `SchemaCore.keyedUpsert`: replace the FIRST key-matching row,
    /// else append.
    pub fn keyed_upsert(&mut self, schema: &Schema, r: Row) {
        match self.rows.iter().position(|row| schema.same_key(row, &r)) {
            Some(i) => self.rows[i] = r,
            None => self.rows.push(r),
        }
    }

    /// `SchemaCore.keyedErase`: drop the FIRST key-matching row.
    pub fn keyed_erase(&mut self, schema: &Schema, k: &Value) {
        if let Some(i) = self.rows.iter().position(|row| schema.same_key_img(row, k)) {
            self.rows.remove(i);
        }
    }
}

/// THE WITNESSED DELTA (`SchemaCore.WDelta`): the position, the OLD row
/// (`None` = the key was absent), the NEW row (`None` = the row is
/// gone). The old row is what makes the inverse LAWFUL.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WDelta {
    /// The position (the first key match, or the append position).
    pub idx: usize,
    /// The recorded pre-image.
    pub old: Option<Row>,
    /// The recorded post-image.
    pub new: Option<Row>,
}

/// THE WITNESS (`SchemaCore.witnessOf`): the delta a change produces at
/// a state — what the journal records per occurrence. The position
/// accumulator rides the walk (the legacy `findIdx` restructured as
/// data — `witnessUpsert`/`witnessErase`).
#[must_use]
pub fn witness_of(schema: &Schema, d: &Delta, rows: &Table) -> WDelta {
    match d {
        Delta::Insert(r) | Delta::Update(r) => {
            witness_upsert(schema, r, rows, 0)
        }
        Delta::Remove(k) => witness_erase(schema, k, rows, 0),
    }
}

fn witness_upsert(schema: &Schema, r: &Row, rows: &Table, base: usize) -> WDelta {
    match rows.rows().iter().enumerate().find(|(_, row)| schema.same_key(row, r)) {
        Some((i, row)) => WDelta { idx: base + i, old: Some(row.clone()), new: Some(r.clone()) },
        None => WDelta { idx: base + rows.rows().len(), old: None, new: Some(r.clone()) },
    }
}

fn witness_erase(schema: &Schema, k: &Value, rows: &Table, base: usize) -> WDelta {
    match rows.rows().iter().enumerate().find(|(_, row)| schema.same_key_img(row, k)) {
        Some((i, row)) => WDelta { idx: base + i, old: Some(row.clone()), new: None },
        None => WDelta { idx: base, old: None, new: None },
    }
}

/// INVERSION (`SchemaCore.invertW`): swap old and new — rollback = the
/// canon's undo row.
#[must_use]
pub fn invert_w(d: &WDelta) -> WDelta {
    WDelta { idx: d.idx, old: d.new.clone(), new: d.old.clone() }
}

/// THE PATCH (`SchemaCore.patchW`): positional replace / erase /
/// insert, matched on the witness directly. Lean-total (out-of-bounds
/// faces mirror `List.set`/`List.eraseIdx`/`List.insertIdx` exactly).
#[must_use]
pub fn patch_w(rows: &Table, d: &WDelta) -> Table {
    let mut out = rows.clone();
    match (&d.old, &d.new) {
        (Some(_), Some(n)) => {
            if d.idx < out.rows.len() {
                out.rows[d.idx] = n.clone();
            }
        }
        (Some(_), None) => {
            if d.idx < out.rows.len() {
                out.rows.remove(d.idx);
            }
        }
        (None, Some(n)) => {
            // `List.insertIdx`: past the end appends at the end.
            let i = d.idx.min(out.rows.len());
            out.rows.insert(i, n.clone());
        }
        (None, None) => {}
    }
    out
}

/// THE CHECKED PATCH (`SchemaCore.patchW?`): it applies iff valid — a
/// lying witness REFUSES, it never silently mispatches. `None` is the
/// refusal.
#[must_use]
pub fn patch_w_checked(rows: &Table, d: &WDelta) -> Option<Table> {
    if valid_wb(rows, d) {
        Some(patch_w(rows, d))
    } else {
        None
    }
}

/// Validity as data (`SchemaCore.validWb`): the recorded OLD row is
/// exactly what's at the position (replace/erase), or the position is
/// in append range (insert).
#[must_use]
pub fn valid_wb(rows: &Table, d: &WDelta) -> bool {
    match (&d.old, &d.new) {
        (Some(o), _) => rows.rows().get(d.idx).is_some_and(|r| r == o),
        (None, Some(_)) => d.idx <= rows.rows().len(),
        (None, None) => true,
    }
}

/// The witnessed journal's application (`SchemaCore.witnessedApply`):
/// the patches in order, each CHECKED — a lying witness poisons the
/// fold, never silently passes (`None` is the poison).
#[must_use]
pub fn witnessed_apply(rows: &Table, log: &[WDelta]) -> Option<Table> {
    let mut acc = Some(rows.clone());
    for w in log {
        acc = acc.and_then(|t| patch_w_checked(&t, w));
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::super::schema::tests as schema_fixtures;
    use super::*;

    use schema_fixtures::{fixture, fixture_row};

    /// The frame codec's known answers: the tag bytes in ctor order,
    /// every payload byte a Lean-pinned atom.
    #[test]
    fn frame_known_answers() {
        let schema = fixture();
        let row = fixture_row(300, "hi");
        let mut out = Vec::new();
        assert!(enc_delta(&schema, &Delta::Insert(row.clone()), &mut out));
        assert_eq!(out, vec![0, 2, 0xAC, 0x02, 2, 104, 105]);
        let mut out = Vec::new();
        assert!(enc_delta(&schema, &Delta::Update(row), &mut out));
        assert_eq!(out, vec![1, 2, 0xAC, 0x02, 2, 104, 105]);
        let mut out = Vec::new();
        assert!(enc_delta(&schema, &Delta::Remove(Value::U64(300)), &mut out));
        assert_eq!(out, vec![2, 0xAC, 0x02]);
    }

    /// The append-form law: frames decode from their encoding + any
    /// suffix, exactly.
    #[test]
    fn frame_append_form() {
        let schema = fixture();
        for d in [
            Delta::Insert(fixture_row(1, "a")),
            Delta::Update(fixture_row(1, "b")),
            Delta::Remove(Value::U64(1)),
        ] {
            let mut bytes = Vec::new();
            assert!(enc_delta(&schema, &d, &mut bytes));
            bytes.extend_from_slice(&[9, 9, 9]); // the suffix
            let mut rest = bytes.as_slice();
            let decoded = dec_delta(&schema, &mut rest).unwrap_or_else(|e| panic!("{e:?}"));
            assert_eq!(decoded, d);
            assert_eq!(rest, &[9, 9, 9]);
        }
    }

    /// The keyed semantics: first-match upsert/erase (the Lean fold's
    /// exact reading, order included).
    #[test]
    fn keyed_semantics() {
        let schema = fixture();
        let mut t = Table::new();
        t.apply(&schema, &Delta::Insert(fixture_row(1, "a")));
        t.apply(&schema, &Delta::Insert(fixture_row(2, "b")));
        // Update replaces in place (first match), never appends.
        t.apply(&schema, &Delta::Update(fixture_row(1, "a2")));
        assert_eq!(t.rows().len(), 2);
        assert_eq!(t.rows()[0], fixture_row(1, "a2"));
        assert_eq!(t.rows()[1], fixture_row(2, "b"));
        // Remove erases the first match.
        t.apply(&schema, &Delta::Remove(Value::U64(1)));
        assert_eq!(t.rows(), &[fixture_row(2, "b")]);
        // Remove of an absent key is a no-op (the Lean totality).
        t.apply(&schema, &Delta::Remove(Value::U64(99)));
        assert_eq!(t.rows(), &[fixture_row(2, "b")]);
    }

    /// The inversion law at every case: patch ∘ apply ∘ invert = id
    /// (`patchW_invert`), and the recorded witness is always valid
    /// (`witnessOf_valid`).
    #[test]
    fn inversion_cases() {
        let schema = fixture();
        // Case: update over a present key.
        let mut t = Table::new();
        t.apply(&schema, &Delta::Insert(fixture_row(1, "old")));
        let before = t.clone();
        let d = Delta::Update(fixture_row(1, "new"));
        let w = witness_of(&schema, &d, &t);
        assert!(valid_wb(&t, &w), "witnessOf_valid");
        t.apply(&schema, &d);
        let rewound = patch_w_checked(&t, &invert_w(&w)).unwrap_or_else(|| panic!("lying witness"));
        assert_eq!(rewound, before);

        // Case: insert over an absent key.
        let mut t = Table::new();
        let before = t.clone();
        let d = Delta::Insert(fixture_row(1, "a"));
        let w = witness_of(&schema, &d, &t);
        assert!(valid_wb(&t, &w));
        t.apply(&schema, &d);
        let rewound = patch_w_checked(&t, &invert_w(&w)).unwrap_or_else(|| panic!("lying witness"));
        assert_eq!(rewound, before);

        // Case: remove over a present key.
        let mut t = Table::new();
        t.apply(&schema, &Delta::Insert(fixture_row(1, "a")));
        let before = t.clone();
        let d = Delta::Remove(Value::U64(1));
        let w = witness_of(&schema, &d, &t);
        assert!(valid_wb(&t, &w));
        t.apply(&schema, &d);
        let rewound = patch_w_checked(&t, &invert_w(&w)).unwrap_or_else(|| panic!("lying witness"));
        assert_eq!(rewound, before);

        // Case: remove over an ABSENT key — the no-op witness
        // (none/none), the shape `journal_notReversible` escapes by
        // RECORDING the old row (which here is honestly absent).
        let mut t = Table::new();
        let before = t.clone();
        let d = Delta::Remove(Value::U64(99));
        let w = witness_of(&schema, &d, &t);
        assert_eq!(w, WDelta { idx: 0, old: None, new: None });
        t.apply(&schema, &d);
        let rewound = patch_w_checked(&t, &invert_w(&w)).unwrap_or_else(|| panic!("lying witness"));
        assert_eq!(rewound, before);
    }

    /// NEGATIVE CONTROL — the lying witness refuses (`patchW?`'s
    /// discipline: the delta does not lie), and one bad witness poisons
    /// the whole witnessed fold.
    #[test]
    fn lying_witness_refuses() {
        let schema = fixture();
        let mut t = Table::new();
        t.apply(&schema, &Delta::Insert(fixture_row(1, "a")));
        t.apply(&schema, &Delta::Insert(fixture_row(2, "b")));
        // Lie: claim the old row at position 0 is (2, "b") — it's (1, "a").
        let liar = WDelta { idx: 0, old: Some(fixture_row(2, "b")), new: Some(fixture_row(1, "c")) };
        assert!(!valid_wb(&t, &liar));
        assert_eq!(patch_w_checked(&t, &liar), None);
        // Out-of-range insert witness refuses too.
        assert_eq!(
            patch_w_checked(&t, &WDelta { idx: 3, old: None, new: Some(fixture_row(3, "c")) }),
            None
        );
        // The poison propagates through the fold.
        let good = witness_of(&schema, &Delta::Update(fixture_row(1, "a2")), &t);
        assert_eq!(witnessed_apply(&t, &[good, liar]), None);
    }

    /// The journal wire's round trip + refusal faces.
    #[test]
    fn journal_wire() {
        let schema = fixture();
        let log = vec![
            Delta::Insert(fixture_row(300, "hi")),
            Delta::Update(fixture_row(300, "ho")),
            Delta::Remove(Value::U64(300)),
        ];
        let mut bytes = Vec::new();
        enc_journal(&schema, &log, &mut bytes);
        // varint(3) + the three frames — every atom a Lean kernel pin
        // (u64 300 = [0xAC, 0x02]; "hi" = [2,104,105]; "ho" = [2,104,111]).
        assert_eq!(
            bytes,
            vec![
                3,
                0, 2, 0xAC, 0x02, 2, 104, 105,
                1, 2, 0xAC, 0x02, 2, 104, 111,
                2, 0xAC, 0x02,
            ]
        );
        let mut rest = bytes.as_slice();
        let decoded = dec_journal(&schema, &mut rest).unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(decoded, log);
        assert!(rest.is_empty());

        // Truncation refuses (a count larger than the frames).
        let mut rest: &[u8] = &[3, 0];
        assert_eq!(dec_journal(&schema, &mut rest), Err(DecodeFail::Truncated));
        // Unknown tag refuses.
        let mut rest: &[u8] = &[1, 7];
        assert_eq!(
            dec_journal(&schema, &mut rest),
            Err(DecodeFail::Corrupt("unknown delta tag"))
        );
    }
}

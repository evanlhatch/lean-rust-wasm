//! The delta shape and its table semantics — the host mirror of
//! `SchemaLang.Delta` (the change variant: `insert`/`update` carry the
//! FULL record, v1 full replacement; `remove` carries the KEY) and of
//! `Dbsp.ChangeSpec`'s `ChangeInversion` law:
//!
//! ```text
//! patch (patch t Δt) (invert Δt) = t        -- correct_invert
//! ```
//!
//! Table-level reading (the event-sourcing shape, notes/vision.md):
//! the state is a key→row map; `insert`/`update` replace the row at
//! the key; `remove` deletes it ("the deletion is the key join's
//! signal", Delta.lean). Every delta is INVERTIBLE-BY-CONSTRUCTION
//! against the pre-image: `invert` reads the current row at the key
//! and emits the delta that restores it (`insert`/`update` over an
//! absent key invert to `remove`; `remove` of a present key inverts to
//! `insert` of the old row; `remove` of an absent key is a no-op and
//! self-inverse).

use std::collections::BTreeMap;

use crate::row::{Row, Schema, row_key_bytes};
use crate::value::Value;

/// The change variant (`Delta.lean`: declaration order pins the wire
/// tags — insert = 0, update = 1, remove = 2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Change {
    /// `insert(record)` — full record payload.
    Insert(Row),
    /// `update(record)` — full record payload (v1 full replacement).
    Update(Row),
    /// `remove(key)` — the key field's value only.
    Remove(Value),
}

impl Change {
    /// The wire tag (`Codec.encEnum` position: declaration order).
    pub(crate) fn tag(&self) -> u64 {
        match self {
            Self::Insert(_) => 0,
            Self::Update(_) => 1,
            Self::Remove(_) => 2,
        }
    }

    /// The key bytes this change acts on (canonical: the key field's
    /// wire encoding). `None` when the schema is key-less or the
    /// payload is ill-typed — callers reject before this point.
    pub(crate) fn key_bytes(&self, schema: &Schema) -> Option<Vec<u8>> {
        match self {
            Self::Insert(r) | Self::Update(r) => row_key_bytes(schema, r),
            Self::Remove(k) => {
                let mut out = Vec::new();
                if crate::row::enc_key(schema, k, &mut out) { Some(out) } else { None }
            }
        }
    }
}

/// A materialized table: key bytes → row. `BTreeMap` keeps iteration
/// deterministic (the conformance relation sorts by canonical row key
/// anyway; order is not observable — `Trace.TableEq`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Table {
    rows: BTreeMap<Vec<u8>, Row>,
}

impl Table {
    /// An empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The rows, ascending by canonical key bytes.
    pub fn rows(&self) -> impl Iterator<Item = &Row> {
        self.rows.values()
    }

    /// The row at a key, if present.
    #[must_use]
    pub fn get(&self, key_bytes: &[u8]) -> Option<&Row> {
        self.rows.get(key_bytes)
    }

    /// `Change.patch`, table-level: insert/update replace the row at
    /// the key; remove deletes it.
    pub(crate) fn patch(&mut self, schema: &Schema, change: &Change) {
        match change {
            Change::Insert(r) | Change::Update(r) => {
                if let Some(k) = row_key_bytes(schema, r) {
                    self.rows.insert(k, r.clone());
                }
            }
            Change::Remove(_) => {
                if let Some(k) = change.key_bytes(schema) {
                    self.rows.remove(&k);
                }
            }
        }
    }
}

/// `ChangeInversion.invert`, invertible-by-construction: the inverse is
/// computed against the PRE-IMAGE (the row at the key before `change`
/// lands — the log's materialized state at append time).
///
/// The law `patch (patch s Δ) (invert Δ) = s`, by cases:
/// - `Insert(r)`/`Update(r)`, key absent: inverse = `Remove(key)` —
///   patch sets r, inverse deletes it, s restored.
/// - `Insert(r)`/`Update(r)`, old row o present: inverse = `Update(o)`
///   — full replacement restores o exactly.
/// - `Remove(k)`, old row o present: inverse = `Insert(o)`.
/// - `Remove(k)`, key absent: the delta is a no-op; inverse =
///   `Remove(k)` (a no-op is self-inverse).
pub(crate) fn invert(schema: &Schema, change: &Change, pre: Option<&Row>) -> Option<Change> {
    match change {
        Change::Insert(r) | Change::Update(r) => match pre {
            None => Some(Change::Remove(r.key()?.clone())),
            Some(old) => Some(Change::Update(old.clone())),
        },
        Change::Remove(k) => match pre {
            None => Some(Change::Remove(k.clone())),
            Some(old) => Some(Change::Insert(old.clone())),
        },
    }
    .filter(|inv| inv.key_bytes(schema).is_some())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::row::Field;
    use crate::value::Ty;

    fn schema() -> Schema {
        Schema::new(vec![
            Field { name: "id".into(), ty: Ty::U64 },
            Field { name: "name".into(), ty: Ty::Str },
        ])
    }

    fn row(id: u64, name: &str) -> Row {
        match Row::new(&schema(), vec![Value::U64(id), Value::Str(name.into())]) {
            Some(r) => r,
            None => panic!("test row must pass Schema::check"),
        }
    }

    /// The ChangeInversion law, all four cases: patch(patch(s, Δ), inv Δ) = s.
    #[test]
    fn correct_invert_cases() {
        let s = schema();
        // Case 1: insert over absent key.
        let mut t = Table::new();
        let before = t.clone();
        let d = Change::Insert(row(1, "a"));
        let pre = t.get(&d.key_bytes(&s).unwrap_or_default()).cloned();
        let inv = invert(&s, &d, pre.as_ref());
        t.patch(&s, &d);
        assert!(inv.is_some());
        if let Some(inv) = inv {
            t.patch(&s, &inv);
        }
        assert_eq!(t, before);

        // Case 2: update over present key.
        let mut t = Table::new();
        t.patch(&s, &Change::Insert(row(1, "old")));
        let before = t.clone();
        let d = Change::Update(row(1, "new"));
        let pre = t.get(&d.key_bytes(&s).unwrap_or_default()).cloned();
        let inv = invert(&s, &d, pre.as_ref());
        t.patch(&s, &d);
        if let Some(inv) = inv {
            t.patch(&s, &inv);
        }
        assert_eq!(t, before);

        // Case 3: remove over present key.
        let d = Change::Remove(Value::U64(1));
        let pre = t.get(&d.key_bytes(&s).unwrap_or_default()).cloned();
        let inv = invert(&s, &d, pre.as_ref());
        t.patch(&s, &d);
        if let Some(inv) = inv {
            t.patch(&s, &inv);
        }
        assert_eq!(t, before);

        // Case 4: remove over absent key (no-op, self-inverse).
        let d = Change::Remove(Value::U64(99));
        let pre = t.get(&d.key_bytes(&s).unwrap_or_default()).cloned();
        let inv = invert(&s, &d, pre.as_ref());
        t.patch(&s, &d);
        if let Some(inv) = inv {
            t.patch(&s, &inv);
        }
        assert_eq!(t, before);
    }
}

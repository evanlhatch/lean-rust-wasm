//! The schema, the row, and their encodings — the documented
//! instantiation of the Lean journal codec's `encR`/`encK` parameters.
//!
//! `SchemaCore.Event`'s journal codec is POLYMORPHIC in the row and key
//! encoders (`encDelta encR encK` over any `fs : List Field`); the Lean
//! tree lands no concrete row codec yet, so this crate pins ONE
//! instantiation, from the Lean codec's OWN combinators (no new shape):
//!
//! ```text
//! enc_row(row)  := varint(field count) ++ encVal(field_i) in schema order
//!                  -- SchemaCore.encList's exact shape over the row's
//!                  -- positional values
//! enc_key(k)    := SchemaCore.Codec.encKey verbatim:
//!                  bool → 1 byte; u64 → varint; i64 → zigzag varint;
//!                  string → varint len + varint code points
//! ```
//!
//! The duel vectors (tests/duel/) are the LANDED journal duel emitter's
//! artifacts (`SchemaCore.Emit.Journal` — a `Kit.Duel.VectorSet`): the
//! Lean kernel computes these bytes through `encDelta`/`encJournal`
//! over EXACTLY this documented instantiation, and the byte-tie commits
//! them; the Rust side consumes them (`tests/duel_vectors.rs`), so the
//! crate's byte-exactness is enforced against the Lean kernel's own
//! encodings, never asserted.

use crate::error::{DecodeFail, DeltaError};
use crate::value::{dec_value, enc_value, Ty, Value};

/// One field: a name + its boundary type (`SchemaCore.Field`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    /// The field's name (the key projection looks it up — FIRST match
    /// wins, the `RowVals.project?` reading).
    pub name: String,
    /// The field's type.
    pub ty: Ty,
}

/// One row: the values in SCHEMA order, checked at construction (the
/// Rust face of `RowVals fs` — the Lean side is type-indexed, so
/// wrong-shape rows are unconstructible; here the check is the
/// boundary's typed refusal instead).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row(Vec<Value>);

impl Row {
    /// The positional values (schema order).
    #[must_use]
    pub fn values(&self) -> &[Value] {
        &self.0
    }

    /// Check-and-build: the values must match the schema's arity and
    /// field types exactly (the boundary's typed refusal — never a
    /// silently ill-typed row).
    ///
    /// # Errors
    /// `SchemaMismatch` on arity or per-field type mismatch.
    pub fn build(schema: &Schema, values: Vec<Value>) -> Result<Self, DeltaError> {
        if values.len() != schema.fields.len() {
            return Err(DeltaError::SchemaMismatch {
                reason: "row arity mismatch",
            });
        }
        for (f, v) in schema.fields.iter().zip(&values) {
            if f.ty != v.ty() {
                return Err(DeltaError::SchemaMismatch {
                    reason: "row field type mismatch",
                });
            }
        }
        Ok(Self(values))
    }
}

/// A keyed schema: the fields + which field names the key (`key : String`
/// in `SchemaCore.deltaApply`). The key field must EXIST — a key name
/// that names no field refuses at construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    /// The fields, in schema order (the row's positional index).
    pub fields: Vec<Field>,
    /// The key field's name.
    pub key: String,
}

impl Schema {
    /// Check-and-build: the key name must name a field.
    ///
    /// # Errors
    /// `SchemaMismatch` when the key name names no field.
    pub fn build(fields: Vec<Field>, key: &str) -> Result<Self, DeltaError> {
        if !fields.iter().any(|f| f.name == key) {
            return Err(DeltaError::SchemaMismatch {
                reason: "key name names no field",
            });
        }
        Ok(Self {
            fields,
            key: key.to_owned(),
        })
    }

    /// The key field's type.
    #[must_use]
    pub fn key_ty(&self) -> Ty {
        // build() guarantees the key names a field.
        self.fields
            .iter()
            .find(|f| f.name == self.key)
            .map_or(Ty::U64, |f| f.ty)
    }

    /// The key projection (`RowVals.project?` at the key name, FIRST
    /// match wins): the row's value at the key field.
    #[must_use]
    pub fn project_key<'a>(&'a self, row: &'a Row) -> Option<&'a Value> {
        self.fields
            .iter()
            .position(|f| f.name == self.key)
            .and_then(|i| row.0.get(i))
    }

    /// `SchemaCore.sameKey`: do both rows project the same key value?
    #[must_use]
    pub fn same_key(&self, a: &Row, b: &Row) -> bool {
        match (self.project_key(a), self.project_key(b)) {
            (Some(x), Some(y)) => x == y,
            _ => false,
        }
    }

    /// `SchemaCore.sameKeyImg`: does the row's key project to `k`?
    #[must_use]
    pub fn same_key_img(&self, row: &Row, k: &Value) -> bool {
        self.project_key(row).is_some_and(|v| v == k)
    }
}

/// `enc_row` — varint field count + one `encVal` per field, schema
/// order (see the module doc).
pub fn enc_row(row: &Row, out: &mut Vec<u8>) {
    enc_count(row.0.len(), out);
    for v in &row.0 {
        enc_value(v, out);
    }
}

/// `enc_key` — `SchemaCore.Codec.encKey` verbatim (the key's type rides
/// the schema's key field).
pub fn enc_key(schema: &Schema, k: &Value, out: &mut Vec<u8>) -> bool {
    if k.ty() != schema.key_ty() {
        return false;
    }
    enc_value(k, out);
    true
}

/// varint count (the shared framing — `SchemaCore.encList`'s head).
fn enc_count(n: usize, out: &mut Vec<u8>) {
    crate::value::enc_varint(n as u64, out);
}

/// Decode a row of the schema (varint count must match the schema's
/// arity — a count/arity disagreement refuses, never a silent
/// reshuffle; the count's real content is framing for the
/// self-delimiting fields).
pub fn dec_row(schema: &Schema, bs: &mut &[u8]) -> Result<Row, DecodeFail> {
    let n = crate::value::dec_varint(bs)?;
    if n as usize != schema.fields.len() {
        return Err(DecodeFail::Corrupt("row field count disagrees with schema"));
    }
    let mut values = Vec::new();
    for f in &schema.fields {
        values.push(dec_value(f.ty, bs)?);
    }
    Ok(Row(values))
}

/// Decode a key of the schema's key type.
pub fn dec_key(schema: &Schema, bs: &mut &[u8]) -> Result<Value, DecodeFail> {
    dec_value(schema.key_ty(), bs)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// The fixture schema (the slice's shape): id:u64 keyed, name:string.
    pub(crate) fn fixture() -> Schema {
        Schema::build(
            vec![
                Field { name: "id".into(), ty: Ty::U64 },
                Field { name: "name".into(), ty: Ty::Str },
            ],
            "id",
        )
        .unwrap_or_else(|e| panic!("fixture schema: {e}"))
    }

    pub(crate) fn fixture_row(id: u64, name: &str) -> Row {
        Row::build(&fixture(), vec![Value::U64(id), Value::Str(name.into())])
            .unwrap_or_else(|e| panic!("fixture row: {e}"))
    }

    /// The row encoding's known answer: varint(2) ++ varint(300) ++
    /// string "hi" — every byte a Lean-pinned atom (Codec.lean's pins:
    /// u64 300 = [0xAC, 0x02]; "hi" = [2, 104, 105]).
    #[test]
    fn row_known_answer() {
        let mut out = Vec::new();
        enc_row(&fixture_row(300, "hi"), &mut out);
        assert_eq!(out, vec![2, 0xAC, 0x02, 2, 104, 105]);
    }

    /// Rows round-trip; arity/type/counterfeits refuse.
    #[test]
    fn row_round_trip_and_refusals() {
        let schema = fixture();
        let row = fixture_row(300, "hi");
        let mut bytes = Vec::new();
        enc_row(&row, &mut bytes);
        let mut rest = bytes.as_slice();
        let decoded = dec_row(&schema, &mut rest).unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(decoded, row);
        assert!(rest.is_empty());

        // Arity mismatch refuses (count 1 vs schema arity 2).
        let bad = vec![1, 5];
        assert_eq!(
            dec_row(&schema, &mut bad.as_slice()),
            Err(DecodeFail::Corrupt("row field count disagrees with schema"))
        );
        // Ill-typed row refuses at construction.
        assert!(Row::build(&schema, vec![Value::Str("x".into()), Value::Str("y".into())]).is_err());
        assert!(Row::build(&schema, vec![Value::U64(1)]).is_err());
    }

    /// The key codec: encKey's bytes + the type-gate refusal.
    #[test]
    fn key_codec() {
        let schema = fixture();
        let mut out = Vec::new();
        assert!(enc_key(&schema, &Value::U64(300), &mut out));
        assert_eq!(out, vec![0xAC, 0x02]);
        // A key of the wrong type refuses to encode.
        assert!(!enc_key(&schema, &Value::Str("x".into()), &mut out));
        let decoded = dec_key(&schema, &mut out.as_slice()).unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(decoded, Value::U64(300));
    }

    /// The key projection: first-match + both rows' agreement faces.
    #[test]
    fn key_projection() {
        let schema = fixture();
        let a = fixture_row(1, "a");
        let b = fixture_row(1, "b");
        let c = fixture_row(2, "a");
        assert!(schema.same_key(&a, &b));
        assert!(!schema.same_key(&a, &c));
        assert!(schema.same_key_img(&a, &Value::U64(1)));
        assert!(!schema.same_key_img(&a, &Value::U64(2)));
        // A key name that names no field refuses at construction.
        assert!(Schema::build(schema.fields.clone(), "nope").is_err());
    }
}

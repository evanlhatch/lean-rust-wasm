//! Rows and schemas — the Rust mirror of `SchemaLang.Trace`'s row
//! layer: `Schema` is the out-of-band field list ("the field list is
//! the decoder's argument, like a table name"), `enc_row`/`dec_row`
//! port `encRowVals`/`decRowVals?` (concatenated per-field encodings,
//! self-delimiting, schema order). The key convention is `Delta.lean`'s
//! `Item.keyOf`: the FIRST field.

use crate::codec::Dec;
use crate::value::{Ty, Value, dec_value, enc_value, value_ty_matches};

/// A schema field (`SchemaLang.Field`: name + type).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    /// The field name (registration order is the schema's order).
    pub name: String,
    /// The field's codec-closed type.
    pub ty: Ty,
}

/// A table schema: the field list, out of band (the decoder argument).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    fields: Vec<Field>,
}

impl Schema {
    /// Build a schema. The first field is the KEY (`Delta.lean`
    /// `Item.keyOf`); a field-less schema has no key and therefore no
    /// change type Lean-side — the log rejects deltas for it.
    #[must_use]
    pub fn new(fields: Vec<Field>) -> Self {
        Self { fields }
    }

    /// The fields, in registration order.
    #[must_use]
    pub fn fields(&self) -> &[Field] {
        &self.fields
    }

    /// The key field (`Item.keyOf`): the first field, if any.
    #[must_use]
    pub fn key(&self) -> Option<&Field> {
        self.fields.first()
    }

    /// The `RowVals` discipline as a runtime check: arity + per-field
    /// type agreement. A row that fails never enters the log.
    #[must_use]
    pub fn check(&self, values: &[Value]) -> bool {
        self.fields.len() == values.len()
            && self
                .fields
                .iter()
                .zip(values)
                .all(|(f, v)| value_ty_matches(&f.ty, v))
    }
}

/// A row over a schema: the field values in schema order (the erased
/// `RowVals`). Construction goes through `Schema::check` at the log
/// boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    values: Vec<Value>,
}

impl Row {
    /// A row from checked values. Returns `None` on arity/type
    /// mismatch (the guarded-cast discipline: refuse, never panic).
    #[must_use]
    pub fn new(schema: &Schema, values: Vec<Value>) -> Option<Self> {
        if schema.check(&values) {
            Some(Self { values })
        } else {
            None
        }
    }

    /// The values, in schema order.
    #[must_use]
    pub fn values(&self) -> &[Value] {
        &self.values
    }

    /// The key value (the first field). `None` for a field-less schema.
    #[must_use]
    pub fn key(&self) -> Option<&Value> {
        self.values.first()
    }
}

/// `Trace.encRowVals`, public form: one row's wire bytes (schema
/// out of band). Returns `None` if the row fails `Schema::check`.
#[must_use]
pub fn encode_row(schema: &Schema, row: &Row) -> Option<Vec<u8>> {
    if !schema.check(row.values()) {
        return None;
    }
    let mut out = Vec::new();
    enc_row(schema, row, &mut out);
    Some(out)
}

/// `Trace.decRowVals?`, public append-form: the row + bytes consumed,
/// `None` on malformed/truncated input.
#[must_use]
pub fn decode_row(schema: &Schema, bytes: &[u8]) -> Option<(Row, usize)> {
    dec_row(schema, bytes).ok()
}

/// `Trace.encRowVals`: the per-field encodings, concatenated in schema
/// order (no framing — the values are self-delimiting).
pub(crate) fn enc_row(schema: &Schema, row: &Row, out: &mut Vec<u8>) {
    for (f, v) in schema.fields().iter().zip(row.values()) {
        enc_value(&f.ty, v, out);
    }
}

/// `Trace.decRowVals?`, append-form.
pub(crate) fn dec_row(schema: &Schema, bs: &[u8]) -> Dec<Row> {
    let mut values = Vec::with_capacity(schema.fields().len());
    let mut u = 0;
    for f in schema.fields() {
        let (v, used) = dec_value(&f.ty, &bs[u..])?;
        values.push(v);
        u += used;
    }
    // dec_row consumed exactly the fields' bytes; the row passed the
    // per-field typed decode, so it checks by construction.
    Ok((Row { values }, u))
}

/// The table-map key bytes for a row: the FIRST field's encoding
/// (Delta.lean's key convention). Injective on the codec-closed
/// universe by the round-trip theorem (equal bytes decode equal), so
/// byte keys are canonical.
pub(crate) fn row_key_bytes(schema: &Schema, row: &Row) -> Option<Vec<u8>> {
    let key_field = schema.key()?;
    let key = row.key()?;
    let mut out = Vec::new();
    enc_value(&key_field.ty, key, &mut out);
    Some(out)
}

/// The key value encoded standalone (the `remove` payload form).
pub(crate) fn enc_key(schema: &Schema, key: &Value, out: &mut Vec<u8>) -> bool {
    match schema.key() {
        Some(f) if value_ty_matches(&f.ty, key) => {
            enc_value(&f.ty, key, out);
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn user_schema() -> Schema {
        Schema::new(vec![
            Field { name: "id".into(), ty: Ty::U64 },
            Field { name: "name".into(), ty: Ty::Str },
        ])
    }

    #[test]
    fn row_roundtrip() {
        let s = user_schema();
        let row = Row::new(&s, vec![Value::U64(42), Value::Str("a".into())]);
        assert!(row.is_some());
        let Some(row) = row else { return };
        let mut out = Vec::new();
        enc_row(&s, &row, &mut out);
        assert_eq!(dec_row(&s, &out).ok(), Some((row, out.len())));
    }

    #[test]
    fn row_check_rejects() {
        let s = user_schema();
        assert!(Row::new(&s, vec![Value::U64(1)]).is_none()); // arity
        assert!(Row::new(&s, vec![Value::Str("x".into()), Value::Str("a".into())]).is_none());
    }
}

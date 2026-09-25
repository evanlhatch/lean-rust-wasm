//! The value universe over the GENERATED atom codec — the atom layer's
//! ONE home is `schema-generated` (the Rust emitter's artifact,
//! byte-tied to `SchemaCore.Codec` by `gates gen-check` + the duel
//! vectors); this crate CONSUMES it instead of mirroring it.
//!
//! WHAT LIVES HERE (and nowhere else): the scalar `Ty`/`Value` layer
//! (the schema-parameter instantiation the journal codec's
//! `encR`/`encK` parameters ride) + the count-framing wrapper
//! (`dec_varint`'s u64 face for the length prefixes). The atom
//! IMPLEMENTATIONS — the varint, the zigzag, the char-varint string —
//! are the generated crate's, not copies.
//!
//! THE WIRE (each law is Lean-side kernel-pinned — see Codec.lean's
//! known-answer coverage pins):
//! - bool   — one byte, `0` = false, `1` = true (any other byte refuses);
//! - u64    — the canonical-minimal LEB128 varint of the value
//!   (range-gated at 2^64 — never a silent wrap);
//! - i64    — the varint of the zigzag of the value (0→0, -1→1, 1→2, …),
//!   re-checked at decode (a zigzag outside the i64 range refuses);
//! - string — varint length + one varint code point per char (NOT
//!   UTF-8: the char-varint wire is the Lean-provable atom).
//!
//! The accepted-byte policy is the EXACT image of the encoder: every
//! out-of-policy byte shape refuses with a typed error ([`DecodeFail`],
//! mapped from the generated `CodecError` — never a panic, never a
//! silent misparse).

use crate::error::DecodeFail;
use schema_generated::{dec_bool, dec_i64, dec_string, dec_u64, enc_str, CodecError};

// The atom encode primitives' ONE home (re-exported for the frame/row
// codecs in `delta`/`schema` — the same names, one implementation).
pub use schema_generated::{enc_varint, zigzag_i64};

/// A schema field's type — the scalar sub-universe of `SchemaCore.Ty`
/// (the closed universe's container arms land with their first
/// byte-exactness authority: a Rust-side arm without a Lean-side
/// emitter would be format invention).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    /// The `SchemaCore.Ty.bool` arm.
    Bool,
    /// The `SchemaCore.Ty.u64` arm.
    U64,
    /// The `SchemaCore.Ty.i64` arm.
    I64,
    /// The `SchemaCore.Ty.string` arm.
    Str,
}

/// One field value (`SchemaCore.Value` at the scalar arms).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    /// `Value.bool`.
    Bool(bool),
    /// `Value.u64`.
    U64(u64),
    /// `Value.i64`.
    I64(i64),
    /// `Value.string`.
    Str(String),
}

impl Value {
    /// The value's own type arm.
    #[must_use]
    pub fn ty(&self) -> Ty {
        match self {
            Self::Bool(_) => Ty::Bool,
            Self::U64(_) => Ty::U64,
            Self::I64(_) => Ty::I64,
            Self::Str(_) => Ty::Str,
        }
    }
}

/// The generated codec error → this crate's failure class (the log's
/// recovery discipline dispatches on exactly this: `Truncated` is the
/// torn-write shape, everything else is corruption). The reason strings
/// are the crate's refusal vocabulary (the tests pin them).
fn atom_fail(e: CodecError) -> DecodeFail {
    match e {
        CodecError::Truncated => DecodeFail::Truncated,
        CodecError::InvalidTag(_) => DecodeFail::Corrupt("invalid bool tag"),
        CodecError::NonCanonicalVarint => DecodeFail::Corrupt("non-canonical varint"),
        CodecError::VarintOverflow => DecodeFail::Corrupt("varint over 10 groups"),
        CodecError::U64Range => DecodeFail::Corrupt("u64 out of range"),
        CodecError::I64Range => DecodeFail::Corrupt("i64 out of range"),
        CodecError::InvalidChar(_) => DecodeFail::Corrupt("invalid char"),
        CodecError::CapViolation { .. } => DecodeFail::Corrupt("cap violation"),
        CodecError::TrailingBytes => DecodeFail::Corrupt("trailing bytes"),
    }
}

/// The canonical-minimal varint decode, u64 face — the COUNT path's
/// framing wrapper (the row/journal length prefixes) over the GENERATED
/// decoder (`schema_generated::dec_varint`, the u128 carrier). A value
/// beyond u64 refuses: the count framing never silently wraps.
///
/// The u64/i64 ATOMS do not ride this wrapper — [`dec_value`] dispatches
/// to the generated `dec_u64`/`dec_i64` directly (their range gates are
/// the Lean codec's: a canonical varint in `[2^64, 2^70)` refuses as a
/// RANGE error, never a wrapped value).
///
/// # Errors
/// `Truncated` (input exhausted mid-varint) or `Corrupt` (complete
/// input, non-canonical or out-of-u64-range varint).
pub fn dec_varint(bs: &mut &[u8]) -> Result<u64, DecodeFail> {
    let n = schema_generated::dec_varint(bs).map_err(atom_fail)?;
    u64::try_from(n).map_err(|_| DecodeFail::Corrupt("varint over u64 range"))
}

/// Encode one value per its type (the `encVal` scalar arms — the byte
/// emissions are the generated codec's).
pub fn enc_value(v: &Value, out: &mut Vec<u8>) {
    match v {
        Value::Bool(b) => out.push(if *b { 1 } else { 0 }),
        Value::U64(n) => enc_varint(*n, out),
        Value::I64(i) => enc_varint(zigzag_i64(*i), out),
        Value::Str(s) => enc_str(s, out),
    }
}

/// Decode one value OF the expected type (the `decVal` scalar arms —
/// the type index comes from the schema, the byte dispatch from it;
/// every arm is the GENERATED decoder's, its range gates included).
///
/// # Errors
/// `Truncated` or `Corrupt` (the generated codec's typed refusals,
/// mapped through [`atom_fail`]).
pub fn dec_value(ty: Ty, bs: &mut &[u8]) -> Result<Value, DecodeFail> {
    match ty {
        Ty::Bool => dec_bool(bs).map(Value::Bool).map_err(atom_fail),
        Ty::U64 => dec_u64(bs).map(Value::U64).map_err(atom_fail),
        Ty::I64 => dec_i64(bs).map(Value::I64).map_err(atom_fail),
        Ty::Str => dec_string(bs).map(Value::Str).map_err(atom_fail),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean's kernel-known-answer pins (Codec.lean's coverage pins),
    /// byte-for-byte — through the GENERATED codec's emissions.
    #[test]
    fn lean_known_answer_pins() {
        let mut out = Vec::new();
        enc_value(&Value::U64(300), &mut out);
        assert_eq!(out, vec![0xAC, 0x02]);
        let mut out = Vec::new();
        enc_value(&Value::I64(-1), &mut out);
        assert_eq!(out, vec![1]);
        let mut out = Vec::new();
        enc_value(&Value::I64(1), &mut out);
        assert_eq!(out, vec![2]);
        let mut out = Vec::new();
        enc_value(&Value::Str("hi".into()), &mut out);
        assert_eq!(out, vec![2, 104, 105]);
        let mut out = Vec::new();
        enc_value(&Value::Bool(false), &mut out);
        assert_eq!(out, vec![0]);
        let mut out = Vec::new();
        enc_value(&Value::Bool(true), &mut out);
        assert_eq!(out, vec![1]);
    }

    /// The atoms round-trip through the bytes.
    #[test]
    fn atom_round_trips() {
        for v in [
            Value::Bool(false),
            Value::Bool(true),
            Value::U64(0),
            Value::U64(300),
            Value::U64(u64::MAX),
            Value::I64(0),
            Value::I64(-1),
            Value::I64(i64::MIN),
            Value::I64(i64::MAX),
            Value::Str(String::new()),
            Value::Str("hi".into()),
            Value::Str("héllo wörld".into()),
        ] {
            let mut out = Vec::new();
            enc_value(&v, &mut out);
            let decoded = dec_value(v.ty(), &mut out.as_slice()).unwrap_or_else(|e| {
                panic!("decode {v:?}: {e:?}")
            });
            assert_eq!(decoded, v);
        }
    }

    /// The refusal matrix: every out-of-policy byte shape refuses with
    /// the right class (never a silent misparse).
    #[test]
    fn refusal_matrix() {
        let mut bs: &[u8] = &[0x80];
        assert_eq!(dec_value(Ty::U64, &mut bs), Err(DecodeFail::Truncated));
        // The dangling continuation bit (Lean's truncation control).
        let mut bs: &[u8] = &[0x80];
        assert_eq!(dec_varint(&mut bs), Err(DecodeFail::Truncated));
        // Non-canonical 0x80 0x00.
        let mut bs: &[u8] = &[0x80, 0x00];
        assert_eq!(
            dec_varint(&mut bs),
            Err(DecodeFail::Corrupt("non-canonical varint"))
        );
        // Bad bool tag.
        let mut bs: &[u8] = &[2];
        assert_eq!(
            dec_value(Ty::Bool, &mut bs),
            Err(DecodeFail::Corrupt("invalid bool tag"))
        );
        // Empty input anywhere truncates.
        let mut bs: &[u8] = &[];
        assert_eq!(dec_value(Ty::Str, &mut bs), Err(DecodeFail::Truncated));
    }

    /// NEGATIVE CONTROL (the dedup's tooth): a canonical varint in
    /// `[2^64, 2^70)` — 10 groups, unrepresentable as a u64 — refuses
    /// as a RANGE error, never a wrapped value. The hand-mirrored
    /// decoder this module replaced SILENTLY WRAPPED this shape (the
    /// u64 accumulator dropped the high bits); the generated codec's
    /// range gate is the fix the dedup bought.
    #[test]
    fn u64_range_gate_never_wraps() {
        // The canonical varint of 2^64: nine 0x80 continuation groups
        // + the final 0x02 (bit 64 rides group 9; not representable as
        // a u64 — that is the point).
        let raw: &[u8] = &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02];
        let mut bs: &[u8] = raw;
        assert_eq!(
            dec_value(Ty::U64, &mut bs),
            Err(DecodeFail::Corrupt("u64 out of range"))
        );
        // The count wrapper refuses the same shape (never a wrapped count).
        let mut bs: &[u8] = raw;
        assert_eq!(
            dec_varint(&mut bs),
            Err(DecodeFail::Corrupt("varint over u64 range"))
        );
    }

    /// The zigzag round trip through the bytes, both directions across
    /// the range (the generated codec's zigzag + its decode re-check).
    #[test]
    fn zigzag_round_trip() {
        for i in [-1_i64, 0, 1, -2, 2, i64::MIN, i64::MAX] {
            let mut out = Vec::new();
            enc_value(&Value::I64(i), &mut out);
            let decoded = dec_value(Ty::I64, &mut out.as_slice())
                .unwrap_or_else(|e| panic!("decode {i}: {e:?}"));
            assert_eq!(decoded, Value::I64(i));
        }
        assert_eq!(zigzag_i64(-1), 1);
        assert_eq!(zigzag_i64(1), 2);
    }
}

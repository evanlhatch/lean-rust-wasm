//! Schema-typed values — the Rust mirror of `SchemaLang.CodecValue`'s
//! codec-CLOSED sub-universe (`CodecClosed : Ty → Type`, the provable
//! fragment). Every arm of `encode_value`/`dec_value` is a line-for-line
//! port of `encodeValue`/`decVal?`; the kernel-checked theorem
//! `decode_encodeValue_append` is the law this module is pinned to
//! (golden vectors: tests/codec_golden.rs).
//!
//! Deliberate exclusions (the CodecClosed doctrine):
//! - `f32`/`f64`: no `ofBits ∘ toBits` core lemmas; outside CodecClosed.
//! - `.ty` named refs: no `Value` constructor exists (resolved before
//!   values exist).
//! - `tensor`: codec-closed Lean-side but excluded host-side in v1
//!   (shape-gated rebuild is guest-domain; no delta carries one today).
//! - `future`/`stream`: erase to their payload Lean-side; a host log
//!   records values, not effects.

use crate::codec::{self, Dec, DecFail};

/// The codec-closed type codes (a sub-universe of `SchemaLang.Ty`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// `Ty.bool`.
    Bool,
    /// `Ty.u8` — NOTE: one raw byte on the wire (`Codec.encodeU8`), NOT
    /// a varint. The wider unsigned ints are varints.
    U8,
    /// `Ty.u16` (varint).
    U16,
    /// `Ty.u32` (varint).
    U32,
    /// `Ty.u64` (varint).
    U64,
    /// `Ty.i8` (zigzag + varint).
    I8,
    /// `Ty.i16` (zigzag + varint).
    I16,
    /// `Ty.i32` (zigzag + varint).
    I32,
    /// `Ty.i64` (zigzag + varint).
    I64,
    /// `Ty.string` — a length-prefixed list of char CODEPOINTS (each a
    /// varint), NOT UTF-8 bytes. The length prefix is the char count.
    Str,
    /// `Ty.bytes` — varint length prefix + raw bytes.
    Bytes,
    /// `Ty.option` — tag byte 0 = none, 1 = some + payload.
    Opt(Box<Ty>),
    /// `Ty.result` — tag byte 0 = ok, 1 = err (`CodecValue.encSum`).
    Res(Box<Ty>, Box<Ty>),
    /// `Ty.list` — varint element count + concatenated elements.
    List(Box<Ty>),
}

/// A schema-typed value (`CodecValue.Value` over the closed fragment).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    /// `Value.bool`.
    Bool(bool),
    /// `Value.u8`.
    U8(u8),
    /// `Value.u16`.
    U16(u16),
    /// `Value.u32`.
    U32(u32),
    /// `Value.u64`.
    U64(u64),
    /// `Value.i8`.
    I8(i8),
    /// `Value.i16`.
    I16(i16),
    /// `Value.i32`.
    I32(i32),
    /// `Value.i64`.
    I64(i64),
    /// `Value.string`.
    Str(String),
    /// `Value.bytes`.
    Bytes(Vec<u8>),
    /// `Value.some`/`Value.none`.
    Opt(Option<Box<Value>>),
    /// `Value.ok`/`Value.err`.
    Res(Result<Box<Value>, Box<Value>>),
    /// `Value.list` (the erased `VList`).
    List(Vec<Value>),
}

/// `CodecValue.zigzag` (over i64 — every signed wire int fits: the
/// source types are ≤ 64 bits).
fn zigzag(i: i64) -> u64 {
    // The standard (i << 1) ^ (i >> 63): `<<` discards high bits (no
    // overflow panic), keeping the i64::MIN arm exact
    // (zigzag(-2^63) = 2^64 - 1 — matches Lean's unbounded-Nat zigzag).
    let bits = (i << 1) ^ (i >> 63);
    #[allow(clippy::cast_sign_loss, reason = "the xor result IS the zigzag bit pattern")]
    let out = bits as u64;
    out
}

/// `CodecValue.unzigzag`.
fn unzigzag(n: u64) -> i64 {
    if n % 2 == 0 {
        // n/2 ≤ 2^63-1 for even n ≤ 2^64-2.
        i64::try_from(n / 2).unwrap_or(i64::MAX)
    } else {
        // -(n/2) - 1 ≥ -2^63 for odd n ≤ 2^64-1.
        i64::try_from(n / 2).map_or(i64::MIN, |h| -h - 1)
    }
}

/// Does this value carry this code? (The `RowVals` discipline: a
/// mismatched pair never reaches the encoder's match arms silently.)
pub fn value_ty_matches(ty: &Ty, v: &Value) -> bool {
    match (ty, v) {
        (Ty::Bool, Value::Bool(_))
        | (Ty::U8, Value::U8(_))
        | (Ty::U16, Value::U16(_))
        | (Ty::U32, Value::U32(_))
        | (Ty::U64, Value::U64(_))
        | (Ty::I8, Value::I8(_))
        | (Ty::I16, Value::I16(_))
        | (Ty::I32, Value::I32(_))
        | (Ty::I64, Value::I64(_))
        | (Ty::Str, Value::Str(_))
        | (Ty::Bytes, Value::Bytes(_)) => true,
        (Ty::Opt(t), Value::Opt(o)) => o.as_ref().is_none_or(|x| value_ty_matches(t, x)),
        (Ty::Res(ok, err), Value::Res(r)) => match r {
            Ok(x) => value_ty_matches(ok, x),
            Err(e) => value_ty_matches(err, e),
        },
        (Ty::List(t), Value::List(xs)) => xs.iter().all(|x| value_ty_matches(t, x)),
        _ => false,
    }
}

/// `CodecValue.encodeValue`, public form: the bytes of one value. A
/// type/value mismatch (`value_ty_matches` fails) is a debug-time
/// programming error; the returned bytes are unspecified then — all
/// in-crate callers check first.
#[must_use]
pub fn encode_value(ty: &Ty, v: &Value) -> Vec<u8> {
    let mut out = Vec::new();
    enc_value(ty, v, &mut out);
    out
}

/// `CodecValue.decVal?`, public append-form: the value + bytes
/// consumed, `None` on malformed/truncated input.
#[must_use]
pub fn decode_value(ty: &Ty, bytes: &[u8]) -> Option<(Value, usize)> {
    dec_value(ty, bytes).ok()
}

/// `CodecValue.encodeValue`, closed fragment. Precondition: the
/// type/value pair matches (`value_ty_matches`) — the encoder is only
/// called through `Schema`-checked rows, which enforce it.
pub(crate) fn enc_value(ty: &Ty, v: &Value, out: &mut Vec<u8>) {
    match (ty, v) {
        (Ty::Bool, Value::Bool(b)) => codec::enc_bool(*b, out),
        (Ty::U8, Value::U8(x)) => out.push(*x),
        (Ty::U16, Value::U16(x)) => codec::enc_varnat(u64::from(*x), out),
        (Ty::U32, Value::U32(x)) => codec::enc_varnat(u64::from(*x), out),
        (Ty::U64, Value::U64(x)) => codec::enc_varnat(*x, out),
        (Ty::I8, Value::I8(x)) => codec::enc_varnat(zigzag(i64::from(*x)), out),
        (Ty::I16, Value::I16(x)) => codec::enc_varnat(zigzag(i64::from(*x)), out),
        (Ty::I32, Value::I32(x)) => codec::enc_varnat(zigzag(i64::from(*x)), out),
        (Ty::I64, Value::I64(x)) => codec::enc_varnat(zigzag(*x), out),
        (Ty::Str, Value::Str(s)) => {
            codec::enc_varnat(s.chars().count() as u64, out);
            for c in s.chars() {
                codec::enc_varnat(u64::from(u32::from(c)), out);
            }
        }
        (Ty::Bytes, Value::Bytes(bs)) => codec::enc_bytes(bs, out),
        (Ty::Opt(_), Value::Opt(None)) => out.push(0),
        (Ty::Opt(t), Value::Opt(Some(x))) => {
            out.push(1);
            enc_value(t, x, out);
        }
        (Ty::Res(ok, _), Value::Res(Ok(x))) => {
            out.push(0);
            enc_value(ok, x, out);
        }
        (Ty::Res(_, err), Value::Res(Err(e))) => {
            out.push(1);
            enc_value(err, e, out);
        }
        (Ty::List(t), Value::List(xs)) => {
            codec::enc_varnat(xs.len() as u64, out);
            for x in xs {
                enc_value(t, x, out);
            }
        }
        _ => debug_assert!(false, "encode_value: type/value mismatch"),
    }
}

/// `CodecValue.decVal?`, append-form (value + bytes consumed). Ranges
/// mirror the Lean guards (`n < 2^16` etc.); invalid char codepoints
/// reject (Lean's total `Char.ofNat` coerces — the strict-decode
/// divergence documented in codec.rs).
pub(crate) fn dec_value(ty: &Ty, bs: &[u8]) -> Dec<Value> {
    match ty {
        Ty::Bool => {
            let (b, u) = codec::dec_bool(bs)?;
            Ok((Value::Bool(b), u))
        }
        Ty::U8 => match bs.first() {
            None => Err(DecFail::Torn),
            Some(&x) => Ok((Value::U8(x), 1)),
        },
        Ty::U16 => {
            let (n, u) = codec::dec_varnat(bs)?;
            let x = u16::try_from(n).map_err(|_| DecFail::Corrupt)?;
            Ok((Value::U16(x), u))
        }
        Ty::U32 => {
            let (n, u) = codec::dec_varnat(bs)?;
            let x = u32::try_from(n).map_err(|_| DecFail::Corrupt)?;
            Ok((Value::U32(x), u))
        }
        Ty::U64 => {
            let (n, u) = codec::dec_varnat(bs)?;
            Ok((Value::U64(n), u))
        }
        Ty::I8 => {
            let (n, u) = codec::dec_varnat(bs)?;
            Ok((Value::I8(unzigzag(n) as i8), u))
        }
        Ty::I16 => {
            let (n, u) = codec::dec_varnat(bs)?;
            Ok((Value::I16(unzigzag(n) as i16), u))
        }
        Ty::I32 => {
            let (n, u) = codec::dec_varnat(bs)?;
            Ok((Value::I32(unzigzag(n) as i32), u))
        }
        Ty::I64 => {
            let (n, u) = codec::dec_varnat(bs)?;
            Ok((Value::I64(unzigzag(n)), u))
        }
        Ty::Str => {
            let (count, mut u) = codec::dec_varnat(bs)?;
            let mut s = String::new();
            for _ in 0..count {
                let (cp, used) = codec::dec_varnat(&bs[u..])?;
                let c = u32::try_from(cp)
                    .ok()
                    .and_then(char::from_u32)
                    .ok_or(DecFail::Corrupt)?;
                s.push(c);
                u += used;
            }
            Ok((Value::Str(s), u))
        }
        Ty::Bytes => {
            let (payload, u) = codec::dec_bytes(bs)?;
            Ok((Value::Bytes(payload.to_vec()), u))
        }
        Ty::Opt(t) => match bs.first() {
            None => Err(DecFail::Torn),
            Some(0) => Ok((Value::Opt(None), 1)),
            Some(1) => {
                let (x, used) = dec_value(t, &bs[1..])?;
                Ok((Value::Opt(Some(Box::new(x))), 1 + used))
            }
            Some(_) => Err(DecFail::Corrupt),
        },
        Ty::Res(ok, err) => match bs.first() {
            None => Err(DecFail::Torn),
            Some(0) => {
                let (x, used) = dec_value(ok, &bs[1..])?;
                Ok((Value::Res(Ok(Box::new(x))), 1 + used))
            }
            Some(1) => {
                let (e, used) = dec_value(err, &bs[1..])?;
                Ok((Value::Res(Err(Box::new(e))), 1 + used))
            }
            Some(_) => Err(DecFail::Corrupt),
        },
        Ty::List(t) => {
            let (count, mut u) = codec::dec_varnat(bs)?;
            let mut xs = Vec::new();
            for _ in 0..count {
                let (x, used) = dec_value(t, &bs[u..])?;
                xs.push(x);
                u += used;
            }
            Ok((Value::List(xs), u))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zigzag_law() {
        for i in [0, -1, 1, -2, 2, i64::MIN, i64::MAX, i64::MIN + 1] {
            assert_eq!(unzigzag(zigzag(i)), i);
        }
        assert_eq!(zigzag(-1), 1);
        assert_eq!(zigzag(1), 2);
        assert_eq!(zigzag(i64::MIN), u64::MAX);
    }

    #[test]
    fn roundtrip_smoke() {
        let cases = [
            (Ty::Bool, Value::Bool(true)),
            (Ty::U8, Value::U8(200)),
            (Ty::U64, Value::U64(u64::MAX)),
            (Ty::I64, Value::I64(i64::MIN)),
            (Ty::Str, Value::Str("héllo".into())),
            (Ty::List(Box::new(Ty::U64)), Value::List(vec![Value::U64(300)])),
        ];
        for (ty, v) in cases {
            let mut out = Vec::new();
            enc_value(&ty, &v, &mut out);
            assert_eq!(dec_value(&ty, &out).ok(), Some((v, out.len())));
        }
    }
}

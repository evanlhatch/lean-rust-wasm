//! Golden vectors: the Rust codec pinned AGAINST THE LEAN ORACLE. Every
//! byte string below was produced by running the Lean definitions
//! themselves (`lake env lean --run` over SchemaLang.Codec /
//! CodecValue / Trace — generator script recorded in the commit
//! message). This is the "parse what the guest emits" gate: the guest's
//! encoder is the compiled Lean code; these bytes are its output.
//!
//! Schema (mirrors the generator):
//!   user: [id: u64, name: string, tags: list string, active: bool]

use wasm_delta::{Field, Row, Schema, Ty, Value, decode_row, decode_value, encode_row, encode_value};

fn hex(bs: &[u8]) -> String {
    bs.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect::<Result<Vec<u8>, _>>()
        .unwrap_or_else(|_| panic!("bad hex literal in test"))
}

fn user_schema() -> Schema {
    Schema::new(vec![
        Field { name: "id".into(), ty: Ty::U64 },
        Field { name: "name".into(), ty: Ty::Str },
        Field { name: "tags".into(), ty: Ty::List(Box::new(Ty::Str)) },
        Field { name: "active".into(), ty: Ty::Bool },
    ])
}

fn row1() -> Row {
    // id=42, name="héllo", tags=["a","bc"], active=true
    Row::new(
        &user_schema(),
        vec![
            Value::U64(42),
            Value::Str("héllo".into()),
            Value::List(vec![Value::Str("a".into()), Value::Str("bc".into())]),
            Value::Bool(true),
        ],
    )
    .unwrap_or_else(|| panic!("row1 checks"))
}

fn row2() -> Row {
    // id=7, name="", tags=[], active=false
    Row::new(
        &user_schema(),
        vec![Value::U64(7), Value::Str(String::new()), Value::List(vec![]), Value::Bool(false)],
    )
    .unwrap_or_else(|| panic!("row2 checks"))
}

/// Value-level goldens (encode direction: Rust bytes == Lean bytes).
#[test]
fn value_goldens_encode() {
    let cases: &[(&str, Ty, Value)] = &[
        ("01", Ty::Bool, Value::Bool(true)),
        ("c8", Ty::U8, Value::U8(200)),
        ("ac02", Ty::U16, Value::U16(300)),
        ("f0a204", Ty::U32, Value::U32(70000)),
        ("ffffffffffffffffff01", Ty::U64, Value::U64(u64::MAX)),
        ("01", Ty::I8, Value::I8(-1)),
        ("02", Ty::I8, Value::I8(1)),
        ("ffffffffffffffffff01", Ty::I64, Value::I64(i64::MIN)),
        ("feffffffffffffffff01", Ty::I64, Value::I64(i64::MAX)),
        // "héllo": 5 CHARS (not bytes) — é rides as codepoint varint e9 01.
        ("0568e9016c6c6f", Ty::Str, Value::Str("héllo".into())),
        ("03010203", Ty::Bytes, Value::Bytes(vec![1, 2, 3])),
        ("00", Ty::Opt(Box::new(Ty::U64)), Value::Opt(None)),
        ("01ac02", Ty::Opt(Box::new(Ty::U64)), Value::Opt(Some(Box::new(Value::U64(300))))),
        (
            "0005",
            Ty::Res(Box::new(Ty::U8), Box::new(Ty::Str)),
            Value::Res(Ok(Box::new(Value::U8(5)))),
        ),
        (
            "01026e6f",
            Ty::Res(Box::new(Ty::U8), Box::new(Ty::Str)),
            Value::Res(Err(Box::new(Value::Str("no".into())))),
        ),
        (
            "030102ac02",
            Ty::List(Box::new(Ty::U64)),
            Value::List(vec![Value::U64(1), Value::U64(2), Value::U64(300)]),
        ),
    ];
    for (want_hex, ty, v) in cases {
        let got = encode_value(ty, v);
        assert_eq!(&hex(&got), want_hex, "encode mismatch for {v:?}");
    }
}

/// Value-level goldens (decode direction: Lean bytes → Rust value) —
/// the host PARSES what the guest emits.
#[test]
fn value_goldens_decode() {
    let cases: &[(&str, Ty, Value)] = &[
        ("c8", Ty::U8, Value::U8(200)),
        ("ac02", Ty::U16, Value::U16(300)),
        ("ffffffffffffffffff01", Ty::U64, Value::U64(u64::MAX)),
        ("01", Ty::I8, Value::I8(-1)),
        ("ffffffffffffffffff01", Ty::I64, Value::I64(i64::MIN)),
        ("0568e9016c6c6f", Ty::Str, Value::Str("héllo".into())),
        ("030102ac02", Ty::List(Box::new(Ty::U64)), Value::List(vec![Value::U64(1), Value::U64(2), Value::U64(300)])),
    ];
    for (bytes_hex, ty, want) in cases {
        let bytes = unhex(bytes_hex);
        let got = decode_value(ty, &bytes);
        assert_eq!(got.as_ref().map(|(v, _)| v), Some(want), "decode mismatch for {bytes_hex}");
        assert_eq!(got.map(|(_, u)| u), Some(bytes.len()), "must consume all bytes");
    }
}

/// Row-level goldens (`Trace.encRowVals` — concatenated fields, schema
/// out of band).
#[test]
fn row_goldens() {
    let s = user_schema();
    let r1 = row1();
    let r2 = row2();
    let b1 = encode_row(&s, &r1).unwrap_or_else(|| panic!("row1 encodes"));
    assert_eq!(hex(&b1), "2a0568e9016c6c6f02016102626301");
    let b2 = encode_row(&s, &r2).unwrap_or_else(|| panic!("row2 encodes"));
    assert_eq!(hex(&b2), "07000000");
    // Decode direction: Lean's bytes → Rust rows, fully consumed.
    assert_eq!(decode_row(&s, &b1).map(|(r, u)| (r, u)), Some((r1, b1.len())));
    assert_eq!(decode_row(&s, &b2).map(|(r, u)| (r, u)), Some((r2, b2.len())));
    // row1's canonical key equals its full encoding here only because
    // the Lean golden rowKey == encRowVals for this row (pinned
    // upstream as row1_key = row1's bytes).
}

//! Round-trip properties over the codec + the journal entry format,
//! with mandatory negative controls (a vacuous suite fails the gate —
//! the TestKit.PropSpec discipline). Deterministic LCG (no deps), the
//! same generator every run.
//!
//! Properties:
//! 1. value round trip, append form: decode(encode v ++ rest) = (v, rest) for random closed values
//!    and random trailing garbage.
//! 2. row round trip through the log: entries appended, the log's raw bytes re-opened, entries
//!    decode equal.
//! 3. NEGATIVE: truncated buffers never panic and (for strict prefixes shorter than the encoding)
//!    decode to None or a shorter-consumed prefix — never the original value with the same
//!    consumption.
//! 4. NEGATIVE: bit-flipped encodings either fail or decode DIFFERENT.

mod common;

use common::Lcg;
use common::row;
use common::schemas;
use wasm_delta::Change;
use wasm_delta::DeltaLog;
use wasm_delta::MemBackend;
use wasm_delta::Ty;
use wasm_delta::Value;
use wasm_delta::decode_value;
use wasm_delta::encode_value;

/// A random leaf type.
fn gen_leaf_ty(r: &mut Lcg) -> Ty {
    match r.below(11) {
        0 => Ty::Bool,
        1 => Ty::U8,
        2 => Ty::U16,
        3 => Ty::U32,
        4 => Ty::U64,
        5 => Ty::I8,
        6 => Ty::I16,
        7 => Ty::I32,
        8 => Ty::I64,
        9 => Ty::Str,
        _ => Ty::Bytes,
    }
}

/// A random codec-closed type, bounded depth.
fn gen_ty(r: &mut Lcg, depth: u32) -> Ty {
    if depth == 0 {
        return gen_leaf_ty(r);
    }
    match r.below(14) {
        11 => Ty::Opt(Box::new(gen_ty(r, depth - 1))),
        12 => Ty::Res(
            Box::new(gen_ty(r, depth - 1)),
            Box::new(gen_ty(r, depth - 1)),
        ),
        13 => Ty::List(Box::new(gen_ty(r, depth - 1))),
        _ => gen_leaf_ty(r),
    }
}

/// A random value of a type, bounded size.
fn gen_value(r: &mut Lcg, ty: &Ty, depth: u32) -> Value {
    match ty {
        Ty::Bool => Value::Bool(r.below(2) == 0),
        Ty::U8 => Value::U8(r.next() as u8),
        Ty::U16 => Value::U16(r.next() as u16),
        Ty::U32 => Value::U32(r.next() as u32),
        Ty::U64 => Value::U64(r.next()),
        Ty::I8 => Value::I8(r.next() as i8),
        Ty::I16 => Value::I16(r.next() as i16),
        Ty::I32 => Value::I32(r.next() as i32),
        Ty::I64 => Value::I64(r.next() as i64),
        Ty::Str => Value::Str(
            (0..r.below(6))
                .map(|_| char::from_u32((r.below(0x500)) as u32).unwrap_or('x'))
                .collect(),
        ),
        Ty::Bytes => Value::Bytes((0..r.below(8)).map(|_| r.next() as u8).collect()),
        Ty::Opt(t) => {
            if r.below(2) == 0 {
                Value::Opt(None)
            } else {
                Value::Opt(Some(Box::new(gen_value(r, t, depth - 1))))
            }
        }
        Ty::Res(ok, err) => {
            if r.below(2) == 0 {
                Value::Res(Ok(Box::new(gen_value(r, ok, depth - 1))))
            } else {
                Value::Res(Err(Box::new(gen_value(r, err, depth - 1))))
            }
        }
        Ty::List(t) => Value::List(
            (0..r.below(5))
                .map(|_| gen_value(r, t, depth - 1))
                .collect(),
        ),
    }
}

/// Property 1: the append-form round trip (the Lean theorem's host
/// statement): decode(encode v ++ rest) = (v, consumed = encode len).
#[test]
fn value_roundtrip_append_form() {
    let mut r = Lcg(0x87);
    for _ in 0..2000 {
        let ty = gen_ty(&mut r, 3);
        let v = gen_value(&mut r, &ty, 3);
        let mut bytes = encode_value(&ty, &v);
        let enc_len = bytes.len();
        // Random trailing garbage must flow through untouched.
        let rest: Vec<u8> = (0..r.below(7)).map(|_| r.next() as u8).collect();
        bytes.extend_from_slice(&rest);
        let got = decode_value(&ty, &bytes);
        assert_eq!(
            got.as_ref().map(|(gv, _)| gv),
            Some(&v),
            "round trip failed for {v:?}"
        );
        assert_eq!(
            got.map(|(_, u)| u),
            Some(enc_len),
            "consumption wrong for {v:?}"
        );
        assert_eq!(
            &bytes[enc_len..],
            rest.as_slice(),
            "trailing bytes disturbed"
        );
    }
}

/// Property 3 (negative control): strict prefixes never panic and never
/// decode to (original value, full consumption).
#[test]
fn value_truncation_never_silent() {
    let mut r = Lcg(0x42);
    let mut rejections = 0u32;
    for _ in 0..500 {
        let ty = gen_ty(&mut r, 3);
        let v = gen_value(&mut r, &ty, 3);
        let bytes = encode_value(&ty, &v);
        for cut in 0..bytes.len() {
            let got = decode_value(&ty, &bytes[..cut]);
            if got.is_none() {
                rejections += 1;
                continue;
            }
            // A prefix decoding at all must not reproduce the full value
            // with full consumption (that would mean the encoding is not
            // self-delimiting — the property the Lean side proves).
            assert_ne!(
                got,
                Some((v.clone(), bytes.len())),
                "truncated decode reproduced the full value: {v:?} cut at {cut}"
            );
        }
    }
    // The negative control bit: the sweep must actually reject
    // truncations, or the test is vacuous.
    assert!(rejections > 0, "vacuous: no truncation was ever rejected");
}

/// Property 4 (negative control): single-bit flips never decode to the
/// original value at the original consumption.
#[test]
fn value_bitflip_never_silent() {
    let mut r = Lcg(0x99);
    let mut rejections = 0u32;
    for _ in 0..300 {
        let ty = gen_ty(&mut r, 2);
        let v = gen_value(&mut r, &ty, 2);
        let bytes = encode_value(&ty, &v);
        for i in 0..bytes.len() {
            for bit in [0x01u8, 0x80] {
                let mut bad = bytes.clone();
                bad[i] ^= bit;
                match decode_value(&ty, &bad) {
                    None => rejections += 1,
                    Some(got) => assert_ne!(
                        got,
                        (v.clone(), bytes.len()),
                        "bit flip silent at byte {i} for {v:?}"
                    ),
                }
            }
        }
    }
    assert!(rejections > 0, "vacuous: no corruption was ever rejected");
}

/// Property 2: the journal entry round trip through a real log —
/// append a random walk, copy the raw bytes into a fresh backend,
/// re-open, entries and states must decode equal.
#[test]
fn log_bytes_roundtrip() {
    let schema = schemas()
        .get("t")
        .unwrap_or_else(|| panic!("registered"))
        .clone();
    let mut r = Lcg(0xdead);
    let mut log =
        DeltaLog::open_with(MemBackend::new(), schemas()).unwrap_or_else(|e| panic!("open: {e}"));
    for i in 0..200 {
        let key = r.below(16);
        let change = match r.below(3) {
            0 => Change::Insert(row(&schema, key, &format!("v{i}"))),
            1 => Change::Update(row(&schema, key, &format!("u{i}"))),
            _ => Change::Remove(Value::U64(key)),
        };
        log.append("t", change)
            .unwrap_or_else(|e| panic!("append: {e}"));
    }
    let bytes = log.backend().bytes().to_vec();
    // Re-open from the raw bytes (simulating a restart).
    let mut backend = MemBackend::new();
    wasm_delta::Backend::append(&mut backend, &bytes).unwrap_or_else(|e| panic!("seed: {e}"));
    let log2 = DeltaLog::open_with(backend, schemas()).unwrap_or_else(|e| panic!("reopen: {e}"));
    assert_eq!(log.len(), log2.len());
    for seq in 0..log.len() {
        assert_eq!(log.entry(seq), log2.entry(seq), "entry {seq} diverged");
    }
    assert_eq!(log.state("t"), log2.state("t"));
}

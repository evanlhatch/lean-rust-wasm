//! The witness lane's Rust checker — the portability discipline's
//! consumer face (notes/v3/03 section 3's duel level, the witness
//! lane's row). The checker is a FRESH PORT of SchemaCore.Witness's
//! `checkWitness` + the witness wire's decoders (the equation ORDER is
//! the theorem's — see `check_witness`), riding the generated crate's
//! codec helpers (the ONE varint/string/bool encoding, never a second
//! one). The duel's verdicts are TESTED AGREEMENT (never a theorem):
//!
//! - the seeded witnesses (the producer's artifacts, emitted by
//!   SchemaCore.Emit.Witness and byte-tied by gen-check) must ACCEPT
//!   here — the Lean side's acceptance is SchemaTests' pin over the
//!   same bytes;
//! - the refusal vectors (the tamper splices + the hand-built
//!   false-claim witness the producer REFUSES to emit) must REFUSE
//!   with a typed error, never a panic;
//! - the registry table re-encodes byte-identically (the differential's
//!   both directions).

use schema_generated::{
    CodecError, dec_bool, dec_byte, dec_string, dec_u64, dec_varint, enc_str, enc_varint,
};

/// The generated registry (tests/witness_check/witnesses_generated.rs —
/// the emitted table; never hand-edited, `just gen` restores).
#[path = "witness_check/witnesses_generated.rs"]
mod witnesses_generated;

use witnesses_generated::WITNESS_REGISTRY;

/// The wire VERSION the consumer pins (the envelope gate — a mismatch
/// refuses before any payload decode).
const WITNESS_VERSION: u64 = 1;

// ---------------------------------------------------------------------------
// The claim fragment + the proof terms (SchemaCore.Witness's Rust faces)
// ---------------------------------------------------------------------------

/// The claim fragment (Pred's Rust face — the closed ctor set, tags
/// 0..7 in declaration order on the wire).
#[derive(Debug, Clone, PartialEq, Eq)]
enum Pred {
    Lit(bool),
    U64EqLit(String, u64),
    U64GtLit(String, u64),
    U64Eq(String, String),
    StrEqLit(String, String),
    And(Box<Pred>, Box<Pred>),
    Or(Box<Pred>, Box<Pred>),
    Not(Box<Pred>),
}

/// The proof terms (WProof's Rust face — tags 0..3 in declaration
/// order: verdict, conj, disj, neg).
#[derive(Debug, Clone, PartialEq, Eq)]
enum WProof {
    Verdict(bool),
    Conj(Box<WProof>, Box<WProof>),
    Disj(bool, Box<WProof>),
    Neg(Box<WProof>),
}

/// The certificate (Witness's Rust face).
#[derive(Debug, Clone, PartialEq, Eq)]
struct Witness {
    label: String,
    claim: Pred,
    proof: WProof,
    fuel: u64,
}

/// The local refusal type: the codec's typed errors + the witness
/// lane's own envelope refusals (the version gate, the depth cap).
#[derive(Debug, PartialEq, Eq)]
enum WitnessError {
    Codec(CodecError),
    Version(u128),
    Depth,
}

impl From<CodecError> for WitnessError {
    fn from(e: CodecError) -> Self {
        WitnessError::Codec(e)
    }
}

// ---------------------------------------------------------------------------
// The row carrier (the duel's shared fixture)
// ---------------------------------------------------------------------------

/// The fixture row's field values (the scalar slice the fragment's
/// atomics can read — u64/string; a missing or mistyped column
/// refuses, never fabricates).
#[derive(Debug, Clone, PartialEq, Eq)]
enum FieldVal {
    Bool(bool),
    U64(u64),
    Str(String),
}

/// The projected row: name -> value pairs (the checker resolves claims
/// BY NAME — SchemaCore.Pred's `project?` discipline).
type Row = Vec<(String, FieldVal)>;

/// THE PINNED FIXTURE ROW (the check slice's goodRow: ready = true,
/// count = 3, delta = 0, label = "a"; the option/list columns are not
/// atomically readable and carry no scalar slice). The duel's shared
/// row: the Lean producer self-checked every seeded witness against
/// the Lean twin — a drift here surfaces as a duel divergence, never
/// as a wrong acceptance on both sides.
fn fixture_row() -> Row {
    vec![
        ("ready".to_string(), FieldVal::Bool(true)),
        ("count".to_string(), FieldVal::U64(3)),
        ("label".to_string(), FieldVal::Str("a".to_string())),
    ]
}

fn project_u64(row: &Row, name: &str) -> Option<u64> {
    match row.iter().find(|(n, _)| n == name) {
        Some((_, FieldVal::U64(x))) => Some(*x),
        _ => None,
    }
}

fn project_str(row: &Row, name: &str) -> Option<String> {
    match row.iter().find(|(n, _)| n == name) {
        Some((_, FieldVal::Str(s))) => Some(s.clone()),
        _ => None,
    }
}

/// The claim's checker (Pred.check's Rust face).
fn pred_check(p: &Pred, row: &Row) -> bool {
    match p {
        Pred::Lit(b) => *b,
        Pred::U64EqLit(n, v) => project_u64(row, n).is_some_and(|x| x == *v),
        Pred::U64GtLit(n, v) => project_u64(row, n).is_some_and(|x| x > *v),
        Pred::U64Eq(a, b) => match (project_u64(row, a), project_u64(row, b)) {
            (Some(x), Some(y)) => x == y,
            _ => false,
        },
        Pred::StrEqLit(n, s) => project_str(row, n).is_some_and(|t| t == *s),
        Pred::And(p, q) => pred_check(p, row) && pred_check(q, row),
        Pred::Or(p, q) => pred_check(p, row) || pred_check(q, row),
        Pred::Not(p) => !pred_check(p, row),
    }
}

// ---------------------------------------------------------------------------
// THE CHECKER — checkWitness's Rust face (the equation ORDER is the
// theorem's: the recorded-verdict arm precedes the structural arms, so
// a `not` claim with a plain verdict record takes the verdict arm on
// BOTH sides; every mismatched shape refuses; fuel 0 refuses).
// ---------------------------------------------------------------------------

fn check_witness(fuel: u64, claim: &Pred, proof: &WProof, row: &Row) -> bool {
    if fuel == 0 {
        return false;
    }
    match proof {
        WProof::Verdict(b) => pred_check(claim, row) && *b,
        WProof::Conj(pp, pq) => match claim {
            Pred::And(p, q) => {
                check_witness(fuel - 1, p, pp, row) && check_witness(fuel - 1, q, pq, row)
            }
            _ => false,
        },
        WProof::Disj(false, pq) => match claim {
            Pred::Or(_, q) => check_witness(fuel - 1, q, pq, row),
            _ => false,
        },
        WProof::Disj(true, pp) => match claim {
            Pred::Or(p, _) => check_witness(fuel - 1, p, pp, row),
            _ => false,
        },
        WProof::Neg(inner) => match (claim, inner.as_ref()) {
            (Pred::Not(p), WProof::Verdict(false)) => !pred_check(p, row),
            _ => false,
        },
    }
}

// ---------------------------------------------------------------------------
// The wire — the depth-capped decoders + the encoders (the differential's
// both directions; unknown tags / truncation / depth exhaustion refuse,
// typed, never a silent misparse)
// ---------------------------------------------------------------------------

fn enc_bool(b: bool, out: &mut Vec<u8>) {
    out.push(if b { 1u8 } else { 0u8 });
}

/// The claim's depth-capped decoder (decPredF?'s Rust face). NOTE the
/// fuel semantics: the cap is DEPTH (one unit per nesting level, the
/// siblings share it) — the entry cap is bytes + 1, one byte per node
/// minimum.
fn dec_pred(depth: u32, bs: &mut &[u8]) -> Result<Pred, WitnessError> {
    if depth == 0 {
        return Err(WitnessError::Depth);
    }
    let tag = dec_byte(bs)?;
    match tag {
        0u8 => Ok(Pred::Lit(dec_bool(bs)?)),
        1u8 => {
            let n = dec_string(bs)?;
            let v = dec_u64(bs)?;
            Ok(Pred::U64EqLit(n, v))
        }
        2u8 => {
            let n = dec_string(bs)?;
            let v = dec_u64(bs)?;
            Ok(Pred::U64GtLit(n, v))
        }
        3u8 => {
            let a = dec_string(bs)?;
            let b = dec_string(bs)?;
            Ok(Pred::U64Eq(a, b))
        }
        4u8 => {
            let n = dec_string(bs)?;
            let s = dec_string(bs)?;
            Ok(Pred::StrEqLit(n, s))
        }
        5u8 => {
            let p = dec_pred(depth - 1, bs)?;
            let q = dec_pred(depth - 1, bs)?;
            Ok(Pred::And(Box::new(p), Box::new(q)))
        }
        6u8 => {
            let p = dec_pred(depth - 1, bs)?;
            let q = dec_pred(depth - 1, bs)?;
            Ok(Pred::Or(Box::new(p), Box::new(q)))
        }
        7u8 => {
            let p = dec_pred(depth - 1, bs)?;
            Ok(Pred::Not(Box::new(p)))
        }
        other => Err(CodecError::InvalidTag(other).into()),
    }
}

fn enc_pred(p: &Pred, out: &mut Vec<u8>) {
    match p {
        Pred::Lit(b) => {
            out.push(0u8);
            enc_bool(*b, out);
        }
        Pred::U64EqLit(n, v) => {
            out.push(1u8);
            enc_str(n, out);
            enc_varint(*v, out);
        }
        Pred::U64GtLit(n, v) => {
            out.push(2u8);
            enc_str(n, out);
            enc_varint(*v, out);
        }
        Pred::U64Eq(a, b) => {
            out.push(3u8);
            enc_str(a, out);
            enc_str(b, out);
        }
        Pred::StrEqLit(n, s) => {
            out.push(4u8);
            enc_str(n, out);
            enc_str(s, out);
        }
        Pred::And(p, q) => {
            out.push(5u8);
            enc_pred(p, out);
            enc_pred(q, out);
        }
        Pred::Or(p, q) => {
            out.push(6u8);
            enc_pred(p, out);
            enc_pred(q, out);
        }
        Pred::Not(p) => {
            out.push(7u8);
            enc_pred(p, out);
        }
    }
}

/// The proof term's depth-capped decoder (decWProofF?'s Rust face).
fn dec_proof(depth: u32, bs: &mut &[u8]) -> Result<WProof, WitnessError> {
    if depth == 0 {
        return Err(WitnessError::Depth);
    }
    let tag = dec_byte(bs)?;
    match tag {
        0u8 => Ok(WProof::Verdict(dec_bool(bs)?)),
        1u8 => {
            let a = dec_proof(depth - 1, bs)?;
            let b = dec_proof(depth - 1, bs)?;
            Ok(WProof::Conj(Box::new(a), Box::new(b)))
        }
        2u8 => {
            let c = dec_bool(bs)?;
            let a = dec_proof(depth - 1, bs)?;
            Ok(WProof::Disj(c, Box::new(a)))
        }
        3u8 => {
            let a = dec_proof(depth - 1, bs)?;
            Ok(WProof::Neg(Box::new(a)))
        }
        other => Err(CodecError::InvalidTag(other).into()),
    }
}

fn enc_proof(p: &WProof, out: &mut Vec<u8>) {
    match p {
        WProof::Verdict(b) => {
            out.push(0u8);
            enc_bool(*b, out);
        }
        WProof::Conj(a, b) => {
            out.push(1u8);
            enc_proof(a, out);
            enc_proof(b, out);
        }
        WProof::Disj(c, a) => {
            out.push(2u8);
            enc_bool(*c, out);
            enc_proof(a, out);
        }
        WProof::Neg(a) => {
            out.push(3u8);
            enc_proof(a, out);
        }
    }
}

/// The whole-form decoder: the version gate BEFORE the payload (the
/// tamper tooth), then label/claim/proof/fuel; the depth caps ride the
/// entry discipline (remaining bytes + 1). Trailing bytes refuse at
/// the caller (the exact-image form).
fn dec_witness(version_gate: u64, bs: &mut &[u8]) -> Result<Witness, WitnessError> {
    let version = dec_varint(bs)?;
    if version != version_gate as u128 {
        return Err(WitnessError::Version(version));
    }
    let label = dec_string(bs)?;
    let claim = dec_pred(bs.len() as u32 + 1, bs)?;
    let proof = dec_proof(bs.len() as u32 + 1, bs)?;
    let fuel = dec_u64(bs)?;
    Ok(Witness {
        label,
        claim,
        proof,
        fuel,
    })
}

fn enc_witness(version: u64, w: &Witness, out: &mut Vec<u8>) {
    enc_varint(version, out);
    enc_str(&w.label, out);
    enc_pred(&w.claim, out);
    enc_proof(&w.proof, out);
    enc_varint(w.fuel, out);
}

// ---------------------------------------------------------------------------
// The duel's consumer contract (Kit.Duel's convention)
// ---------------------------------------------------------------------------

/// The duel manifest, compile-time pinned to the committed artifact.
const MANIFEST: &str = include_str!("duel-witness/manifest.txt");

/// The generated crate's repo-root prefix (Kit.Duel's shared preamble —
/// byte-identical with the other duel consumers).
const CRATE_PREFIX: &str = "crates/schema-generated/";

/// Re-base a manifest row's repo-root-relative path to the crate root.
fn crate_path(row_path: &str) -> &str {
    row_path.strip_prefix(CRATE_PREFIX).unwrap_or(row_path)
}

/// One parsed manifest row: the vector path + the expectation (the
/// accept rows' note starts with `decode accept`; the refusal rows
/// render `refuse`).
struct DuelRow {
    path: String,
    accept: bool,
}

/// Kit.Duel's consumer contract, through the ONE shared parser (the
/// manifest module in mandate-delta — the journal duel's home crate): the
/// expectation vocabulary is THIS lane's — `decode accept …` accepts,
/// `refuse` refuses.
fn manifest_rows() -> Vec<DuelRow> {
    mandate_delta::parse_duel_manifest(MANIFEST, |col| {
        if col == "refuse" {
            Some(false)
        } else if col.starts_with("decode accept") {
            Some(true)
        } else {
            None
        }
    })
    .unwrap_or_else(|e| panic!("manifest: {e}"))
    .rows
    .into_iter()
    .map(|r| DuelRow {
        path: r.path,
        accept: r.expectation,
    })
    .collect()
}

/// The duel's verdict vocabulary, reduced to the two outcomes the
/// witness lane's consumer can observe: ACCEPTED (decoded AND
/// checker-accepted at the pinned fuel) vs REFUSED (a typed decode
/// error OR the checker's refusal). Never a panic.
#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Accepted,
    Refused,
}

fn witness_verdict(bytes: &[u8], row: &Row) -> Verdict {
    let mut bs = bytes;
    match dec_witness(WITNESS_VERSION, &mut bs) {
        Err(_) => Verdict::Refused,
        Ok(w) => {
            if !bs.is_empty() {
                return Verdict::Refused; // trailing bytes refuse
            }
            if check_witness(w.fuel, &w.claim, &w.proof, row) {
                Verdict::Accepted
            } else {
                Verdict::Refused
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The tests
// ---------------------------------------------------------------------------

/// THE PRODUCER→CHECKER ROUND (side B): every seeded witness decodes
/// from its registry bytes, ACCEPTS the Rust checker at its pinned
/// fuel over the fixture row, and RE-ENCODES byte-identically (the
/// differential's both directions).
#[test]
fn registry_round_trip_and_accept() {
    let row = fixture_row();
    assert!(!WITNESS_REGISTRY.is_empty(), "the seed registry is empty");
    for r in WITNESS_REGISTRY {
        assert_eq!(r.version, WITNESS_VERSION, "the registry's pinned version");
        let mut bs = r.bytes;
        let w = dec_witness(r.version, &mut bs).expect("the registry witness must decode");
        assert!(bs.is_empty(), "trailing bytes refuse: {}", r.label);
        assert_eq!(w.label, r.label, "the label survives the wire");
        assert_eq!(w.fuel, r.fuel, "the pinned fuel survives the wire");
        assert!(
            check_witness(w.fuel, &w.claim, &w.proof, &row),
            "duel divergence: the Rust checker refused the seeded witness \
             `{}` (the Lean side accepts — SchemaTests' pin over the same \
             bytes)",
            r.label
        );
        let mut out = Vec::new();
        enc_witness(r.version, &w, &mut out);
        assert_eq!(out, r.bytes, "re-encoding must be byte-identical");
    }
}

/// THE DUEL over the manifest: the accept rows must ACCEPT, the refusal
/// rows must REFUSE (typed, never a panic). A mismatch names the
/// vector — the duel's divergence witness.
#[test]
fn duel_manifest() {
    let row = fixture_row();
    for r in manifest_rows() {
        let bytes = std::fs::read(crate_path(&r.path)).expect("the duel vector file exists");
        let verdict = witness_verdict(&bytes, &row);
        match (&r.accept, &verdict) {
            (true, Verdict::Accepted) => {}
            (false, Verdict::Refused) => {}
            (true, Verdict::Refused) => panic!(
                "duel divergence at {}: the Rust checker REFUSED a seeded \
                 witness the Lean side accepts",
                r.path
            ),
            (false, Verdict::Accepted) => panic!(
                "duel divergence at {}: the Rust checker ACCEPTED a \
                 refusal vector",
                r.path
            ),
        }
    }
}

/// THE TAMPER TEETH: the flipped record refuses (the record is
/// verified, never trusted) and the byte-level version splice refuses
/// (the envelope gate fires before any payload decode).
#[test]
fn tamper_teeth() {
    let row = fixture_row();
    let good = &WITNESS_REGISTRY[0];
    // (1) the flipped record: rebuild the certificate with the proof
    //     term's verdict negated — the checker must refuse.
    let mut bs = good.bytes;
    let w = dec_witness(good.version, &mut bs).expect("decodes");
    let mut tampered = w.clone();
    match &w.proof {
        WProof::Verdict(b) => tampered.proof = WProof::Verdict(!*b),
        _ => panic!("the atomic seed's proof term is a verdict"),
    }
    assert!(
        !check_witness(tampered.fuel, &tampered.claim, &tampered.proof, &row),
        "the flipped record must refuse"
    );
    // (2) the byte-level tamper: bump the version varint's byte — the
    //     envelope gate refuses, typed.
    let mut bytes = good.bytes.to_vec();
    bytes[0] = 2u8; // the version varint: 1 -> 2
    assert_eq!(witness_verdict(&bytes, &row), Verdict::Refused);
}

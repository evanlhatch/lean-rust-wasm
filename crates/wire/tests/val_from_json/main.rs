//! FUZZ: `wire::rpc::Val::from_json` — the tagged-JSON value decoder.
//!
//! NON-DUPLICATION RATIONALE (why this target exists at all):
//! - Lean PROVES the pure codec laws of the schema-typed value codec
//!   (lean/schema-lang) and the Plausible generator suite property-tests
//!   it over random well-typed values; Rust only replays the resulting
//!   diff.json manifest. NONE of that reaches THIS surface: `Val` is
//!   the wire crate's OWN tagged-JSON vocabulary, and this target feeds
//!   it ARBITRARY bytes — hostile input, not well-typed values.
//! - This is the hostile-input contract, category (a): random bytes
//!   through the JSON parse + tag decode must NEVER panic — every run
//!   either decodes or returns a structured error.
//! - The one round-trip encoded here is Rust-only-meaningful and NOT a
//!   Lean-proved law: for any successfully decoded value, re-encoding
//!   with `Val::to_json` and decoding again is a fixpoint (the decode
//!   normalizes into the grammar's canonical form). Lean proves
//!   round-trips over well-typed schema values; this pins the
//!   normalization of whatever a hostile peer managed to get decoded.
//!
//! NOT covered here (deliberate exclusions):
//! - `read_frame`/`encode_frame` length-prefix framing needs a live
//!   transport (`RecvStream` wraps a noq stream; no in-memory
//!   constructor) and the cap check is one comparison.
//! - `decode_request`/`decode_response` are `pub(crate)` — unreachable
//!   from an integration fuzz target; the same `Val::from_json` core
//!   plus serde parse IS reachable and fuzzed here.

use bolero::check;
use wire::rpc::Val;

/// NaN-safe value equality: f64 payloads compare equal when both are
/// NaN or `==` (bit-exactness of the round-trip is not claimed — the
/// f64 string form round-trips through `format!`/`parse`).
fn eq_val(a: &Val, b: &Val) -> bool {
    match (a, b) {
        (Val::U64(x), Val::U64(y)) => x == y,
        (Val::F64(x), Val::F64(y)) => (x.is_nan() && y.is_nan()) || x == y,
        (Val::Bool(x), Val::Bool(y)) => x == y,
        (Val::String(x), Val::String(y)) => x == y,
        (Val::Some(x), Val::Some(y)) => eq_val(x, y),
        (Val::None, Val::None) => true,
        (Val::List(xs), Val::List(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys.iter()).all(|(x, y)| eq_val(x, y))
        }
        (Val::Record(xs), Val::Record(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys.iter())
                    .all(|((an, av), (bn, bv))| an == bn && eq_val(av, bv))
        }
        _ => false,
    }
}

fn main() {
    check!().for_each(|input: &[u8]| {
        // Arbitrary bytes through the parse + decode boundary: the
        // ONLY allowed outcomes are a structured error or a decoded
        // value. A panic here is the bug this target exists to find.
        let Ok(parsed) = serde_json::from_slice::<serde_json::Value>(input) else {
            return; // malformed JSON = the structured-error path
        };
        let Ok(val) = Val::from_json(&parsed) else {
            return; // tag-grammar rejection = the structured-error path
        };
        // The Rust-only fixpoint: decode ∘ to_json ∘ decode is stable.
        let reencoded = val.to_json();
        let redecoded = Val::from_json(&reencoded);
        assert!(
            matches!(&redecoded, Ok(re) if eq_val(re, &val)),
            "Val fixpoint broken: {val:?} -> {reencoded} -> {redecoded:?}"
        );
    });
}

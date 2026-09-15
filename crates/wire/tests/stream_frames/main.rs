//! FUZZ: the streaming-call frame decoders — `wire::rpc::decode_stream_ack`
//! and `wire::rpc::decode_stream_frame`.
//!
//! NON-DUPLICATION RATIONALE (why this target exists at all):
//! - Lean proves the pure laws (codec round-trips, patch/invert) over
//!   the schema-typed universe and Plausible property-tests that codec
//!   with generated values; nothing on the Lean side reaches the wire
//!   crate's RPC frame protocol — ack/item/end shapes, id correlation,
//!   and the ok:false-as-Remote classification are Rust-owned state
//!   machines parsing a hostile peer's bytes.
//! - This is the hostile-input contract, category (a): structured
//!   arbitrary frames (plus fully raw byte blobs) fed to both decoders
//!   must NEVER panic — every run decodes into a typed frame or
//!   returns a structured `WireError`.
//! - Where a frame is ACCEPTED, the classification is pinned: a valid
//!   ack is `Ok(())` exactly when ok:true + stream:true + matching id;
//!   an ok:false ack surfaces the peer's message as `WireError::Remote`
//!   (never Protocol); an end:false frame is a Protocol fault.
//!
//! NOT covered here (deliberate exclusions):
//! - `read_frame` (the 4-byte length prefix + cap): needs a live
//!   `RecvStream` (noq wrapper, no in-memory constructor) and the cap
//!   is one comparison.
//! - The client state machine around the decoders (`RemoteCaller`):
//!   sequential-call correlation is covered by `tests/rpc.rs` over the
//!   real transport; fuzzing would need a transport seam that does not
//!   exist yet.
#![allow(
    clippy::panic,
    reason = "fuzz harness: a violated property MUST abort the run — the panic is the crash report"
)]

use bolero::check;
use serde_json::json;
use wire::rpc::StreamFrame;
use wire::rpc::Val;
use wire::rpc::decode_stream_ack;
use wire::rpc::decode_stream_frame;
use wire::WireError;

/// Structured stand-in for `Val`: arbitrary recursion, converted to
/// `Val` so the builder reuses the crate's OWN encoder (`Val::to_json`)
/// instead of duplicating the tag grammar here.
#[derive(Debug, Clone, arbitrary::Arbitrary)]
enum ValInput {
    U64(u64),
    F64(f64),
    Bool(bool),
    String(String),
    Some(Box<ValInput>),
    None,
    List(Vec<ValInput>),
    Record(Vec<(String, ValInput)>),
}

impl From<ValInput> for Val {
    fn from(input: ValInput) -> Self {
        match input {
            ValInput::U64(n) => Val::U64(n),
            ValInput::F64(x) => Val::F64(x),
            ValInput::Bool(b) => Val::Bool(b),
            ValInput::String(s) => Val::String(s),
            ValInput::Some(inner) => Val::Some(Box::new((*inner).into())),
            ValInput::None => Val::None,
            ValInput::List(items) => Val::List(items.into_iter().map(Into::into).collect()),
            ValInput::Record(fields) => Val::Record(
                fields
                    .into_iter()
                    .map(|(name, val)| (name, val.into()))
                    .collect(),
            ),
        }
    }
}

/// The arbitrary frame shapes: every field the decoders look at, plus
/// a raw-bytes arm for fully hostile payloads.
#[derive(Debug, Clone, arbitrary::Arbitrary)]
enum FrameInput {
    Ack {
        id: u64,
        ok: bool,
        stream: Option<bool>,
        err: Option<String>,
    },
    Item {
        id: u64,
        val: ValInput,
    },
    End {
        id: u64,
        end_is_true: bool,
        err: Option<Option<String>>,
    },
    Raw(Vec<u8>),
}

/// NaN-safe value equality (see the val_from_json target for the
/// rationale; duplicated here so each target stands alone).
fn eq_val(a: &Val, b: &Val) -> bool {
    match (a, b) {
        (Val::F64(x), Val::F64(y)) => (x.is_nan() && y.is_nan()) || x == y,
        (Val::Some(x), Val::Some(y)) => eq_val(x, y),
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
        (a, b) => a == b,
    }
}

/// The test-built payload's JSON bytes — RAW, no length prefix: the
/// decoders take the payload (the 4-byte prefix is `read_frame`'s
/// job, which needs a live transport; see the header exclusions).
fn payload_of(payload: &serde_json::Value) -> Vec<u8> {
    match serde_json::to_vec(payload) {
        Ok(bytes) => bytes,
        Err(e) => panic!("serde_json::to_vec of a test-built payload cannot fail: {e}"),
    }
}

fn main() {
    check!()
        .with_arbitrary::<FrameInput>()
        .cloned()
        .for_each(|frame: FrameInput| {
        let req_id: u64 = 7; // the caller's correlation id for every probe
        match frame {
            FrameInput::Ack { id, ok, stream, err } => {
                let mut payload = json!({ "id": id, "ok": ok });
                if let Some(s) = stream {
                    payload["stream"] = json!(s);
                }
                if let Some(e) = &err {
                    payload["err"] = json!(e);
                }
                let bytes = payload_of(&payload);
                match decode_stream_ack(&bytes, req_id) {
                    // THE CLASSIFICATION: a valid ack passes only with
                    // the full shape; ok:false is Remote (the peer's
                    // own rejection message), everything else Protocol.
                    Ok(()) => {
                        assert!(ok && id == req_id && stream == Some(true));
                    }
                    Err(WireError::Remote(_)) => {
                        assert!(!ok, "ok:false ack must classify as Remote");
                        assert!(err.is_some(), "Remote classification requires an err message");
                    }
                    Err(WireError::Protocol(_)) => {
                        assert!(id != req_id || stream != Some(true));
                    }
                    Err(other) => panic!("ack decode produced a transport fault: {other}"),
                }
            }
            FrameInput::Item { id, val } => {
                let v: Val = val.into();
                let payload = json!({ "id": id, "item": v.to_json() });
                let bytes = payload_of(&payload);
                match decode_stream_frame(&bytes, req_id) {
                    Ok(StreamFrame::Item(decoded)) => {
                        assert!(id == req_id, "id-mismatched item must not decode");
                        // Accepted frames re-encode to a fixpoint (the
                        // same Rust-only normalization pin as the
                        // val_from_json target).
                        let re = Val::from_json(&decoded.to_json());
                        assert!(
                            matches!(&re, Ok(r) if eq_val(r, &decoded)),
                            "stream item fixpoint broken: {decoded:?}"
                        );
                    }
                    Ok(other) => panic!("item frame decoded as {other:?}"),
                    Err(WireError::Protocol(_)) => {
                        assert!(id != req_id);
                    }
                    Err(other) => panic!("item decode produced a transport fault: {other}"),
                }
            }
            FrameInput::End { id, end_is_true, err } => {
                let mut payload = json!({ "id": id, "end": end_is_true });
                match &err {
                    Some(Some(e)) => payload["err"] = json!(e),
                    Some(None) => payload["err"] = json!(null),
                    None => {}
                }
                let bytes = payload_of(&payload);
                match decode_stream_frame(&bytes, req_id) {
                    Ok(StreamFrame::End(decoded_err)) => {
                        assert!(id == req_id && end_is_true);
                        assert_eq!(decoded_err, err.clone().flatten());
                    }
                    Ok(other) => panic!("end frame decoded as {other:?}"),
                    Err(WireError::Protocol(_)) => {
                        assert!(id != req_id || !end_is_true);
                    }
                    Err(other) => panic!("end decode produced a transport fault: {other}"),
                }
            }
            // The fully hostile arm: arbitrary bytes straight into both
            // decoders. Only the no-panic contract holds — any Result
            // is acceptable.
            FrameInput::Raw(bytes) => {
                let _ = decode_stream_ack(&bytes, req_id);
                let _ = decode_stream_frame(&bytes, req_id);
            }
        }
    });
}

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
//!
//! FrameInput (the old hand-written stand-in that mirrored Val with a
//! custom ValInput enum) is removed: `Val` itself now derives
//! `arbitrary::Arbitrary` (gated behind `cfg(feature = "arbitrary")`),
//! so the fuzz target generates frame components as primitive types +
//! a real `Val` instead.

#![allow(
    clippy::panic,
    reason = "fuzz harness: a violated property MUST abort the run — the panic is the crash report"
)]

use bolero::check;
use serde_json::json;
use wire::rpc::Val;
use wire::rpc::decode_stream_ack;
use wire::rpc::decode_stream_frame;
use wire::rpc::StreamFrame;
use wire::WireError;

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

/// One fuzz iteration's generated parameters.  This replaces the old
/// hand-written FrameInput + ValInput enums: `Val` is generated
/// directly via its `arbitrary::Arbitrary` derive (gated behind
/// `cfg(feature = "arbitrary")` on the wire crate).  Each iteration
/// exercises every decoder on every frame shape plus raw hostile bytes.
#[derive(Debug, Clone, arbitrary::Arbitrary)]
struct FuzzArgs {
    /// Frame correlation id (may or may not match req_id).
    frame_id: u64,
    /// The `ok` flag in an ack frame.
    ok: bool,
    /// Optional `stream` flag in an ack frame.
    stream: Option<bool>,
    /// The `end` flag in an end frame.
    end_is_true: bool,
    /// Optional error message (ack's `err` or end's `err`).
    err: Option<String>,
    /// Value carried in an item frame — generated directly as a real Val.
    val: Val,
    /// Fully hostile raw bytes for the no-panic decoder contract.
    raw_bytes: Vec<u8>,
}

fn main() {
    check!()
        .with_arbitrary::<FuzzArgs>()
        .cloned()
        .for_each(|args: FuzzArgs| {
            let req_id: u64 = 7; // the caller's correlation id for every probe

            // ── 1. Ack frame ────────────────────────────────────────
            let mut ack_payload = json!({"id": args.frame_id, "ok": args.ok});
            if let Some(s) = args.stream {
                ack_payload["stream"] = json!(s);
            }
            if let Some(e) = &args.err {
                ack_payload["err"] = json!(e);
            }
            let ack_bytes = payload_of(&ack_payload);
            match decode_stream_ack(&ack_bytes, req_id) {
                Ok(()) => {
                    assert!(
                        args.ok && args.frame_id == req_id && args.stream == Some(true)
                    );
                }
                Err(WireError::Remote(_)) => {
                    assert!(!args.ok, "ok:false ack must classify as Remote");
                    assert!(
                        args.err.is_some(),
                        "Remote classification requires an err message"
                    );
                }
                Err(WireError::Protocol(_)) => {
                    assert!(
                        args.frame_id != req_id || args.stream != Some(true)
                    );
                }
                Err(other) => {
                    panic!("ack decode produced a transport fault: {other}")
                }
            }

            // ── 2. Item frame ──────────────────────────────────────
            let item_payload = json!({"id": args.frame_id, "item": args.val.to_json()});
            let item_bytes = payload_of(&item_payload);
            match decode_stream_frame(&item_bytes, req_id) {
                Ok(StreamFrame::Item(decoded)) => {
                    assert!(
                        args.frame_id == req_id,
                        "id-mismatched item must not decode"
                    );
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
                    assert!(args.frame_id != req_id);
                }
                Err(other) => {
                    panic!("item decode produced a transport fault: {other}")
                }
            }

            // ── 3. End frame ────────────────────────────────────────
            let mut end_payload = json!({"id": args.frame_id, "end": args.end_is_true});
            if let Some(e) = &args.err {
                end_payload["err"] = json!(e);
            }
            let end_bytes = payload_of(&end_payload);
            let want_err = if args.end_is_true {
                args.err.clone()
            } else {
                None
            };
            match decode_stream_frame(&end_bytes, req_id) {
                Ok(StreamFrame::End(decoded_err)) => {
                    assert!(args.frame_id == req_id && args.end_is_true);
                    assert_eq!(decoded_err, want_err);
                }
                Ok(other) => panic!("end frame decoded as {other:?}"),
                Err(WireError::Protocol(_)) => {
                    assert!(args.frame_id != req_id || !args.end_is_true);
                }
                Err(other) => {
                    panic!("end decode produced a transport fault: {other}")
                }
            }

            // ── 4. Raw hostile bytes: only the no-panic contract ──
            let _ = decode_stream_ack(&args.raw_bytes, req_id);
            let _ = decode_stream_frame(&args.raw_bytes, req_id);
        });
}
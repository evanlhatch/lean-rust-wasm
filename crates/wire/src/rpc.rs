//! WIT-native RPC framing over the [`crate`] seam.
//!
//! # Frame protocol (this crate OWNS the framing)
//!
//! One frame = 4-byte big-endian length prefix + that many bytes of
//! UTF-8 JSON. One bidi stream = one call: client sends a request
//! frame, then [`crate::SendStream::finish`]; server responds with a
//! response frame and finishes.
//!
//! Request:  `{"id": <u64>, "fn": "<name>", "args": [<val>...]}`
//! Response: `{"id": <u64>, "ok": true,  "vals": [<val>...]}`
//!        or `{"id": <u64>, "ok": false, "err": "<msg>"}`
//!
//! # Val representation
//!
//! Tagged JSON: `{"t":"u64","v":"<decimal>"}`, `{"t":"f64","v":"..."}`,
//! `{"t":"bool","v":true|false}`, `{"t":"string","v":"..."}`. Numeric
//! scalars travel as strings to keep u64 precision and f64 round-trips
//! exact through JSON.
//!
//! Aggregates nest the same tagged grammar recursively:
//!
//! - option: `{"t":"some","v":<val>}` / `{"t":"none"}` (no `v`)
//! - list:   `{"t":"list","v":[<val>, ...]}`
//! - record: `{"t":"record","v":[["<field>", <val>], ...]}`
//!
//! Record fields are an ARRAY OF PAIRS, not a JSON object: this crate
//! builds serde_json without the `preserve_order` feature, so a JSON
//! object would silently sort keys (BTreeMap) and lose field order —
//! a semantic difference for WIT records. Pairs keep order exact and
//! round-trip verifiable. Nesting is arbitrary (list of records,
//! option of list, ...) with a decode depth cap of [`MAX_VAL_DEPTH`]
//! so a hostile peer cannot drive unbounded recursion. Results and
//! handles remain out of scope.
//!
//! # Serving
//!
//! [`serve`] runs the accept loop of a server-capable [`Transport`] and
//! dispatches calls to an [`RpcTarget`] — the generic `(&str, &[Val])
//! -> Result<Vec<Val>>` call surface, so `wire` never depends on a
//! host. One task per connection, one task per bidi stream inside it.

use std::future::Future;
use std::sync::Arc;

use serde_json::Value;
use serde_json::json;

use crate::Conn;
use crate::RecvStream;
use crate::SendStream;
use crate::Transport;
use crate::WireError;

/// Hard cap on one frame's JSON payload: guards the length-prefix read
/// against a corrupt or hostile peer directing an unbounded allocation.
const MAX_FRAME_BYTES: u32 = 16 * 1024 * 1024;

/// Decode recursion cap: no legitimate WIT type nests this deep; a
/// hostile peer feeding deeply nested `some`/`list`/`record` tags gets
/// a protocol fault instead of a stack overflow.
const MAX_VAL_DEPTH: usize = 128;

/// A wire-representable component value: scalars plus the aggregate
/// shapes option/list/record (see module docs for the exact JSON).
#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    /// Unsigned 64-bit integer (`u64` WIT scalar).
    U64(u64),
    /// IEEE-754 double (`f64` WIT scalar).
    F64(f64),
    /// Boolean (`bool` WIT scalar).
    Bool(bool),
    /// Unicode string (`string` WIT type).
    String(String),
    /// Present option (`option<_>` with a value); payload boxed to
    /// keep `Val` a reasonable size.
    Some(Box<Val>),
    /// Absent option (`option<_>` with no value).
    None,
    /// List of values (`list<_>` WIT type), in order.
    List(Vec<Val>),
    /// Record: field name / value pairs IN ORDER. Order is semantic
    /// (WIT record fields are positional in the type), hence the pair
    /// array on the wire instead of a JSON object — see module docs.
    Record(Vec<(String, Val)>),
}

impl Val {
    /// The value's tagged-JSON form. Numeric scalars serialize as
    /// decimal strings (u64 precision, f64 round-trip); bool as a JSON
    /// boolean; string as a JSON string; aggregates nest recursively
    /// (record fields as an order-preserving pair array).
    pub fn to_json(&self) -> Value {
        match self {
            Val::U64(n) => json!({ "t": "u64", "v": n.to_string() }),
            Val::F64(x) => json!({ "t": "f64", "v": format!("{x}") }),
            Val::Bool(b) => json!({ "t": "bool", "v": b }),
            Val::String(s) => json!({ "t": "string", "v": s }),
            Val::Some(inner) => json!({ "t": "some", "v": inner.to_json() }),
            Val::None => json!({ "t": "none" }),
            Val::List(items) => json!({
                "t": "list",
                "v": items.iter().map(Val::to_json).collect::<Vec<_>>(),
            }),
            Val::Record(fields) => json!({
                "t": "record",
                // Pair array, NOT a JSON object: preserves field order
                // (serde_json here sorts object keys; see module docs).
                "v": fields
                    .iter()
                    .map(|(name, val)| json!([name, val.to_json()]))
                    .collect::<Vec<_>>(),
            }),
        }
    }

    /// Inverse of [`Val::to_json`]; any deviation from the tag grammar
    /// is a protocol fault, not a silent coercion.
    ///
    /// # Errors
    /// Malformed tagged JSON: not an object, unknown tag, a `v`
    /// payload that does not parse as the tag's shape, or aggregate
    /// nesting deeper than [`MAX_VAL_DEPTH`].
    pub fn from_json(v: &Value) -> Result<Val, String> {
        Self::from_json_depth(v, 0)
    }

    /// [`Val::from_json`] with a recursion budget; all decode paths
    /// funnel here so a hostile peer cannot overflow the stack.
    fn from_json_depth(v: &Value, depth: usize) -> Result<Val, String> {
        if depth > MAX_VAL_DEPTH {
            return Err(format!("val: nesting deeper than {MAX_VAL_DEPTH}"));
        }
        let obj = v.as_object().ok_or_else(|| "val: not an object".to_owned())?;
        let tag = obj
            .get("t")
            .and_then(Value::as_str)
            .ok_or_else(|| "val: missing `t` tag".to_owned())?;
        // `none` is the only tag with no payload; all others require `v`.
        if tag == "none" {
            return Ok(Val::None);
        }
        let inner = obj.get("v").ok_or_else(|| "val: missing `v`".to_owned())?;
        match tag {
            "u64" => inner
                .as_str()
                .ok_or_else(|| "val u64: `v` not a string".to_owned())
                .and_then(|s| s.parse::<u64>().map_err(|e| format!("val u64: {e}")))
                .map(Val::U64),
            "f64" => inner
                .as_str()
                .ok_or_else(|| "val f64: `v` not a string".to_owned())
                .and_then(|s| s.parse::<f64>().map_err(|e| format!("val f64: {e}")))
                .map(Val::F64),
            "bool" => inner
                .as_bool()
                .ok_or_else(|| "val bool: `v` not a bool".to_owned())
                .map(Val::Bool),
            "string" => inner
                .as_str()
                .ok_or_else(|| "val string: `v` not a string".to_owned())
                .map(|s| Val::String(s.to_owned())),
            "some" => Self::from_json_depth(inner, depth + 1)
                .map(Box::new)
                .map(Val::Some),
            "list" => inner
                .as_array()
                .ok_or_else(|| "val list: `v` not an array".to_owned())?
                .iter()
                .map(|item| Self::from_json_depth(item, depth + 1))
                .collect::<Result<Vec<_>, _>>()
                .map(Val::List),
            "record" => inner
                .as_array()
                .ok_or_else(|| "val record: `v` not an array".to_owned())?
                .iter()
                .map(|entry| Self::record_field(entry, depth))
                .collect::<Result<Vec<_>, _>>()
                .map(Val::Record),
            other => Err(format!("val: unknown tag `{other}`")),
        }
    }

    /// One `["<field>", <val>]` entry of a record's pair array.
    fn record_field(entry: &Value, depth: usize) -> Result<(String, Val), String> {
        let pair = entry
            .as_array()
            .ok_or_else(|| "val record: field entry not a pair array".to_owned())?;
        let (name, val) = match pair.as_slice() {
            [name, val] => (name, val),
            _ => return Err("val record: field entry not exactly [name, val]".to_owned()),
        };
        let name = name
            .as_str()
            .ok_or_else(|| "val record: field name not a string".to_owned())?
            .to_owned();
        let val = Self::from_json_depth(val, depth + 1)?;
        Ok((name, val))
    }
}

/// One call request (see the module docs for the JSON shape).
#[derive(Debug, Clone)]
pub(crate) struct Request {
    /// Caller-assigned correlation id; the response echoes it back.
    pub id: u64,
    /// Exported function name.
    pub func: String,
    /// Positional arguments.
    pub args: Vec<Val>,
}

impl Request {
    /// Length-prefixed wire bytes for this request.
    pub(crate) fn encode(&self) -> Result<Vec<u8>, WireError> {
        let payload = json!({
            "id": self.id,
            "fn": self.func,
            "args": self.args.iter().map(Val::to_json).collect::<Vec<_>>(),
        });
        encode_frame(&payload)
    }

    /// Parse a request frame from decoded JSON.
    fn from_json(v: &Value) -> Result<Request, String> {
        let obj = v.as_object().ok_or_else(|| "request: not an object".to_owned())?;
        let id = obj
            .get("id")
            .and_then(Value::as_u64)
            .ok_or_else(|| "request.id: not u64".to_owned())?;
        let func = obj
            .get("fn")
            .and_then(Value::as_str)
            .ok_or_else(|| "request.fn: not a string".to_owned())?
            .to_owned();
        let args_val = obj
            .get("args")
            .and_then(Value::as_array)
            .ok_or_else(|| "request.args: not an array".to_owned())?;
        let args = args_val.iter().map(Val::from_json).collect::<Result<Vec<_>, _>>()?;
        Ok(Request { id, func, args })
    }
}

/// Payload of one call response.
#[derive(Debug, Clone)]
pub(crate) enum Outcome {
    /// The target call succeeded; returned values in order.
    Ok(Vec<Val>),
    /// The target call failed; the target's error message.
    Fail(String),
}

/// One call response (see the module docs for the JSON shape).
#[derive(Debug, Clone)]
pub(crate) struct Response {
    /// Echoes the request's correlation id.
    pub id: u64,
    /// Success values or the failure message.
    pub outcome: Outcome,
}

impl Response {
    /// Length-prefixed wire bytes for this response.
    fn encode(&self) -> Result<Vec<u8>, WireError> {
        let payload = match &self.outcome {
            Outcome::Ok(vals) => json!({
                "id": self.id,
                "ok": true,
                "vals": vals.iter().map(Val::to_json).collect::<Vec<_>>(),
            }),
            Outcome::Fail(err) => json!({ "id": self.id, "ok": false, "err": err }),
        };
        encode_frame(&payload)
    }

    /// Parse a response frame from decoded JSON.
    fn from_json(v: &Value) -> Result<Response, String> {
        let obj = v.as_object().ok_or_else(|| "response: not an object".to_owned())?;
        let id = obj
            .get("id")
            .and_then(Value::as_u64)
            .ok_or_else(|| "response.id: not u64".to_owned())?;
        let ok = obj
            .get("ok")
            .and_then(Value::as_bool)
            .ok_or_else(|| "response.ok: not a bool".to_owned())?;
        let outcome = if ok {
            let vals_val = obj
                .get("vals")
                .and_then(Value::as_array)
                .ok_or_else(|| "response.vals: not an array".to_owned())?;
            let vals = vals_val.iter().map(Val::from_json).collect::<Result<Vec<_>, _>>()?;
            Outcome::Ok(vals)
        } else {
            let err = obj
                .get("err")
                .and_then(Value::as_str)
                .ok_or_else(|| "response.err: not a string".to_owned())?
                .to_owned();
            Outcome::Fail(err)
        };
        Ok(Response { id, outcome })
    }
}

/// Wrap `payload` in the frame envelope: 4-byte big-endian length +
/// the JSON bytes.
fn encode_frame(payload: &Value) -> Result<Vec<u8>, WireError> {
    let json = serde_json::to_vec(payload)
        .map_err(|e| WireError::Protocol(format!("frame encode: {e}")))?;
    let len = u32::try_from(json.len())
        .map_err(|_| WireError::Protocol(format!("frame too large: {} bytes", json.len())))?;
    let mut frame = Vec::with_capacity(4 + json.len());
    frame.extend_from_slice(&len.to_be_bytes());
    frame.extend_from_slice(&json);
    Ok(frame)
}

/// Read one frame: the length prefix, then exactly that many payload
/// bytes. The payload stays raw; callers decode per direction.
pub(crate) async fn read_frame(recv: &mut RecvStream) -> Result<Vec<u8>, WireError> {
    let mut prefix = [0u8; 4];
    recv.read_exact(&mut prefix).await?;
    let len = u32::from_be_bytes(prefix);
    if len > MAX_FRAME_BYTES {
        return Err(WireError::Protocol(format!(
            "frame length {len} exceeds cap {MAX_FRAME_BYTES}"
        )));
    }
    let mut payload = vec![
        0u8;
        usize::try_from(len)
            .map_err(|_| WireError::Protocol(format!("frame length {len} exceeds usize")))?
    ];
    recv.read_exact(&mut payload).await?;
    Ok(payload)
}

/// Decode raw frame bytes into a [`Request`].
pub(crate) fn decode_request(bytes: &[u8]) -> Result<Request, WireError> {
    let v: Value =
        serde_json::from_slice(bytes).map_err(|e| WireError::Protocol(format!("request: {e}")))?;
    Request::from_json(&v).map_err(WireError::Protocol)
}

/// Decode raw frame bytes into a [`Response`].
pub(crate) fn decode_response(bytes: &[u8]) -> Result<Response, WireError> {
    let v: Value =
        serde_json::from_slice(bytes).map_err(|e| WireError::Protocol(format!("response: {e}")))?;
    Response::from_json(&v).map_err(WireError::Protocol)
}

/// The generic call surface `serve` dispatches to. A host implements
/// this over its component runtimes; `wire` stays ignorant of any
/// concrete host type.
pub trait RpcTarget: Send + Sync + 'static {
    /// Call exported function `func` with positional `args`.
    ///
    /// # Errors
    /// Any target-side failure (unknown function, marshalling, guest
    /// trap) as a message; it becomes the response's `err` frame.
    fn call(
        &self,
        func: &str,
        args: &[Val],
    ) -> impl Future<Output = Result<Vec<Val>, String>> + Send;
}

/// Serve RPC calls forever: accept every connection, then one task per
/// bidi stream (one call). Never returns normally; ends when the
/// transport's accept loop fails.
///
/// Generic over the target (not `dyn`): `RpcTarget::call` is native
/// async-in-trait, which is not dyn compatible — a host with several
/// runtimes boxes them behind its own enum or spawns one `serve` per
/// runtime instead.
///
/// # Errors
/// Propagates [`Transport::accept`] failures — bind first, then pass
/// the bound transport in.
pub async fn serve<T: Transport, R: RpcTarget>(
    transport: &mut T,
    target: Arc<R>,
) -> Result<(), WireError> {
    loop {
        let conn = transport.accept().await?;
        let target = Arc::clone(&target);
        tokio::spawn(async move {
            while let Ok((send, recv)) = conn.accept_bidirectional().await {
                let target = Arc::clone(&target);
                tokio::spawn(async move { handle_stream(send, recv, target).await });
            }
        });
    }
}

/// One call's lifecycle on one bidi stream: read the request frame,
/// dispatch, answer (ok or err), finish. A request read that fails
/// (stream or connection dead, malformed frame) ends the stream with
/// no response — there is no id to correlate an error to.
async fn handle_stream<R: RpcTarget>(
    mut send: SendStream,
    mut recv: RecvStream,
    target: Arc<R>,
) {
    let response = match read_frame(&mut recv).await.and_then(|bytes| decode_request(&bytes)) {
        Err(_) => return,
        Ok(request) => {
            let outcome = match target.call(&request.func, &request.args).await {
                Ok(vals) => Outcome::Ok(vals),
                Err(err) => Outcome::Fail(err),
            };
            Response { id: request.id, outcome }
        }
    };
    // Best-effort answer: a peer that hung up just drops it. Encode
    // failure (only conceivable: a >4 GiB value list) ends the stream
    // silently rather than answering garbage.
    if let Ok(frame) = response.encode() {
        let _ = send.write_all(&frame).await;
        let _ = send.finish().await;
    }
}

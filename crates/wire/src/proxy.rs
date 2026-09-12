//! Client-side remote-call proxy: the mesh's caller half.
//!
//! [`RemoteCaller`] wraps an established [`Conn`] and exposes the
//! generic call surface — `call(&str, &[Val]) -> Result<Vec<Val>>` —
//! mirroring the server's [`RpcTarget`](crate::rpc::RpcTarget). One
//! bidi stream per call (frame protocol in [`crate::rpc`]); calls on
//! one `RemoteCaller` are sequential (correlation ids are simple), but
//! callers may open several `RemoteCaller`s over the same connection
//! shape for concurrency. Full host-shape transparency (a
//! `ComponentRuntime`-shaped drop-in) is a later layer; this is the
//! mesh's core call primitive.
//!
//! Streaming: [`RemoteCaller::call_streaming`] opens a streaming call
//! (request + `"stream":true`) and returns a [`StreamingCall`] that
//! yields the producer's items incrementally — the mesh's
//! stream-forwarding primitive (a component host forwards a WASM
//! stream's items to a remote peer).

use crate::Conn;
use crate::rpc::Request;
use crate::rpc::StreamFrame;
use crate::rpc::Val;
use crate::rpc::decode_response;
use crate::rpc::decode_stream_ack;
use crate::rpc::decode_stream_frame;
use crate::rpc::read_frame;
use crate::WireError;

/// Calls a remote [`RpcTarget`](crate::rpc::RpcTarget) through a
/// stream-based connection.
pub struct RemoteCaller<C: Conn> {
    conn: C,
    next_id: u64,
}

impl<C: Conn> RemoteCaller<C> {
    /// Proxy calls over an established connection.
    pub fn new(conn: C) -> Self {
        Self { conn, next_id: 1 }
    }

    /// Call remote function `func` with positional `args`.
    ///
    /// One request frame on a fresh bidi stream; awaits the correlated
    /// response frame on the same stream.
    ///
    /// # Errors
    /// - transport faults while opening/sending/receiving
    ///   ([`WireError::Send`]/[`WireError::Recv`]/[`WireError::Connection`])
    /// - malformed or mismatched frames ([`WireError::Protocol`])
    /// - the remote target's failure ([`WireError::Remote`], message
    ///   preserved)
    pub async fn call(&mut self, func: &str, args: &[Val]) -> Result<Vec<Val>, WireError> {
        let id = self.next_id;
        self.next_id = self.next_id.wrapping_add(1);
        let request = Request { id, func: func.to_owned(), args: args.to_vec(), stream: false };
        let (mut send, mut recv) = self.conn.open_bidirectional().await?;
        send.write_all(&request.encode()?).await?;
        send.finish().await?;
        let bytes = read_frame(&mut recv).await?;
        let response = decode_response(&bytes)?;
        if response.id != id {
            return Err(WireError::Protocol(format!(
                "response id {} does not match request {id}",
                response.id
            )));
        }
        match response.outcome {
            crate::rpc::Outcome::Ok(vals) => Ok(vals),
            crate::rpc::Outcome::Fail(err) => Err(WireError::Remote(err)),
        }
    }

    /// Call remote function `func` as a STREAMING call: returns a
    /// [`StreamingCall`] that yields the remote producer's items
    /// incrementally over one bidi stream.
    ///
    /// Sends the request frame (the plain shape plus
    /// `"stream":true`), awaits and validates the ack frame, then
    /// hands the receive half to the returned [`StreamingCall`].
    ///
    /// # Errors
    /// - transport faults while opening/sending/receiving
    /// - the ack deviating from `{"id","ok":true,"stream":true}`
    ///   ([`WireError::Protocol`]); a server that answered the plain
    ///   `ok:false` rejection instead surfaces as
    ///   [`WireError::Remote`] (message preserved)
    pub async fn call_streaming(
        &mut self,
        func: &str,
        args: &[Val],
    ) -> Result<StreamingCall, WireError> {
        let id = self.next_id;
        self.next_id = self.next_id.wrapping_add(1);
        let request = Request { id, func: func.to_owned(), args: args.to_vec(), stream: true };
        let (mut send, mut recv) = self.conn.open_bidirectional().await?;
        send.write_all(&request.encode()?).await?;
        send.finish().await?;
        let bytes = read_frame(&mut recv).await?;
        decode_stream_ack(&bytes, id)?;
        Ok(StreamingCall { recv, id, done: false })
    }
}

/// One in-progress streaming call: the receive half of the bidi
/// stream the call runs on, plus the correlation id and the
/// end-of-stream latch.
pub struct StreamingCall {
    recv: crate::RecvStream,
    id: u64,
    /// Set once the terminal `end` frame was seen; a further
    /// [`StreamingCall::next`] faults (frames after `end` are a
    /// protocol violation).
    done: bool,
}

impl StreamingCall {
    /// The next produced item, in order.
    ///
    /// Returns `Ok(Some(val))` per item frame, `Ok(None)` exactly once
    /// on a clean end (terminal frame with `err:null`),
    /// `Err(WireError::Remote)` when the producer failed mid-stream
    /// (terminal frame's `err` message preserved), and
    /// `Err(WireError::Protocol)` for a broken frame (id mismatch,
    /// unknown shape, item after `end`).
    ///
    /// # Errors
    /// See above; transport read failures propagate as
    /// [`WireError::Recv`]/[`WireError::Connection`].
    pub async fn next(&mut self) -> Result<Option<Val>, WireError> {
        if self.done {
            return Err(WireError::Protocol("stream frame after `end`".to_owned()));
        }
        let bytes = read_frame(&mut self.recv).await?;
        match decode_stream_frame(&bytes, self.id)? {
            StreamFrame::Item(val) => Ok(Some(val)),
            StreamFrame::End(err) => {
                self.done = true;
                match err {
                    Some(err) => Err(WireError::Remote(err)),
                    None => Ok(None),
                }
            }
        }
    }
}

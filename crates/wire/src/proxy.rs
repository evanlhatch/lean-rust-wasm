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

use crate::Conn;
use crate::rpc::Request;
use crate::rpc::Val;
use crate::rpc::decode_response;
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
        let request = Request { id, func: func.to_owned(), args: args.to_vec() };
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
}

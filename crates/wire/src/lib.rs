//! `wire` — the transport-generic QUIC seam for the component mesh.
//!
//! # Role
//!
//! Track 2 of the mesh plan (`notes/async-wrpc-oci-plan.md`): guestlang
//! components call each other's exports over the network. The transport
//! MUST be swappable, so this crate defines the seam (`Transport`,
//! `Conn`, `SendStream`, `RecvStream`) and keeps every concrete
//! transport type OUT of the trait signatures.
//!
//! [`noq`] (n0-computer's Quinn fork) is the FIRST adapter via
//! [`NoqTransport`]/[`NoqConn`]. The WIT-native RPC layer lands on top
//! of this seam later; nothing in this crate knows about WIT or RPC.
//!
//! # Security posture
//!
//! QUIC requires TLS. This crate's only TLS mode today is a RUNTIME-
//! GENERATED self-signed cert + a certificate-verifier that accepts
//! EVERYTHING (`SkipServerVerification`, lifted verbatim from noq's
//! own `insecure_connection` example). That is vulnerable to
//! machine-in-the-middle attacks BY CONSTRUCTION and is fit only for
//! the local dev/test loop. Real peer verification (pinned roots /
//! WebPKI) is a tracked gap, not a done deal — do not point this at a
//! network you do not control.
//!
//! # Send/Recv stream shape
//!
//! Concrete wrapper structs, not traits: noq's stream types appear
//! ONLY as private fields inside [`SendStream`]/[`RecvStream`], so the
//! public byte-level API (`read_exact`, `read_to_end`, `write_all`,
//! `finish`) is transport-neutral. Swapping adapters means re-pointing
//! the wrapper internals — the seam's public surface does not change.
//! Framing (length-prefix vs EOF-delimited) is the CALLER's concern;
//! these wrappers expose exactly the byte-level primitives plus
//! [`SendStream::finish`] for EOF signalling.

use std::fmt;
use std::net::SocketAddr;

/// Error type for every fallible `wire` operation.
///
/// String-backed on purpose: this crate compiles fast, and callers
/// (the mesh RPC layer) treat transport failures as opaque faults to
/// surface, not match on. The workspace error tool (fast-observe) is
/// deliberately not a dependency of the seam itself.
#[derive(Debug)]
pub enum WireError {
    /// Failed to bind a listening endpoint.
    Bind(String),
    /// Failed to establish an outgoing connection.
    Connect(String),
    /// An established connection failed mid-flight.
    Connection(String),
    /// Writing to a send stream failed.
    Send(String),
    /// Reading from a recv stream failed.
    Recv(String),
}

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WireError::Bind(e) => write!(f, "wire: bind failed: {e}"),
            WireError::Connect(e) => write!(f, "wire: connect failed: {e}"),
            WireError::Connection(e) => write!(f, "wire: connection lost: {e}"),
            WireError::Send(e) => write!(f, "wire: send failed: {e}"),
            WireError::Recv(e) => write!(f, "wire: recv failed: {e}"),
        }
    }
}

impl std::error::Error for WireError {}

/// The transport seam. No concrete transport types appear here.
///
/// Native async fn in trait (Rust 1.75+): the returned futures are NOT
/// automatically `Send`, so bind a concrete transport into a task via
/// a `where`-bound or `Box::pin` at the spawn site.
///
/// `bind` is meaningful for server-capable transports; a client-only
/// transport returns [`WireError::Bind`].
pub trait Transport: Send + 'static {
    /// Connection handle produced by `connect`/`accept`.
    type Conn: Conn;

    /// Start listening (server mode). Ephemeral ports (`:0`) allowed;
    /// discover the bound address via the adapter's own accessor.
    fn bind(&mut self) -> impl Future<Output = Result<(), WireError>> + Send;

    /// Connect to `addr` (`ip:port` or `host:port`), returning the
    /// established connection.
    fn connect(&self, addr: &str) -> impl Future<Output = Result<Self::Conn, WireError>> + Send;

    /// Accept the next incoming connection (server mode).
    fn accept(&mut self) -> impl Future<Output = Result<Self::Conn, WireError>> + Send;
}

/// An established connection: bidirectional streams in both directions.
pub trait Conn: Send {
    /// Open an outgoing bidirectional stream.
    fn open_bidirectional(
        &self,
    ) -> impl Future<Output = Result<(SendStream, RecvStream), WireError>> + Send;

    /// Accept an incoming bidirectional stream. The peer MUST write
    /// before this resolves (QUIC-side requirement, not a wire one).
    fn accept_bidirectional(
        &self,
    ) -> impl Future<Output = Result<(SendStream, RecvStream), WireError>> + Send;
}

// ---------------------------------------------------------------------------
// Noq adapter
// ---------------------------------------------------------------------------

use noq::ClientConfig;
use noq::Endpoint;
use noq::ServerConfig;
use noq_proto::crypto::rustls::QuicClientConfig;
use rustls::pki_types::CertificateDer;
use rustls::pki_types::PrivatePkcs8KeyDer;
use rustls::pki_types::ServerName;
use rustls::pki_types::UnixTime;

/// noq-backed [`Transport`] — the FIRST adapter (NOT the seam itself;
/// no noq types appear in the trait signatures above).
///
/// TLS: runtime-generated self-signed cert (server) + skip-verify
/// client. See the crate-level security note: dev/test ONLY.
///
/// Shapes:
/// - client-only: [`NoqTransport::client`]
/// - server: [`NoqTransport::server`], then [`Transport::bind`]
///   (client-side `connect` reuses the bound endpoint, so a server can
///   also dial out over the same UDP socket).
pub struct NoqTransport {
    /// Server bind address; `None` = client-only.
    bind_addr: Option<SocketAddr>,
    /// TLS server name the client verifies (well — would verify, see
    /// skip-verify caveat) against. Defaults to `localhost`.
    server_name: String,
    endpoint: Option<Endpoint>,
}

impl NoqTransport {
    /// Client-only transport dialing `server_name` (SNI).
    pub fn client(server_name: impl Into<String>) -> Self {
        Self {
            bind_addr: None,
            server_name: server_name.into(),
            endpoint: None,
        }
    }

    /// Server transport bound to `bind_addr` on
    /// [`Transport::bind`]. `server_name` is the SNI clients are
    /// expected to use (informational under skip-verify).
    pub fn server(bind_addr: SocketAddr, server_name: impl Into<String>) -> Self {
        Self {
            bind_addr: Some(bind_addr),
            server_name: server_name.into(),
            endpoint: None,
        }
    }

    /// The locally bound address (ephemeral-port resolution for tests
    /// and dial-back meshes). `None` before a successful bind.
    pub fn local_addr(&self) -> Option<SocketAddr> {
        self.endpoint
            .as_ref()
            .and_then(|ep| ep.local_addr().ok())
    }

    fn client_config() -> ClientConfig {
        // LOUD: accepts ANY server certificate. Dev/test loop only —
        // MITM-able by construction. See crate docs.
        let rustls_cfg = rustls::ClientConfig::builder()
            .dangerous()
            .with_custom_certificate_verifier(SkipServerVerification::new())
            .with_no_client_auth();
        ClientConfig::new(Arc::new(QuicClientConfig::try_from(rustls_cfg).expect(
            "rustls config with supported QUIC version (statically valid)",
        )))
    }

    fn server_config() -> (ServerConfig, CertificateDer<'static>) {
        let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_string()])
            .expect("self-signed cert generation (no external CA involved)");
        let cert_der = CertificateDer::from(cert.cert);
        let key_der = PrivatePkcs8KeyDer::from(cert.signing_key.serialize_der());
        let config = ServerConfig::with_single_cert(vec![cert_der.clone()], key_der.into())
            .expect("cert/key pair generated together always matches");
        (config, cert_der)
    }
}

impl Transport for NoqTransport {
    type Conn = NoqConn;

    async fn bind(&mut self) -> Result<(), WireError> {
        let bind_addr =
            self.bind_addr.ok_or_else(|| WireError::Bind("client-only transport".into()))?;
        let (server_config, _cert) = Self::server_config();
        let endpoint = Endpoint::server(server_config, bind_addr)
            .map_err(|e| WireError::Bind(e.to_string()))?;
        // Same endpoint dials out too (mesh peers call each other).
        endpoint.set_default_client_config(Self::client_config());
        self.endpoint = Some(endpoint);
        Ok(())
    }

    async fn connect(&self, addr: &str) -> Result<NoqConn, WireError> {
        let socket_addr = resolve(addr).await?;
        // Lazily create a client endpoint when this transport was
        // never bound (client-only shape).
        let owned;
        let endpoint = if let Some(ep) = &self.endpoint {
            ep
        } else {
            // Bind the client endpoint on the target's IP family (not
            // 0.0.0.0): under WSL2 mirrored networking, datagrams from
            // an unspecified-bound socket to a loopback target take a
            // different (hang-prone) path than same-IP-bound sockets.
            owned = Endpoint::client(SocketAddr::new(socket_addr.ip(), 0))
                .map_err(|e| WireError::Connect(e.to_string()))?;
            owned.set_default_client_config(Self::client_config());
            &owned
        };
        let connection = endpoint
            .connect(socket_addr, &self.server_name)
            .map_err(|e| WireError::Connect(e.to_string()))?
            .await
            .map_err(|e| WireError::Connection(e.to_string()))?;
        Ok(NoqConn { connection })
    }

    async fn accept(&mut self) -> Result<NoqConn, WireError> {
        let endpoint = self
            .endpoint
            .as_ref()
            .ok_or_else(|| WireError::Bind("accept before bind".into()))?;
        let connection = endpoint
            .accept()
            .await
            .ok_or_else(|| WireError::Bind("endpoint closed".into()))?
            .await
            .map_err(|e| WireError::Connection(e.to_string()))?;
        Ok(NoqConn { connection })
    }
}

/// `ip:port` parses directly; `host:port` resolves via the std
/// resolver (blocking — acceptable for connection setup, revisit for
/// hot reconnect loops).
async fn resolve(addr: &str) -> Result<SocketAddr, WireError> {
    if let Ok(sa) = addr.parse() {
        return Ok(sa);
    }
    let addr = addr.to_string();
    let display = addr.clone();
    let addrs = tokio::task::spawn_blocking(move || {
        std::net::ToSocketAddrs::to_socket_addrs(addr.as_str()).map(|mut i| i.next())
    })
    .await
    .map_err(|e| WireError::Connect(format!("resolver join: {e}")))?
    .map_err(|e| WireError::Connect(format!("resolve {display}: {e}")))?;
    addrs
        .ok_or_else(|| WireError::Connect(format!("resolve {display}: no addresses")))
}

/// noq-backed [`Conn`].
pub struct NoqConn {
    connection: noq::Connection,
}

impl Conn for NoqConn {
    async fn open_bidirectional(&self) -> Result<(SendStream, RecvStream), WireError> {
        let (send, recv) = self
            .connection
            .open_bi()
            .await
            .map_err(|e| WireError::Connection(e.to_string()))?;
        Ok((SendStream { inner: send }, RecvStream { inner: recv }))
    }

    async fn accept_bidirectional(&self) -> Result<(SendStream, RecvStream), WireError> {
        let (send, recv) = self
            .connection
            .accept_bi()
            .await
            .map_err(|e| WireError::Connection(e.to_string()))?;
        Ok((SendStream { inner: send }, RecvStream { inner: recv }))
    }
}

/// Byte-level send half of a bidirectional stream. Wraps the
/// adapter's stream as a private field — the public API is seam-only.
pub struct SendStream {
    inner: noq::SendStream,
}

impl SendStream {
    /// Write the whole buffer.
    pub async fn write_all(&mut self, buf: &[u8]) -> Result<(), WireError> {
        noq::SendStream::write_all(&mut self.inner, buf)
            .await
            .map_err(|e| WireError::Send(e.to_string()))
    }

    /// Signal EOF. The peer's reads complete cleanly after all buffered
    /// data. Stream is finished — further writes fail.
    pub async fn finish(&mut self) -> Result<(), WireError> {
        self.inner.finish().map_err(|e| WireError::Send(e.to_string()))
    }
}

/// Byte-level recv half of a bidirectional stream.
pub struct RecvStream {
    inner: noq::RecvStream,
}

impl RecvStream {
    /// Fill `buf` completely or fail.
    pub async fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), WireError> {
        self.inner
            .read_exact(buf)
            .await
            .map_err(|e| WireError::Recv(e.to_string()))
    }

    /// Read until EOF (peer called [`SendStream::finish`]) or
    /// `size_limit` bytes.
    pub async fn read_to_end(&mut self, size_limit: usize) -> Result<Vec<u8>, WireError> {
        self.inner
            .read_to_end(size_limit)
            .await
            .map_err(|e| WireError::Recv(e.to_string()))
    }
}

// `Endpoint` and `Connection` are cheap-handle types (Arc underneath),
// so holding one endpoint and cloning connections stays correct.
use std::sync::Arc;

/// LOUD: certificate verifier that accepts EVERYTHING. Lifted from
/// noq's `insecure_connection` example. Dev/test ONLY — MITM-able by
/// construction (see crate docs).
#[derive(Debug)]
struct SkipServerVerification(Arc<rustls::crypto::CryptoProvider>);

impl SkipServerVerification {
    fn new() -> Arc<Self> {
        Arc::new(Self(Arc::new(rustls::crypto::ring::default_provider())))
    }
}

impl rustls::client::danger::ServerCertVerifier for SkipServerVerification {
    fn verify_server_cert(
        &self,
        _end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _server_name: &ServerName<'_>,
        _ocsp: &[u8],
        _now: UnixTime,
    ) -> Result<rustls::client::danger::ServerCertVerified, rustls::Error> {
        Ok(rustls::client::danger::ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls12_signature(
            message,
            cert,
            dss,
            &self.0.signature_verification_algorithms,
        )
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(
            message,
            cert,
            dss,
            &self.0.signature_verification_algorithms,
        )
    }

    fn supported_verify_schemes(&self) -> Vec<rustls::SignatureScheme> {
        self.0.signature_verification_algorithms.supported_schemes()
    }
}

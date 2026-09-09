//! Loopback test: noq adapter over the `wire` seam, server + client on
//! localhost. Exercises bind (ephemeral port) → connect → open/accept
//! bidi → write → read → echo → read-echo.
//!
//! Loopback-address note: plain 127.0.0.1 is NOT always usable. Under
//! WSL2 mirrored networking, ALL TCP/UDP for 127/8 is routed through
//! the Windows-side proxy (ip rule priority 1: `ipproto tcp/udp
//! lookup 127` → `via 169.254.73.152 dev loopback0`); datagrams loop
//! back but the QUIC handshake never completes there (asymmetric NAT
//! on the mirror path). `10.255.255.254` — a table-local address on
//! `lo` — bypasses the mirror and behaves like real kernel loopback.
//! The test therefore runs the FULL exchange against each candidate
//! and succeeds on the first that works: 127.0.0.1 on normal Linux,
//! the bypass address under WSL2.
//!
//! Both halves run concurrently in THIS task (join!): the transport
//! owning the noq Endpoint must outlive the exchange — a task that
//! returns right after `finish()` drops the Endpoint and kills the
//! connection before the echo is readable.

use std::net::IpAddr;
use std::net::SocketAddr;
use std::time::Duration;

use wire::{Conn, NoqTransport, Transport};

/// One full loopback exchange against `host`. Errors are per-candidate
/// findings, not test failures — the caller tries the next candidate.
async fn try_exchange(host: IpAddr) -> Result<(), String> {
    let mut server = NoqTransport::server(SocketAddr::new(host, 0), "localhost");
    server.bind().await.map_err(|e| e.to_string())?;
    let server_addr = server.local_addr().ok_or("no bound address after bind")?;
    let client = NoqTransport::client("localhost");

    // Released by the client half after the echo is verified: the
    // server half must hold its Conn until then — dropping the last
    // noq Connection handle closes the connection and the client's
    // read of the echo would fail.
    let (client_done_tx, client_done_rx) = tokio::sync::oneshot::channel::<()>();

    let server_half = async {
        let conn = server.accept().await.map_err(|e| e.to_string())?;
        let (mut send, mut recv) =
            conn.accept_bidirectional().await.map_err(|e| e.to_string())?;
        // Echo: read exactly what the client sent (10 bytes), write back.
        let mut buf = [0u8; 10];
        recv.read_exact(&mut buf).await.map_err(|e| e.to_string())?;
        send.write_all(&buf).await.map_err(|e| e.to_string())?;
        send.finish().await.map_err(|e| e.to_string())?;
        // Hold the Conn until the client confirms; also hold conn
        // itself alive past this await.
        let _ = client_done_rx.await;
        drop(conn);
        Ok::<(), String>(())
    };

    let client_half = async {
        let conn = tokio::time::timeout(
            Duration::from_secs(5),
            client.connect(&server_addr.to_string()),
        )
        .await
        .map_err(|_| "connect timed out (5s)".to_string())?
        .map_err(|e| e.to_string())?;
        let (mut send, mut recv) =
            conn.open_bidirectional().await.map_err(|e| e.to_string())?;
        send.write_all(b"hello wire").await.map_err(|e| e.to_string())?;
        send.finish().await.map_err(|e| e.to_string())?;
        let echoed = recv.read_to_end(64).await.map_err(|e| e.to_string())?;
        if echoed != b"hello wire" {
            return Err(format!("echo mismatch: {echoed:?}"));
        }
        let _ = client_done_tx.send(());
        Ok::<(), String>(())
    };

    let (server_r, client_r) = tokio::time::timeout(
        Duration::from_secs(10),
        async { tokio::join!(server_half, client_half) },
    )
    .await
    .map_err(|_| "exchange timed out (10s)".to_string())?;
    server_r?;
    client_r?;
    Ok(())
}

#[tokio::test]
async fn loopback_echo() {
    // CANDIDATE 2 is WSL2-specific: only bindable when a table-local
    // address exists on lo (mirrored-networking hosts). CANDIDATE 1 is
    // universal on real Linux and tried first.
    const CANDIDATES: [IpAddr; 2] = [
        IpAddr::V4(std::net::Ipv4Addr::LOCALHOST),
        IpAddr::V4(std::net::Ipv4Addr::new(10, 255, 255, 254)),
    ];

    let mut findings = Vec::new();
    for cand in CANDIDATES {
        match try_exchange(cand).await {
            Ok(()) => return, // candidate works; done
            Err(e) => findings.push(format!("{cand}: {e}")),
        }
    }
    panic!(
        "no working loopback address for QUIC (WSL2 mirrored networking suspected); findings: {}",
        findings.join("; ")
    );
}

/// Negative-shape check: client-only transport refuses bind/accept —
/// the trait's server half degrades to an error, not a panic.
#[tokio::test]
async fn client_only_bind_is_error() {
    let mut client = NoqTransport::client("localhost");
    assert!(client.bind().await.is_err());
    assert!(client.accept().await.is_err());
}

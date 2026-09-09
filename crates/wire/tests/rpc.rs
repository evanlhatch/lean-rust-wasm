//! RPC tests: the full stack — noq transport → frames → serve/target
//! dispatch → RemoteCaller — on localhost. Three paths exercised:
//! u64 round-trip ("double"), string round-trip through the frame
//! ("greet"), and the error path (target failure → `err` frame →
//! `WireError::Remote`).
//!
//! Loopback-address note: reused verbatim from tests/loopback.rs —
//! under WSL2 mirrored networking, plain 127.0.0.1's QUIC handshake
//! can hang; `10.255.255.254` (table-local on `lo`) bypasses the
//! mirror. Each candidate runs the FULL exchange; the first that
//! works wins.

use std::net::IpAddr;
use std::net::SocketAddr;
use std::time::Duration;

use wire::NoqTransport;
use wire::Transport;
use wire::proxy::RemoteCaller;
use wire::rpc::RpcTarget;
use wire::rpc::Val;

/// The dispatch surface the server serves. Deliberately tiny: mirrors
/// what a steel-host adapter would implement over `ComponentRuntime`.
struct DemoTarget;

impl RpcTarget for DemoTarget {
    fn call(
        &self,
        func: &str,
        args: &[Val],
    ) -> impl Future<Output = Result<Vec<Val>, String>> + Send {
        async move {
            match (func, args) {
                ("double", [Val::U64(n)]) => n
                    .checked_mul(2)
                    .map(|d| vec![Val::U64(d)])
                    .ok_or_else(|| "double: overflow".to_owned()),
                ("greet", [Val::U64(1)]) => Ok(vec![Val::String("hello".to_owned())]),
                ("boom", _) => Err("boom: deliberate failure".to_owned()),
                (_, _) => Err(format!("no such function: {func}")),
            }
        }
    }
}

use std::future::Future;

/// Bind an RPC server on `host`, run [`wire::rpc::serve`] in a task,
/// return its bound address. The task owns the transport (endpoint
/// must outlive the exchange, same as the loopback test).
async fn spawn_server(host: IpAddr) -> Result<SocketAddr, String> {
    let mut transport = NoqTransport::server(SocketAddr::new(host, 0), "localhost");
    transport.bind().await.map_err(|e| e.to_string())?;
    let addr = transport.local_addr().ok_or("no bound address after bind")?;
    tokio::spawn(async move {
        let _ = wire::rpc::serve(&mut transport, std::sync::Arc::new(DemoTarget)).await;
    });
    Ok(addr)
}

/// One full RPC exchange against `host`. Errors are per-candidate
/// findings, not test failures — the caller tries the next candidate.
async fn try_exchange(host: IpAddr) -> Result<(), String> {
    let server_addr = spawn_server(host).await?;
    let client = NoqTransport::client("localhost");
    let conn = tokio::time::timeout(
        Duration::from_secs(5),
        client.connect(&server_addr.to_string()),
    )
    .await
    .map_err(|_| "connect timed out (5s)".to_string())?
    .map_err(|e| e.to_string())?;
    let mut remote = RemoteCaller::new(conn);

    // u64 round-trip: U64(21) over the wire, closure doubles, U64(42) back.
    let doubled = remote
        .call("double", &[Val::U64(21)])
        .await
        .map_err(|e| e.to_string())?;
    assert_eq!(doubled, vec![Val::U64(42)], "double(21)");

    // String round-trip: the frame's tagged-JSON string values survive.
    let greeted = remote
        .call("greet", &[Val::U64(1)])
        .await
        .map_err(|e| e.to_string())?;
    assert_eq!(greeted, vec![Val::String("hello".to_owned())], "greet(1)");

    // Error path: target failure becomes the `err` frame, preserved
    // as WireError::Remote with the message intact.
    let boom = remote
        .call("boom", &[])
        .await
        .map_err(|e| e.to_string());
    match boom {
        Err(e) => assert!(
            e.contains("boom: deliberate failure"),
            "expected remote error message, got: {e}"
        ),
        Ok(vals) => return Err(format!("boom should fail, returned {vals:?}")),
    }

    // Unknown function reports through the same error channel.
    let unknown = remote.call("nope", &[]).await.map_err(|e| e.to_string());
    match unknown {
        Err(e) => assert!(
            e.contains("no such function: nope"),
            "expected unknown-function error, got: {e}"
        ),
        Ok(vals) => return Err(format!("nope should fail, returned {vals:?}")),
    }

    // Hold the client transport until the exchange completes.
    drop(client);
    Ok(())
}

#[tokio::test]
async fn rpc_round_trip_and_error() {
    // Same candidate list + rationale as tests/loopback.rs.
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

/// Frame-level unit checks that need no network: the tagged-JSON Val
/// codec round-trips exactly (u64 precision, f64 round-trip, unicode
/// strings) and rejects malformed tags.
#[test]
fn val_codec_round_trip() {
    for val in [
        Val::U64(u64::MAX),
        Val::U64(0),
        Val::F64(0.5),
        Val::F64(f64::MIN_POSITIVE),
        Val::Bool(true),
        Val::Bool(false),
        Val::String("hello ünicode".to_owned()),
        Val::String(String::new()),
    ] {
        let json = val.to_json();
        let back = Val::from_json(&json).unwrap_or_else(|e| panic!("re-decode {json}: {e}"));
        assert_eq!(back, val, "round-trip of {val:?}");
    }

    // Exact precision claims: u64 survives as a string (JSON numbers
    // would not), f64 round-trips bit-exactly.
    assert_eq!(Val::U64(u64::MAX).to_json()["v"], u64::MAX.to_string());
    let pi = Val::F64(core::f64::consts::PI);
    assert_eq!(Val::from_json(&pi.to_json()), Ok(pi));
}

/// Malformed tagged JSON is a protocol fault, not a silent coercion.
#[test]
fn val_codec_rejects_garbage() {
    let bad: [serde_json::Value; 4] = [
        serde_json::json!({"t":"u64","v": 21}), // numeric v, not string
        serde_json::json!({"t":"i32","v":"3"}), // unknown tag
        serde_json::json!({"t":"u64"}), // missing v
        serde_json::json!(21), // not an object at all
    ];
    for v in bad {
        assert!(Val::from_json(&v).is_err(), "must reject: {v}");
    }
}

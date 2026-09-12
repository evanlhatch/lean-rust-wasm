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

/// Aggregate round-trips: option/list/record nest arbitrarily and
/// come back identical, including record FIELD ORDER (the reason
/// records use a pair array, not a JSON object — serde_json here
/// sorts object keys).
#[test]
fn val_codec_aggregates_round_trip() {
    // Covers every aggregate shape and every nesting combination:
    // list of records, option of list, record containing
    // lists/strings/u64s, deeply nested options.
    let nested = Val::List(vec![
        Val::Some(Box::new(Val::List(vec![
            Val::U64(1),
            Val::U64(u64::MAX),
        ]))),
        Val::None,
        Val::Record(vec![
            ("name".to_owned(), Val::String("zed".to_owned())),
            ("count".to_owned(), Val::U64(9)),
            ("tags".to_owned(), Val::List(vec![Val::String("a".to_owned())])),
            ("nick".to_owned(), Val::String("aaa".to_owned())),
        ]),
        Val::Some(Box::new(Val::Some(Box::new(Val::Bool(true))))),
        Val::Record(vec![]),
        Val::List(vec![]),
    ]);

    let json = nested.to_json();
    let back = Val::from_json(&json).unwrap_or_else(|e| panic!("re-decode {json}: {e}"));
    assert_eq!(back, nested, "nested aggregate round-trip");

    // Field order preserved: `name` before `nick` (a sorted-key JSON
    // object would flip them; the pair array must not).
    let record_json = serde_json::json!({"t":"record","v":[["name",{"t":"string","v":"zed"}],["nick",{"t":"string","v":"aaa"}]]});
    let decoded = Val::from_json(&record_json).unwrap_or_else(|e| panic!("decode {record_json}: {e}"));
    assert_eq!(
        decoded,
        Val::Record(vec![
            ("name".to_owned(), Val::String("zed".to_owned())),
            ("nick".to_owned(), Val::String("aaa".to_owned())),
        ]),
        "record field order must survive decode"
    );
    assert_eq!(decoded.to_json(), record_json, "encode preserves order too");

    // Depth cap sits far above any legitimate type but exists: a
    // chain of 128 `some`s decodes, 129 does not.
    let mut deep = Val::None;
    for _ in 0..MAX_DEPTH_TEST {
        deep = Val::Some(Box::new(deep));
    }
    let deep_json = deep.to_json();
    assert!(
        Val::from_json(&deep_json).is_err(),
        "nesting beyond the depth cap must fault, not recurse"
    );
}

/// Depth used by [`val_codec_aggregates_round_trip`]: just over
/// rpc.rs's `MAX_VAL_DEPTH` (kept in sync — a decode fault is
/// expected at this depth).
const MAX_DEPTH_TEST: usize = 129;

/// u64 precision survives INSIDE aggregates: a value > 2^53 (where
/// JSON numbers lose exactness) nested in a record field round-trips
/// bit-exactly because scalars travel as decimal strings.
#[test]
fn val_codec_precision_inside_aggregate() {
    let big = u64::MAX;
    let val = Val::Record(vec![
        ("amount".to_owned(), Val::U64(big)),
        ("items".to_owned(), Val::List(vec![Val::U64((1 << 53) + 1)])),
    ]);
    let json = val.to_json();
    // The wire bytes literally carry the full decimal digits.
    assert_eq!(json["v"][0][1]["v"], big.to_string());
    assert_eq!(
        Val::from_json(&json),
        Ok(val),
        "u64 > 2^53 inside a record must round-trip exactly"
    );
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

/// Malformed AGGREGATE tagged JSON: same rule, new tags. Every shape
/// deviation faults; none coerces.
#[test]
fn val_codec_rejects_aggregate_garbage() {
    let bad: [serde_json::Value; 9] = [
        serde_json::json!({"t":"some"}), // missing v
        serde_json::json!({"t":"some","v":21}), // v not a val object
        serde_json::json!({"t":"list","v":"nope"}), // v not an array
        serde_json::json!({"t":"list","v":[21]}), // element not a val object
        serde_json::json!({"t":"record","v":{"a":1}}), // v a JSON object, not a pair array
        serde_json::json!({"t":"record","v":"nope"}), // v not an array
        serde_json::json!({"t":"record","v":[["a"]]}), // entry not exactly [name, val]
        serde_json::json!({"t":"record","v":[[1,{"t":"none"}]]}), // field name not a string
        serde_json::json!({"t":"record","v":[["a",21]]}), // field value not a val object
    ];
    for v in bad {
        assert!(Val::from_json(&v).is_err(), "must reject: {v}");
    }
}

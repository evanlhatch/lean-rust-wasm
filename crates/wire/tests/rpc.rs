//! RPC tests: the full stack — noq transport → frames → serve/target
//! dispatch → RemoteCaller — on localhost. Paths exercised: u64
//! round-trip ("double"), string round-trip ("greet"), the error path
//! (target failure → `err` frame → `WireError::Remote`), plus the
//! STREAMING verb (ack → item frames → end frame): clean round-trip,
//! mid-stream failure, up-front refusal, and a rogue ack missing
//! `"stream":true` (→ Protocol).
//!
//! Loopback-address note: reused verbatim from tests/loopback.rs —
//! under WSL2 mirrored networking, plain 127.0.0.1's QUIC handshake
//! can hang; `10.255.255.254` (table-local on `lo`) bypasses the
//! mirror. Each candidate runs the FULL exchange; the first that
//! works wins.

use std::net::IpAddr;
use std::net::SocketAddr;
use std::time::Duration;

use futures_util::Stream;
use wire::Conn;
use wire::NoqTransport;
use wire::Transport;
use wire::WireError;
use wire::proxy::RemoteCaller;
use wire::rpc::RpcTarget;
use wire::rpc::Val;
use wire::rpc::decode_stream_ack;
use wire::rpc::decode_stream_frame;

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
use std::pin::Pin;

/// Bind an RPC server for `target` on `host`, run
/// [`wire::rpc::serve`] in a task, return its bound address. The task
/// owns the transport (endpoint must outlive the exchange, same as the
/// loopback test).
async fn spawn_server<R: RpcTarget + 'static>(host: IpAddr, target: R) -> Result<SocketAddr, String> {
    let mut transport = NoqTransport::server(SocketAddr::new(host, 0), "localhost");
    transport.bind().await.map_err(|e| e.to_string())?;
    let addr = transport.local_addr().ok_or("no bound address after bind")?;
    tokio::spawn(async move {
        let _ = wire::rpc::serve(&mut transport, std::sync::Arc::new(target)).await;
    });
    Ok(addr)
}

/// One full RPC exchange against `host`. Errors are per-candidate
/// findings, not test failures — the caller tries the next candidate.
async fn try_exchange(host: IpAddr) -> Result<(), String> {
    let server_addr = spawn_server(host, DemoTarget).await?;
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

// ---------------------------------------------------------------------------
// Streaming calls
// ---------------------------------------------------------------------------

/// A target that OPTS IN to streaming: `count` yields 1..=3 then ends
/// cleanly; `flaky` yields one item then fails mid-stream. Plain calls
/// refuse everything (streaming target need not also serve `call`).
struct StreamTarget;

fn boxed_stream(
    items: Vec<Result<Val, String>>,
) -> Pin<Box<dyn Stream<Item = Result<Val, String>> + Send>> {
    Box::pin(futures_util::stream::iter(items))
}

impl RpcTarget for StreamTarget {
    fn call(
        &self,
        _func: &str,
        _args: &[Val],
    ) -> impl Future<Output = Result<Vec<Val>, String>> + Send {
        async { Err("StreamTarget serves streams only".to_owned()) }
    }

    fn stream(
        &self,
        func: &str,
        _args: &[Val],
    ) -> Pin<
        Box<
            dyn Future<
                    Output = Result<Pin<Box<dyn Stream<Item = Result<Val, String>> + Send>>, String>,
                > + Send
                + '_,
        >,
    > {
        let func = func.to_owned();
        Box::pin(async move {
            match func.as_str() {
                "count" => Ok(boxed_stream(vec![
                    Ok(Val::U64(1)),
                    Ok(Val::U64(2)),
                    Ok(Val::U64(3)),
                ])),
                "flaky" => Ok(boxed_stream(vec![
                    Ok(Val::String("one".to_owned())),
                    Err("boom".to_owned()),
                ])),
                other => Err(format!("no such stream: {other}")),
            }
        })
    }}

/// One full streaming exchange against `host` (same candidate-runner
/// shape as [`try_exchange`]).
async fn try_stream_exchange(host: IpAddr) -> Result<(), String> {
    let server_addr = spawn_server(host, StreamTarget).await?;
    let client = NoqTransport::client("localhost");
    let conn = tokio::time::timeout(
        Duration::from_secs(5),
        client.connect(&server_addr.to_string()),
    )
    .await
    .map_err(|_| "connect timed out (5s)".to_string())?
    .map_err(|e| e.to_string())?;
    let mut remote = RemoteCaller::new(conn);

    // Round-trip: 3 items in order, then a clean end (None).
    let mut call = remote
        .call_streaming("count", &[])
        .await
        .map_err(|e| e.to_string())?;
    for expected in [1u64, 2, 3] {
        let item = call.next().await.map_err(|e| e.to_string())?;
        assert_eq!(item, Some(Val::U64(expected)), "stream item {expected}");
    }
    let end = call.next().await.map_err(|e| e.to_string())?;
    assert_eq!(end, None, "clean stream end");
    // Frames after `end` are a protocol violation.
    let after = call.next().await.map_err(|e| e.to_string());
    assert!(
        matches!(after, Err(ref e) if e.to_string().contains("protocol")),
        "next() after end must fault, got: {after:?}"
    );

    // Mid-stream failure: one item lands, then Remote("boom").
    let mut flaky = remote
        .call_streaming("flaky", &[])
        .await
        .map_err(|e| e.to_string())?;
    let first = flaky.next().await.map_err(|e| e.to_string())?;
    assert_eq!(first, Some(Val::String("one".to_owned())), "flaky first item");
    let boom = flaky.next().await.map_err(|e| e.to_string());
    match boom {
        Err(e) => assert!(
            e.contains("boom"),
            "expected mid-stream remote error, got: {e}"
        ),
        Ok(v) => return Err(format!("flaky should fail, got {v:?}")),
    }

    // Up-front refusal: a streaming call against a target whose
    // stream() rejects answers the plain error response; the client
    // surfaces it as Remote (message preserved), not Protocol.
    let refused = remote
        .call_streaming("no-such-stream", &[])
        .await
        .map_err(|e| e.to_string());
    match refused {
        Err(e) => assert!(
            e.contains("no such stream"),
            "expected up-front refusal, got: {e}"
        ),
        Ok(_) => return Err("no-such-stream should refuse".to_owned()),
    }

    drop(client);
    Ok(())
}

#[tokio::test]
async fn streaming_round_trip_error_and_refusal() {
    const CANDIDATES: [IpAddr; 2] = [
        IpAddr::V4(std::net::Ipv4Addr::LOCALHOST),
        IpAddr::V4(std::net::Ipv4Addr::new(10, 255, 255, 254)),
    ];

    let mut findings = Vec::new();
    for cand in CANDIDATES {
        match try_stream_exchange(cand).await {
            Ok(()) => return,
            Err(e) => findings.push(format!("{cand}: {e}")),
        }
    }
    panic!(
        "no working loopback address for QUIC (WSL2 mirrored networking suspected); findings: {}",
        findings.join("; ")
    );
}

/// Protocol garbage over the real wire: a "server" that answers a
/// streaming request with an ack-shaped frame MISSING `"stream":true`
/// must fault the client with [`WireError::Protocol`].
#[tokio::test]
async fn streaming_ack_without_stream_flag_is_protocol_error() {
    const CANDIDATES: [IpAddr; 2] = [
        IpAddr::V4(std::net::Ipv4Addr::LOCALHOST),
        IpAddr::V4(std::net::Ipv4Addr::new(10, 255, 255, 254)),
    ];

    async fn try_rogue(host: IpAddr) -> Result<(), String> {
        let mut transport = NoqTransport::server(SocketAddr::new(host, 0), "localhost");
        transport.bind().await.map_err(|e| e.to_string())?;
        let addr = transport.local_addr().ok_or("no bound address")?;
        // Leak so the endpoint outlives the exchange: dropping the
        // server Endpoint closes the connection before the client
        // reads the frame.
        let transport: &'static mut NoqTransport = Box::leak(Box::new(transport));
        tokio::spawn(async move {
            match transport.accept().await {
                Err(_) => {} // dead candidate; the runner moves on
                Ok(conn) => match conn.accept_bidirectional().await {
                    Err(_) => {} // ditto
                    Ok((mut send, _recv)) => {
                        // Deliberately WRONG ack: the plain success shape,
                        // no `"stream":true`.
                        let payload = serde_json::json!({ "id": 1, "ok": true, "vals": [] });
                        let json = serde_json::to_vec(&payload).expect("json serialize");
                        let mut frame = (json.len() as u32).to_be_bytes().to_vec();
                        frame.extend_from_slice(&json);
                        if send.write_all(&frame).await.is_err() {
                            return; // dead candidate
                        }
                        let _ = send.finish().await;
                        // Hold the conn open: dropping the server's
                        // last Connection handle tears the QUIC
                        // connection down before the client reads.
                        std::future::pending::<()>().await;
                    }
                },
            }
        });

        let client = NoqTransport::client("localhost");
        let conn = tokio::time::timeout(
            Duration::from_secs(5),
            client.connect(&addr.to_string()),
        )
        .await
        .map_err(|_| "connect timed out (5s)".to_string())?
        .map_err(|e| e.to_string())?;
        let mut remote = RemoteCaller::new(conn);
        let open = remote.call_streaming("count", &[]).await.map_err(|e| e.to_string());
        match open {
            // The good path: Protocol fault naming the stream flag.
            Err(e) if e.contains("protocol") && e.contains("stream") => Ok(()),
            // Anything else (incl. a dead 127.0.0.1 candidate) is a
            // per-candidate finding, not an assert — the runner moves on.
            Err(e) => Err(format!("expected Protocol fault, got: {e}")),
            Ok(_) => Err("rogue ack must be rejected".to_owned()),
        }
    }

    let mut findings = Vec::new();
    for cand in CANDIDATES {
        match try_rogue(cand).await {
            Ok(()) => return,
            Err(e) => findings.push(format!("{cand}: {e}")),
        }
    }
    panic!("no working loopback address for QUIC; findings: {}", findings.join("; "));
}

/// Frame-decoder unit checks (no network): ack shape, id mismatch,
/// unknown frame shapes, and the terminal frame's err forms.
#[test]
fn stream_frame_decoders_reject_garbage() {
    // Ack missing "stream":true → Protocol.
    let bytes = serde_json::to_vec(&serde_json::json!({ "id": 7, "ok": true, "vals": [] }))
        .expect("serialize");
    assert!(matches!(
        decode_stream_ack(&bytes, 7),
        Err(WireError::Protocol(_))
    ));

    // Ack with the right shape but the WRONG id → Protocol.
    let bytes = serde_json::to_vec(&serde_json::json!({ "id": 8, "ok": true, "stream": true }))
        .expect("serialize");
    assert!(matches!(
        decode_stream_ack(&bytes, 7),
        Err(WireError::Protocol(_))
    ));

    // Up-front rejection (ok:false) → Remote with the message.
    let bytes = serde_json::to_vec(&serde_json::json!({ "id": 7, "ok": false, "err": "nope" }))
        .expect("serialize");
    assert!(matches!(
        decode_stream_ack(&bytes, 7),
        Err(WireError::Remote(ref m)) if m == "nope"
    ));

    // Valid item frame round-trips; wrong-id item faults.
    let item = serde_json::json!({ "id": 7, "item": { "t": "u64", "v": "42" } });
    let bytes = serde_json::to_vec(&item).expect("serialize");
    assert!(
        matches!(decode_stream_frame(&bytes, 7), Ok(wire::rpc::StreamFrame::Item(Val::U64(42)))),
        "valid item must decode"
    );
    assert!(matches!(
        decode_stream_frame(&bytes, 8),
        Err(WireError::Protocol(_))
    ));

    // Terminal frames: err:null → End(None); err string → End(Some).
    let end = serde_json::to_vec(&serde_json::json!({ "id": 7, "end": true, "err": null }))
        .expect("serialize");
    assert!(matches!(
        decode_stream_frame(&end, 7),
        Ok(wire::rpc::StreamFrame::End(None))
    ));
    let end_err = serde_json::to_vec(&serde_json::json!({ "id": 7, "end": true, "err": "boom" }))
        .expect("serialize");
    assert!(matches!(
        decode_stream_frame(&end_err, 7),
        Ok(wire::rpc::StreamFrame::End(Some(ref m))) if m == "boom"
    ));

    // Garbage shapes → Protocol: neither item nor end; end not true;
    // err of the wrong type; item payload not a Val.
    let bad: [serde_json::Value; 4] = [
        serde_json::json!({ "id": 7, "other": true }),
        serde_json::json!({ "id": 7, "end": 1, "err": null }),
        serde_json::json!({ "id": 7, "end": true, "err": 5 }),
        serde_json::json!({ "id": 7, "item": { "t": "i32", "v": "3" } }),
    ];
    for v in &bad {
        let bytes = serde_json::to_vec(v).expect("serialize");
        assert!(
            matches!(decode_stream_frame(&bytes, 7), Err(WireError::Protocol(_))),
            "must reject: {v}"
        );
    }
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

// ── AUTH (the opt-in per-stream token handshake) ────────────────────

async fn spawn_authed_server<R: RpcTarget + 'static>(
    host: IpAddr,
    target: R,
    token: &'static str,
) -> Result<SocketAddr, String> {
    let mut transport = NoqTransport::server(SocketAddr::new(host, 0), "localhost");
    transport.bind().await.map_err(|e| e.to_string())?;
    let addr = transport.local_addr().ok_or("no bound address after bind")?;
    tokio::spawn(async move {
        let _ = wire::rpc::serve_authed(&mut transport, std::sync::Arc::new(target), token).await;
    });
    Ok(addr)
}

/// The AUTH handshake on the raw-frame level: the client opens the
/// stream and sends the auth-frame FIRST; the server's gate checks it
/// (constant-time) before any request is read. The wire-level client
/// API = the follow-up; these tests pin the PROTOCOL.
async fn auth_good_token_passes_at(host: IpAddr) -> Result<(), String> {
    let server_addr = spawn_authed_server(host, DemoTarget, "s3cret")
        .await
        .map_err(|e| format!("server: {e}"))?;
    let client = NoqTransport::client("localhost");
    let conn = tokio::time::timeout(
        Duration::from_secs(5),
        client.connect(&server_addr.to_string()),
    )
    .await
    .map_err(|_| "connect: timeout".to_string())?
    .map_err(|e| format!("connect: {e}"))?;
    let (mut send, mut recv) = conn.open_bidirectional().await.map_err(|e| format!("stream: {e}"))?;

    // the handshake: the auth-frame FIRST
    send.write_all(&wire::rpc::encode_auth("s3cret").unwrap())
        .await
        .unwrap();
    // then the request — the normal flow
    send.write_all(
        &wire::rpc::encode_frame(&serde_json::json!({
            "id": 1u64, "fn": "double", "args": [{"t": "u64", "v": "21"}]
        }))
        .unwrap(),
    )
    .await
    .unwrap();
    let reply = tokio::time::timeout(Duration::from_secs(5), wire::rpc::read_frame(&mut recv))
        .await
        .expect("reply")
        .expect("reply frame");
    let v: serde_json::Value = serde_json::from_slice(&reply).unwrap();
    assert_eq!(v["id"], 1u64);
    assert_eq!(v["ok"], true);

    Ok(())
}

#[tokio::test]
async fn auth_good_token_passes() {
    const CANDIDATES: [IpAddr; 2] = [
        IpAddr::V4(std::net::Ipv4Addr::LOCALHOST),
        IpAddr::V4(std::net::Ipv4Addr::new(10, 255, 255, 254)),
    ];
    let mut findings = Vec::new();
    for cand in CANDIDATES {
        if let Err(e) = auth_good_token_passes_at(cand).await {
            findings.push(format!("{cand}: {e}"));
        } else {
            return; // candidate works; done
        }
    }
    panic!("auth_good_token_passes: no candidate worked: {findings:?}");
}
async fn auth_bad_token_refused_at(host: IpAddr) -> Result<(), String> {
    let server_addr = spawn_authed_server(host, DemoTarget, "s3cret")
        .await
        .map_err(|e| format!("server: {e}"))?;
    let client = NoqTransport::client("localhost");
    let conn = tokio::time::timeout(
        Duration::from_secs(5),
        client.connect(&server_addr.to_string()),
    )
    .await
    .map_err(|_| "connect: timeout".to_string())?
    .map_err(|e| format!("connect: {e}"))?;
    let (mut send, mut recv) = conn.open_bidirectional().await.map_err(|e| format!("stream: {e}"))?;

    // the WRONG token: one error frame, then the stream dies — the
    // request (even a valid one) is never read
    send.write_all(&wire::rpc::encode_auth("wrong").unwrap())
        .await
        .unwrap();
    send.write_all(
        &wire::rpc::encode_frame(&serde_json::json!({
            "id": 1u64, "fn": "double", "args": [{"t": "u64", "v": "21"}]
        }))
        .unwrap(),
    )
    .await
    .unwrap();
    let reply = tokio::time::timeout(Duration::from_secs(5), wire::rpc::read_frame(&mut recv))
        .await
        .expect("the refusal frame")
        .expect("refusal frame");
    let v: serde_json::Value = serde_json::from_slice(&reply).unwrap();
    assert_eq!(v["ok"], false);
    assert!(
        v["err"].as_str().unwrap().contains("auth"),
        "the refusal names the reason: {v}"
    );
    // the NEGATIVE half: no second frame — the gate KILLED the stream
    // the stream's dead = the read's Err — EITHER the timeout OR the
    // finished-early (the server dropped the stream after the refusal)
    let next = tokio::time::timeout(Duration::from_millis(500), wire::rpc::read_frame(&mut recv))
        .await;
    assert!(
        matches!(next, Err(_) | Ok(Err(_))),
        "the stream must die after the refusal (got {next:?})"
    );

    Ok(())
}

#[tokio::test]
async fn auth_bad_token_refused() {
    const CANDIDATES: [IpAddr; 2] = [
        IpAddr::V4(std::net::Ipv4Addr::LOCALHOST),
        IpAddr::V4(std::net::Ipv4Addr::new(10, 255, 255, 254)),
    ];
    let mut findings = Vec::new();
    for cand in CANDIDATES {
        if let Err(e) = auth_bad_token_refused_at(cand).await {
            findings.push(format!("{cand}: {e}"));
        } else {
            return; // candidate works; done
        }
    }
    panic!("auth_bad_token_refused: no candidate worked: {findings:?}");
}
async fn auth_absent_token_refused_at(host: IpAddr) -> Result<(), String> {
    let server_addr = spawn_authed_server(host, DemoTarget, "s3cret")
        .await
        .map_err(|e| format!("server: {e}"))?;
    let client = NoqTransport::client("localhost");
    let conn = tokio::time::timeout(
        Duration::from_secs(5),
        client.connect(&server_addr.to_string()),
    )
    .await
    .map_err(|_| "connect: timeout".to_string())?
    .map_err(|e| format!("connect: {e}"))?;
    let (mut send, mut recv) = conn.open_bidirectional().await.map_err(|e| format!("stream: {e}"))?;

    // NO auth frame: the request goes straight in — the gate reads the
    // first frame AS the auth (the request's JSON has no "auth" key =
    // not presented = refused)
    send.write_all(
        &wire::rpc::encode_frame(&serde_json::json!({
            "id": 1u64, "fn": "double", "args": [{"t": "u64", "v": "21"}]
        }))
        .unwrap(),
    )
    .await
    .unwrap();
    let reply = tokio::time::timeout(Duration::from_secs(5), wire::rpc::read_frame(&mut recv))
        .await
        .expect("the refusal frame")
        .expect("refusal frame");
    let v: serde_json::Value = serde_json::from_slice(&reply).unwrap();
    assert_eq!(v["ok"], false);
    assert!(v["err"].as_str().unwrap().contains("auth"));

    Ok(())
}

#[tokio::test]
async fn auth_absent_token_refused() {
    const CANDIDATES: [IpAddr; 2] = [
        IpAddr::V4(std::net::Ipv4Addr::LOCALHOST),
        IpAddr::V4(std::net::Ipv4Addr::new(10, 255, 255, 254)),
    ];
    let mut findings = Vec::new();
    for cand in CANDIDATES {
        if let Err(e) = auth_absent_token_refused_at(cand).await {
            findings.push(format!("{cand}: {e}"));
        } else {
            return; // candidate works; done
        }
    }
    panic!("auth_absent_token_refused: no candidate worked: {findings:?}");
}

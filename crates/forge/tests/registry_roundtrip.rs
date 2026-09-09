//! Registry round-trip: pack → push → pull → byte-identity.
//!
//! The registry is a MINIMAL hand-rolled HTTP/1.1 server on a std
//! TcpListener (no deps): request line + headers + Content-Length body
//! parsing, five routes (blob upload POST/PUT, manifest PUT, manifest
//! GET, blob GET). Serves on 127.0.0.1:0 (ephemeral port), one request
//! per connection (`Connection: close`), std + threads only.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use forge::oci::{Digest, OciStore, sha256_hex};

const MANIFEST_MEDIA_TYPE: &str = "application/vnd.oci.image.manifest.v1+json";
const LABEL: &str = "lean/wasm-backend/target/demo.component.wasm";

struct Shared {
    /// "sha256:<hex>" → blob bytes
    blobs: Mutex<HashMap<String, Vec<u8>>>,
    /// tag → manifest bytes
    manifests: Mutex<HashMap<String, Vec<u8>>>,
}

/// Some sandboxed environments sever loopback TCP (connect succeeds,
/// data never flows) while leaving real interfaces alone. Probe
/// loopback; if it's dead, fall back to the primary local IPv4.
fn probe_http(host: &str) -> bool {
    let listener = match TcpListener::bind((host, 0)) {
        Ok(l) => l,
        Err(_) => return false,
    };
    let port = listener.local_addr().unwrap().port();
    listener.set_nonblocking(true).unwrap();
    let server = thread::spawn(move || {
        // Bounded accept: a severed path must not wedge the probe.
        let deadline = Instant::now() + Duration::from_secs(4);
        loop {
            match listener.accept() {
                Ok((mut s, _)) => {
                    let _ = s.set_read_timeout(Some(Duration::from_secs(2)));
                    let mut buf = [0u8; 4];
                    let _ = s.read(&mut buf);
                    let _ = s.write_all(b"ok");
                    break;
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    if Instant::now() > deadline {
                        break;
                    }
                    thread::sleep(Duration::from_millis(20));
                }
                Err(_) => break,
            }
        }
    });
    let addr = SocketAddr::new(host.parse().expect("probe host must be an IP"), port);
    let ok = (|| -> Option<()> {
        let mut s = TcpStream::connect_timeout(&addr, Duration::from_secs(2)).ok()?;
        s.set_read_timeout(Some(Duration::from_secs(2))).ok()?;
        s.set_write_timeout(Some(Duration::from_secs(2))).ok()?;
        s.write_all(b"ping").ok()?;
        let mut buf = [0u8; 2];
        s.read_exact(&mut buf).ok()?;
        Some(())
    })()
    .is_some();
    server.join().ok();
    ok
}

fn http_host() -> String {
    if probe_http("127.0.0.1") {
        return "127.0.0.1".to_string();
    }
    // Route-free local-address discovery: a UDP "connect" to a public
    // endpoint sends no packets but resolves the primary source IP.
    let sock = std::net::UdpSocket::bind("0.0.0.0:0").unwrap();
    let ip = sock
        .connect("8.8.8.8:80")
        .ok()
        .and_then(|()| sock.local_addr().ok())
        .map(|a| a.ip().to_string())
        .unwrap_or_else(|| panic!("no loopback or local address available for the registry test"));
    assert!(probe_http(&ip), "neither 127.0.0.1 nor {ip} carry TCP — cannot run the registry test");
    ip
}

fn serve(listener: TcpListener, shared: Arc<Shared>) {
    for stream in listener.incoming() {
        match stream {
            Ok(s) => {
                let _ = handle_conn(s, &shared);
            }
            Err(_) => break,
        }
    }
}

fn handle_conn(mut stream: TcpStream, shared: &Shared) -> std::io::Result<()> {
    let (head, body) = read_request(&mut stream)?;
    let request_line = head.lines().next().unwrap_or_default();
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or_default().to_string();
    let target = parts.next().unwrap_or_default().to_string();
    let (path, query) = match target.split_once('?') {
        Some((p, q)) => (p.to_string(), q.to_string()),
        None => (target, String::new()),
    };

    if method == "POST" && path.ends_with("/blobs/uploads/") {
        let repo = path
            .trim_start_matches("/v2/")
            .trim_end_matches("/blobs/uploads/");
        let location = format!("/v2/{repo}/blobs/uploads/test-upload-1");
        respond(
            &mut stream,
            "202 Accepted",
            None,
            b"",
            &format!("Location: {location}\r\n"),
        )
    } else if method == "PUT" && path.contains("/blobs/uploads/") {
        let digest = query
            .split('&')
            .find_map(|kv| kv.strip_prefix("digest="))
            .unwrap_or_default()
            .to_string();
        shared.blobs.lock().unwrap().insert(digest, body);
        respond(&mut stream, "201 Created", None, b"", "")
    } else if method == "PUT" && path.contains("/manifests/") {
        let tag = path.rsplit('/').next().unwrap_or_default().to_string();
        shared.manifests.lock().unwrap().insert(tag, body);
        respond(&mut stream, "201 Created", None, b"", "")
    } else if method == "GET" && path.contains("/manifests/") {
        let tag = path.rsplit('/').next().unwrap_or_default().to_string();
        match shared.manifests.lock().unwrap().get(&tag) {
            Some(m) => respond(&mut stream, "200 OK", Some(MANIFEST_MEDIA_TYPE), m, ""),
            None => respond(&mut stream, "404 Not Found", None, b"no such manifest", ""),
        }
    } else if method == "GET" && path.contains("/blobs/") {
        let digest = path.rsplit('/').next().unwrap_or_default().to_string();
        match shared.blobs.lock().unwrap().get(&digest) {
            Some(b) => respond(&mut stream, "200 OK", Some("application/octet-stream"), b, ""),
            None => respond(&mut stream, "404 Not Found", None, b"no such blob", ""),
        }
    } else {
        respond(&mut stream, "404 Not Found", None, b"unrouted", "")
    }
}

/// Read one request: head through \r\n\r\n, then Content-Length bytes of body.
fn read_request(stream: &mut TcpStream) -> std::io::Result<(String, Vec<u8>)> {
    let mut buf = Vec::new();
    let mut chunk = [0u8; 4096];
    let head_end = loop {
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "eof in request head",
            ));
        }
        buf.extend_from_slice(&chunk[..n]);
        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break pos;
        }
    };
    let head = String::from_utf8_lossy(&buf[..head_end]).to_string();
    let content_length = head
        .to_ascii_lowercase()
        .lines()
        .find_map(|l| l.strip_prefix("content-length:"))
        .and_then(|v| v.trim().parse::<usize>().ok())
        .unwrap_or(0);
    let mut body: Vec<u8> = buf[head_end + 4..].to_vec();
    while body.len() < content_length {
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&chunk[..n]);
    }
    body.truncate(content_length);
    Ok((head, body))
}

fn respond(
    stream: &mut TcpStream,
    status: &str,
    content_type: Option<&str>,
    body: &[u8],
    extra_headers: &str,
) -> std::io::Result<()> {
    let mut head = format!(
        "HTTP/1.1 {status}\r\nContent-Length: {}\r\nConnection: close\r\n",
        body.len()
    );
    if let Some(ct) = content_type {
        head.push_str(&format!("Content-Type: {ct}\r\n"));
    }
    head.push_str(extra_headers);
    head.push_str("\r\n");
    stream.write_all(head.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

#[test]
fn push_pull_roundtrip() {
    // ── start the minimal registry on an ephemeral port ─────────────
    let host = http_host();
    let listener = TcpListener::bind((host.as_str(), 0)).unwrap();
    let port = listener.local_addr().unwrap().port();
    let shared = Arc::new(Shared {
        blobs: Mutex::new(HashMap::new()),
        manifests: Mutex::new(HashMap::new()),
    });
    let srv_shared = shared.clone();
    thread::spawn(move || serve(listener, srv_shared));

    // ── pack a real artifact if it exists, else a synthetic blob ────
    let demo = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/wasm-backend/target/demo.component.wasm");
    let artifact = if demo.exists() {
        std::fs::read(&demo).unwrap()
    } else {
        eprintln!("demo.component.wasm not built — using synthetic blob");
        (0..4096u32).map(|i| (i % 251) as u8).collect()
    };

    let dir = std::env::temp_dir().join(format!("forge-registry-test-{}", std::process::id()));
    let mut store = OciStore::open(&dir.join("oci")).unwrap();
    let original_digest: Digest = store.put(LABEL, &artifact).unwrap();
    store.write_index().unwrap();

    let mut m = forge::manifest::pack(&mut store, LABEL).unwrap();
    assert_eq!(m.layers[0].digest, original_digest, "pack must reuse the stored digest");
    assert_eq!(
        m.annotations.get("com.guestlang.axioms").map(String::as_str),
        Some("clean"),
        "axiom provenance annotation"
    );
    assert_eq!(
        m.annotations.get("org.opencontainers.image.ref.name").map(String::as_str),
        Some(LABEL),
        "label annotation"
    );

    // ── push: blobs then manifest ────────────────────────────────────
    let target = format!("{host}:{port}/guestlang/test:v1");
    let (reg, tag) = forge::registry::Registry::parse(&target).unwrap();
    assert_eq!(tag, "v1");
    let blobs = vec![
        store.blob_path(&m.config.digest),
        store.blob_path(&m.layers[0].digest),
    ];
    reg.push(&tag, &m, &blobs).unwrap();

    // Server holds both blobs under their sha256 digests.
    {
        let blobs = shared.blobs.lock().unwrap();
        assert_eq!(
            blobs.get(&format!("sha256:{original_digest}")).map(Vec::as_slice),
            Some(artifact.as_slice()),
            "layer blob arrived byte-identical"
        );
        assert!(blobs.contains_key(&format!("sha256:{}", m.config.digest)), "config blob arrived");
    }
    // Server holds the manifest, well-formed.
    let served_manifest = shared.manifests.lock().unwrap().get("v1").cloned();
    let served_manifest = served_manifest.expect("manifest arrived");
    let served: serde_json::Value = serde_json::from_slice(&served_manifest).unwrap();
    assert_eq!(served["schemaVersion"], 2);
    assert_eq!(served["mediaType"], MANIFEST_MEDIA_TYPE);
    assert_eq!(served["config"]["mediaType"], "application/vnd.oci.image.config.v1+json");
    assert_eq!(served["layers"][0]["mediaType"], "application/wasm");

    // ── pull into a fresh store; byte-identity ───────────────────────
    let mut dst = OciStore::open(&dir.join("dst-oci")).unwrap();
    let pulled = reg.pull("v1", &mut dst, &dir).unwrap();
    assert_eq!(pulled.manifest.label, LABEL);
    assert_eq!(pulled.artifacts.len(), 1);
    assert_eq!(pulled.artifacts[0].1, original_digest, "pulled digest matches original");
    assert_eq!(pulled.artifacts[0].2, artifact, "pulled bytes match original");

    let landed = std::fs::read(dir.join(LABEL)).unwrap();
    assert_eq!(landed, artifact, "materialized artifact byte-identical");
    assert_eq!(sha256_hex(&landed), original_digest, "materialized sha256 matches");
    assert_eq!(dst.get(&original_digest).unwrap(), artifact, "store blob byte-identical");

    // Tamper control: flip one byte in the served manifest's layer
    // digest and the pull must fail loudly (digest = security boundary).
    m.layers[0].digest = "0".repeat(64);
    let bad_raw = m.to_bytes();
    shared
        .manifests
        .lock()
        .unwrap()
        .insert("bad".to_string(), bad_raw);
    let err = reg.pull("bad", &mut OciStore::open(&dir.join("dst2")).unwrap(), &dir);
    assert!(err.is_err(), "tampered manifest must fail the pull");

    let _ = std::fs::remove_dir_all(&dir);
}

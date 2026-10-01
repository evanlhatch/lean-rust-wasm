//! The store's teeth (design-wave-30 D5): the round-trip identity, the
//! tamper refusals, the provenance-honesty controls. Hermetic — every
//! store lives in a fresh temp dir under target/.

use mandate_store::digest::{is_valid_digest, sha256_hex};
use mandate_store::prov::{self, Provenance};
use mandate_store::store::{CONFIG_JSON, MANIFEST_MT};
use mandate_store::{Artifact, Refusal, Store, StoreError, Verify};
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

static N: AtomicU32 = AtomicU32::new(0);

/// A fresh store root under target/ (never the tree's artifacts).
fn fresh_root(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "{}-{}",
        name,
        N.fetch_add(1, Ordering::SeqCst)
    ));
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn refusal_of(err: &StoreError) -> &Refusal {
    match err {
        StoreError::Refusal(r) => r,
        StoreError::Io(e) => panic!("unexpected io error: {e}"),
    }
}

/// A provenance CONSISTENT with `data` (the honest writer's shape).
fn prov_for(label: &str, data: &[u8]) -> Provenance {
    Provenance {
        label: label.into(),
        axiom_report_sha256: sha256_hex(b"axiom-report-v1"),
        gates_reports: vec![("notes/axiom-report.md".into(), b"axiom-report-v1".to_vec())],
        ledger_hash: sha256_hex(data),
    }
}

const WIT: &str = "package mandate:slice;\nworld slice { export answer: func() -> u64; }\n";

/// An attacker-rebuilt index pointing at a hand-made manifest.
fn repoint_index(root: &PathBuf, manifest_bytes: &[u8], label: &str) {
    let md = sha256_hex(manifest_bytes);
    fs::write(root.join("blobs/sha256").join(&md), manifest_bytes).unwrap();
    let index = serde_json::json!({
        "schemaVersion": 2,
        "manifests": [{
            "mediaType": MANIFEST_MT,
            "digest": format!("sha256:{md}"),
            "size": manifest_bytes.len(),
            "annotations": {"org.opencontainers.image.ref.name": label}
        }]
    });
    fs::write(root.join("index.json"), index.to_string()).unwrap();
}

#[test]
fn round_trip_is_identity() {
    let root = fresh_root("round-trip");
    let mut store = Store::open(&root).unwrap();
    let data = WIT.as_bytes();
    let stored = store
        .put(&prov_for("gen/component-slice.wit", data), data)
        .unwrap();

    // The stored digest IS the content address.
    assert_eq!(stored, sha256_hex(data));
    assert!(is_valid_digest(&stored));

    let artifact: Artifact = store.read("gen/component-slice.wit").unwrap();
    assert_eq!(artifact.data, data); // store → read ≡ identity
    assert_eq!(artifact.digest, stored);

    // The badges landed, composed by the one writer.
    let ann = &artifact.annotations;
    assert_eq!(ann[prov::GATES].as_str().unwrap(), "green");
    assert_eq!(
        ann[prov::AXIOM_REPORT].as_str().unwrap(),
        format!("sha256:{}", sha256_hex(b"axiom-report-v1"))
    );
    assert_eq!(
        ann[prov::LEDGER_HASH].as_str().unwrap(),
        format!("sha256:{stored}")
    );

    // The layout is image-spec-shaped: oci-layout + index + blob.
    assert!(root.join("oci-layout").exists());
    assert!(root.join("index.json").exists());
    assert!(root.join("blobs/sha256").join(&stored).exists());
}

#[test]
fn reopen_preserves_tags() {
    let root = fresh_root("reopen");
    let data = b"duel manifest bytes";
    {
        let mut store = Store::open(&root).unwrap();
        store
            .put(&prov_for("gen/wasm-duel/manifest.txt", data), data)
            .unwrap();
    }
    let store = Store::open(&root).unwrap();
    assert_eq!(store.read("gen/wasm-duel/manifest.txt").unwrap().data, data);
}

#[test]
fn tampered_blob_refuses() {
    let root = fresh_root("tamper");
    let mut store = Store::open(&root).unwrap();
    let data = b"wasm component bytes";
    let digest = store
        .put(&prov_for("gen/component-slice.wasm", data), data)
        .unwrap();
    drop(store);

    // Flip one byte in the layer blob.
    let blob = root.join("blobs/sha256").join(&digest);
    let mut bytes = fs::read(&blob).unwrap();
    bytes[0] ^= 0xff;
    fs::write(&blob, &bytes).unwrap();

    let store = Store::open(&root).unwrap();
    let err = store.read("gen/component-slice.wasm").unwrap_err();
    match refusal_of(&err) {
        Refusal::HashMismatch {
            digest: d, actual, ..
        } => {
            assert_eq!(d, &digest);
            assert_ne!(actual, &digest);
        }
        other => panic!("expected HashMismatch, got {other:?}"),
    }
    // The report renders the refusal (refuse-with-report).
    let report = refusal_of(&err).report();
    assert!(report.starts_with("REFUSED"), "{report}");
    assert!(report.contains("tampered"), "{report}");
}

#[test]
fn lying_ledger_row_refuses_at_put() {
    let root = fresh_root("ledger-mismatch");
    let mut store = Store::open(&root).unwrap();
    let data = b"artifact";
    let mut p = prov_for("gen/component-slice.wit", data);
    p.ledger_hash = sha256_hex(b"different-bytes"); // the ledger's lie
    let err = store.put(&p, data).unwrap_err();
    match refusal_of(&err) {
        Refusal::LedgerMismatch { declared, actual } => {
            assert_eq!(declared, &sha256_hex(b"different-bytes"));
            assert_eq!(actual, &sha256_hex(data));
        }
        other => panic!("expected LedgerMismatch, got {other:?}"),
    }
    // Nothing was written: the refusal fires before the filesystem.
    assert!(!root.join("blobs/sha256").join(sha256_hex(data)).exists());
}

#[test]
fn missing_provenance_refuses() {
    let root = fresh_root("missing-prov");
    let mut store = Store::open(&root).unwrap();
    let data = b"artifact";
    store
        .put(&prov_for("gen/component-slice.wit", data), data)
        .unwrap();
    drop(store);

    // An attacker rebuilds the manifest WITHOUT the badges and
    // re-points the index at it. The layer bytes still hash true —
    // the provenance SHAPE is what refuses.
    let manifest = serde_json::json!({
        "schemaVersion": 2,
        "mediaType": MANIFEST_MT,
        "config": {
            "mediaType": mandate_store::store::CONFIG_MT,
            "digest": format!("sha256:{}", sha256_hex(CONFIG_JSON)),
            "size": CONFIG_JSON.len()
        },
        "layers": [{
            "mediaType": mandate_store::store::ARTIFACT_MT,
            "digest": format!("sha256:{}", sha256_hex(data)),
            "size": data.len(),
            "annotations": {}
        }],
        "annotations": {}
    });
    let manifest_bytes = manifest.to_string().into_bytes();
    repoint_index(&root, &manifest_bytes, "gen/component-slice.wit");

    let store = Store::open(&root).unwrap();
    let err = store.read("gen/component-slice.wit").unwrap_err();
    let report = refusal_of(&err).report();
    assert!(report.contains("REFUSED provenance"), "{report}");
    assert!(report.contains("missing"), "{report}");
}

#[test]
fn not_green_stamp_refuses() {
    // A manifest stamped with something other than `green` refuses —
    // an artifact stored without a green gates run is unread.
    let root = fresh_root("not-green");
    let mut store = Store::open(&root).unwrap();
    let data = b"artifact";
    store
        .put(&prov_for("gen/component-slice.wit", data), data)
        .unwrap();
    drop(store);

    let layer = sha256_hex(data);
    let manifest = serde_json::json!({
        "schemaVersion": 2, "mediaType": MANIFEST_MT,
        "config": {
            "mediaType": mandate_store::store::CONFIG_MT,
            "digest": format!("sha256:{}", sha256_hex(CONFIG_JSON)),
            "size": CONFIG_JSON.len()
        },
        "layers": [{
            "mediaType": mandate_store::store::ARTIFACT_MT,
            "digest": format!("sha256:{layer}"), "size": data.len()
        }],
        "annotations": {
            "org.opencontainers.image.ref.name": "gen/component-slice.wit",
            "dev.mandate.prov.axiom-report": format!("sha256:{}", sha256_hex(b"axiom-report-v1")),
            "dev.mandate.prov.gates": "red",
            "dev.mandate.prov.gates-stamp": format!("sha256:{}", sha256_hex(b"axiom-report-v1")),
            "dev.mandate.prov.ledger-hash": format!("sha256:{layer}")
        }
    });
    repoint_index(
        &root,
        &manifest.to_string().as_bytes(),
        "gen/component-slice.wit",
    );

    let store = Store::open(&root).unwrap();
    let err = store.read("gen/component-slice.wit").unwrap_err();
    let report = refusal_of(&err).report();
    assert!(report.contains("`red` is not `green`"), "{report}");
}

#[test]
fn stale_axiom_badge_refuses() {
    let root = fresh_root("stale");
    let mut store = Store::open(&root).unwrap();
    let data = b"artifact";
    store
        .put(&prov_for("gen/component-slice.wit", data), data)
        .unwrap();

    // The gates ran again: the live report's content moved.
    let live = b"axiom-report-v2";
    let err = store
        .read_fresh("gen/component-slice.wit", live)
        .unwrap_err();
    let report = refusal_of(&err).report();
    assert!(report.contains("stale"), "{report}");
    assert!(report.contains(&sha256_hex(b"axiom-report-v1")), "{report}");
    assert!(report.contains(&sha256_hex(live)), "{report}");

    // And the honest path: same report → fresh read passes.
    store
        .read_fresh("gen/component-slice.wit", b"axiom-report-v1")
        .unwrap();
}

#[test]
fn unknown_label_refuses() {
    let root = fresh_root("unknown");
    let store = Store::open(&root).unwrap();
    let err = store.read("gen/never-stored.wit").unwrap_err();
    let report = refusal_of(&err).report();
    assert!(report.contains("no artifact stored"), "{report}");
}

#[test]
fn verify_file_byte_tie() {
    let root = fresh_root("byte-tie");
    let mut store = Store::open(&root).unwrap();
    let data = WIT.as_bytes();
    store
        .put(&prov_for("gen/component-slice.wit", data), data)
        .unwrap();

    let file = fresh_root("byte-tie-file").join("component-slice.wit");
    fs::write(&file, data).unwrap();
    assert_eq!(
        store.verify_file("gen/component-slice.wit", &file).unwrap(),
        Verify::Match
    );

    fs::write(&file, b"drifted bytes").unwrap();
    assert!(matches!(
        store.verify_file("gen/component-slice.wit", &file).unwrap(),
        Verify::Mismatch { .. }
    ));
    assert_eq!(
        store.verify_file("gen/absent.wit", &file).unwrap(),
        Verify::NotStored
    );
}

#[test]
fn list_reports_stored_rows() {
    let root = fresh_root("list");
    let mut store = Store::open(&root).unwrap();
    for (label, data) in [
        ("gen/component-slice.wit", WIT.as_bytes()),
        ("gen/component-slice.wasm", b"wasm".as_slice()),
    ] {
        store.put(&prov_for(label, data), data).unwrap();
    }
    let rows = store.list();
    assert_eq!(rows.len(), 2);
    let wit = rows
        .iter()
        .find(|r| r.label == "gen/component-slice.wit")
        .unwrap();
    assert_eq!(wit.layer_digest, sha256_hex(WIT.as_bytes()));
    assert_eq!(wit.axiom_report, sha256_hex(b"axiom-report-v1"));

    // The stamp is order-independent in the reports' set.
    let a = prov::gates_stamp(&[("a".into(), b"1".to_vec()), ("b".into(), b"2".to_vec())]);
    let b = prov::gates_stamp(&[("b".into(), b"2".to_vec()), ("a".into(), b"1".to_vec())]);
    assert_eq!(a, b);
}

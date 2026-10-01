//! The tree's OWN artifacts through the store: the gen/ faces (the
//! wasm components, the WIT worlds, the duel manifest) round-trip and
//! byte-tie. The byte-tie's consumer side: the store's digest over the
//! committed bytes must be stable across runs — a drifted gen/ file
//! shows up as a Mismatch (the gates' gen-check owns the writer side).

use mandate_store::digest::sha256_hex;
use mandate_store::prov::Provenance;
use mandate_store::{Store, Verify};
use std::fs;
use std::path::{Path, PathBuf};

/// The tree root from this crate's dir (tests run from the crate).
fn tree_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

fn store_gen(store: &mut Store, rel: &str, data: &[u8]) -> String {
    let p = Provenance {
        label: rel.to_string(),
        axiom_report_sha256: sha256_hex(b"gen-test-report"),
        gates_reports: vec![("gen-test".into(), b"gen-test".to_vec())],
        ledger_hash: sha256_hex(data),
    };
    store.put(&p, data).unwrap()
}

#[test]
fn gen_artifacts_round_trip_and_byte_tie() {
    let root = tree_root();
    let artifacts: Vec<&str> = vec![
        "gen/component-slice.wasm",
        "gen/component-slice.wit",
        "gen/wasm-duel/manifest.txt",
    ];
    let store_root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("gen-store");
    let _ = fs::remove_dir_all(&store_root);
    let mut store = Store::open(&store_root).unwrap();

    for rel in &artifacts {
        let data = fs::read(root.join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"));
        let digest = store_gen(&mut store, rel, &data);
        assert_eq!(
            digest,
            sha256_hex(&data),
            "{rel}: the digest is the content address"
        );

        // Round-trip: store → read ≡ identity over the committed bytes.
        let artifact = store.read(rel).unwrap();
        assert_eq!(artifact.data, data, "{rel}");
        assert_eq!(
            artifact.annotations[mandate_store::prov::GATES].as_str(),
            Some("green")
        );

        // Byte-tie: the file on disk still matches the store.
        assert_eq!(
            store.verify_file(rel, &root.join(rel)).unwrap(),
            Verify::Match,
            "{rel}: the committed bytes must tie to the store's"
        );
    }

    // The query face sees the tree's artifact set.
    let rows = store.list();
    assert_eq!(rows.len(), artifacts.len());
    for rel in &artifacts {
        assert!(
            rows.iter().any(|r| r.label == *rel),
            "{rel} missing from list"
        );
    }
}

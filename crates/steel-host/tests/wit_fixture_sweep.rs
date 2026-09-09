//! WIT inversion sweep — `parse (emit u) ≅ u` over GENERATED universes.
//!
//! Stage F's `wit_roundtrip.rs` parses ONE generated WIT (the demo
//! universe). This test generalizes toward the theorem shape: schema-lang's
//! `WitFixture` emitter emits a DETERMINISTIC SET of universes (scalars /
//! nesting / variants / async) as WIT fixtures plus a JSON manifest of each
//! universe's structure — Lean's view. Here we parse every fixture with
//! wit-parser — an INDEPENDENT parser, not the Lean printer — and assert
//! the resolved structure equals the manifest.
//!
//! Everything (fixtures + manifest) is byte-tied: drift fails CI before
//! this test even runs.

use std::path::{Path, PathBuf};

use wit_parser::{Resolve, TypeDefKind};

/// The fixtures directory, relative to this crate.
fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// Fail loud, fail clear (workspace denies clippy::panic; tests excepted).
#[track_caller]
#[allow(clippy::panic, reason = "test helper: fail loud, fail clear")]
fn fail(msg: &str) -> ! {
    panic!("{msg}");
}

use serde_json::Value;

/// One manifest entry: Lean's view of a fixture universe (navigated as a
/// `serde_json::Value` — serde's derive feature isn't a dep here).
struct FixtureManifest {
    fixture: String,
    types: Vec<TypeEntry>,
    funcs: Vec<FuncEntry>,
}

struct TypeEntry {
    name: String,
    kind: String, // "record" | "variant" (wit-parser TypeDefKind names)
    fields: Vec<String>,
    cases: Vec<String>,
}

struct FuncEntry {
    name: String,
    params: Vec<String>,
}

fn strings(v: &Value, key: &str) -> Vec<String> {
    v[key]
        .as_array()
        .map(|a| {
            a.iter()
                .map(|s| s.as_str().unwrap_or_default().to_string())
                .collect()
        })
        .unwrap_or_default()
}

/// Load + strip the GENERATED header (`//` comment lines) — serde_json
/// rejects them, and the header contract applies to every artifact.
fn load_manifest() -> Vec<FixtureManifest> {
    let path = fixtures_dir().join("wit_manifest.json");
    let raw = std::fs::read_to_string(&path).unwrap_or_else(|e| fail(&format!("manifest: {e}")));
    let json: String = raw
        .lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");
    let root: Value =
        serde_json::from_str(&json).unwrap_or_else(|e| fail(&format!("manifest parse: {e}")));
    root.as_array()
        .expect("manifest is an array")
        .iter()
        .map(|v| FixtureManifest {
            fixture: v["fixture"].as_str().unwrap_or_default().to_string(),
            types: v["types"]
                .as_array()
                .map(|a| {
                    a.iter()
                        .map(|t| TypeEntry {
                            name: t["name"].as_str().unwrap_or_default().to_string(),
                            kind: t["kind"].as_str().unwrap_or_default().to_string(),
                            fields: strings(t, "fields"),
                            cases: strings(t, "cases"),
                        })
                        .collect()
                })
                .unwrap_or_default(),
            funcs: v["funcs"]
                .as_array()
                .map(|a| {
                    a.iter()
                        .map(|f| FuncEntry {
                            name: f["name"].as_str().unwrap_or_default().to_string(),
                            params: strings(f, "params"),
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

/// Parse one fixture WIT; return the single interface's type/func surfaces.
fn resolve_fixture(name: &str) -> (Resolve, Vec<wit_parser::InterfaceId>) {
    let path = fixtures_dir().join(format!("wit_fixture_{name}.wit"));
    let mut resolve = Resolve::default();
    let (pkg_id, _sources) = match resolve.push_path(&path) {
        Ok(x) => x,
        Err(e) => fail(&format!("fixture {name}: parse failed: {e}")),
    };
    let pkg = &resolve.packages[pkg_id];
    assert_eq!(
        (pkg.name.namespace.as_str(), pkg.name.name.as_str()),
        ("demo", &*format!("fixture-{name}")),
        "fixture {name}: package name"
    );
    // `worldOf` emits the types + exports interface pair — the fixture's
    // types/funcs live across BOTH (a funcs-only universe gets no -types
    // surface worth asserting separately).
    let type_and_func_ids: Vec<wit_parser::InterfaceId> =
        pkg.interfaces.values().copied().collect();
    assert!(
        !type_and_func_ids.is_empty(),
        "fixture {name}: no interfaces"
    );
    (resolve, type_and_func_ids.iter().copied().collect())
}

/// Look a type or func up across ALL of the fixture package's interfaces
/// (`worldOf` may split them across the types/exports pair).

#[test]
fn every_fixture_parses_and_matches_the_manifest() {
    let manifests = load_manifest();
    assert!(
        manifests.len() >= 4,
        "the sweep is VACUOUS with <4 fixtures — the emitter regressed"
    );

    for m in &manifests {
        let (resolve, iface_ids) = resolve_fixture(&m.fixture);
        let ifaces: Vec<&wit_parser::Interface> = iface_ids
            .iter()
            .map(|id| &resolve.interfaces[*id])
            .collect();

        for t in &m.types {
            let (iface, id) = ifaces
                .iter()
                .find_map(|i| i.types.get(&t.name).map(|id| (i, *id)))
                .unwrap_or_else(|| {
                    fail(&format!("fixture {}: missing type `{}`", m.fixture, t.name))
                });
            let td = &resolve.types[id];
            match (t.kind.as_str(), &td.kind) {
                ("record", TypeDefKind::Record(r)) => {
                    let field_names: Vec<&str> = r.fields.iter().map(|f| f.name.as_str()).collect();
                    assert_eq!(
                        field_names,
                        t.fields.iter().map(String::as_str).collect::<Vec<_>>(),
                        "fixture {}: record `{}` field names/order",
                        m.fixture,
                        t.name
                    );
                }
                ("variant", TypeDefKind::Variant(v)) => {
                    let case_names: Vec<&str> = v.cases.iter().map(|c| c.name.as_str()).collect();
                    assert_eq!(
                        case_names,
                        t.cases.iter().map(String::as_str).collect::<Vec<_>>(),
                        "fixture {}: variant `{}` case names/order",
                        m.fixture,
                        t.name
                    );
                }
                (kind, got) => fail(&format!(
                    "fixture {}: type `{}` is {kind:?} in the manifest but {:?} parsed",
                    m.fixture, t.name, got
                )),
            }
        }

        for f in &m.funcs {
            let func = ifaces
                .iter()
                .find_map(|i| i.functions.get(&f.name))
                .unwrap_or_else(|| {
                    fail(&format!("fixture {}: missing func `{}`", m.fixture, f.name))
                });
            let param_names: Vec<&str> = func.params.iter().map(|p| p.name.as_str()).collect();
            assert_eq!(
                param_names,
                f.params.iter().map(String::as_str).collect::<Vec<_>>(),
                "fixture {}: func `{}` param names/order",
                m.fixture,
                f.name
            );
        }
    }
}

#[test]
fn async_fixture_uses_the_async_function_type() {
    // WASI 0.3: async-ness lives in the FUNCTION TYPE — wit-parser must
    // report the `watch` func as AsyncFreestanding, not a sync func
    // returning future<...> (the component validator rejects that shape).
    let manifests = load_manifest();
    let m = manifests
        .iter()
        .find(|m| m.fixture == "async")
        .expect("async fixture in the manifest");
    let (resolve, iface_ids) = resolve_fixture(&m.fixture);
    let func = iface_ids
        .iter()
        .find_map(|id| resolve.interfaces[*id].functions.get("watch"))
        .unwrap_or_else(|| fail("async fixture: missing `watch`"));
    assert!(
        matches!(func.kind, wit_parser::FunctionKind::AsyncFreestanding),
        "`watch` parsed as {:?} — the async emitter lowering regressed",
        func.kind
    );
}

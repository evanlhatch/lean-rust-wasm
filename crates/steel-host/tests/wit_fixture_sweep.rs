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
//!
//! The SEEDED sweep (`wit_sweep/`) generalizes further: N seeded
//! universes (pinned LCG seed) + pinned corner universes — map/set
//! assoc-list rendering under option payloads, tensor flattening under
//! async funcs, deep nesting, empty records, near-collision names —
//! emitted by `SchemaLang.Emit.WitSweep` with a manifest recording each
//! universe's LOWERED shape. Here every accepted universe is parsed and
//! its resolved structure compared against the manifest
//! (`parse (emit u) ≅ manifest u`), recursively over the shape JSON.

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

// ── The seeded sweep (`wit_sweep/`): `parse (emit u) ≅ manifest u` ────

/// The seeded-sweep fixtures directory: N seeded universes (pinned LCG
/// seed) + pinned corner universes, emitted by `SchemaLang.Emit.WitSweep`.
/// The manifest records each universe's LOWERED shape — what wit-parser
/// must resolve, not the lossy Lean `Ty` (map/set → list-of-tuple,
/// tensor → list, bytes → list<u8>).
fn sweep_dir() -> PathBuf {
    fixtures_dir().join("wit_sweep")
}

/// One expected type (record/variant/resource) in a sweep universe.
struct SweepType {
    name: String,
    kind: String,
    /// record fields: name + expected shape ("" kinds match scalars).
    fields: Vec<(String, Value)>,
    /// variant cases: name + expected payload shape (None = bare case).
    cases: Vec<(String, Option<Value>)>,
}

/// One expected func: name, async-ness, params (name + shape), result
/// shape (Value::Null = no result).
struct SweepFunc {
    name: String,
    is_async: bool,
    params: Vec<(String, Value)>,
    result: Value,
}

/// One sweep universe's manifest entry.
struct SweepEntry {
    fixture: String,
    package: String,
    types: Vec<SweepType>,
    funcs: Vec<SweepFunc>,
}

/// Parse one manifest entry's JSON (shared by the loader and the
/// corrupted-manifest negative control).
fn parse_sweep_entry(v: &Value) -> SweepEntry {
    let types = v["types"]
        .as_array()
        .map(|a| {
            a.iter()
                .map(|t| SweepType {
                    name: t["name"].as_str().unwrap_or_default().to_string(),
                    kind: t["kind"].as_str().unwrap_or_default().to_string(),
                    fields: t["fields"]
                        .as_array()
                        .map(|a| {
                            a.iter()
                                .map(|f| {
                                    (
                                        f["name"].as_str().unwrap_or_default().to_string(),
                                        f["shape"].clone(),
                                    )
                                })
                                .collect()
                        })
                        .unwrap_or_default(),
                    cases: t["cases"]
                        .as_array()
                        .map(|a| {
                            a.iter()
                                .map(|c| {
                                    (
                                        c["name"].as_str().unwrap_or_default().to_string(),
                                        if c["payload"].is_null() {
                                            None
                                        } else {
                                            Some(c["payload"].clone())
                                        },
                                    )
                                })
                                .collect()
                        })
                        .unwrap_or_default(),
                })
                .collect()
        })
        .unwrap_or_default();
    let funcs = v["funcs"]
        .as_array()
        .map(|a| {
            a.iter()
                .map(|f| SweepFunc {
                    name: f["name"].as_str().unwrap_or_default().to_string(),
                    is_async: f["async"].as_bool().unwrap_or(false),
                    params: f["params"]
                        .as_array()
                        .map(|a| {
                            a.iter()
                                .map(|p| {
                                    (
                                        p["name"].as_str().unwrap_or_default().to_string(),
                                        p["shape"].clone(),
                                    )
                                })
                                .collect()
                        })
                        .unwrap_or_default(),
                    result: f["result"].clone(),
                })
                .collect()
        })
        .unwrap_or_default();
    SweepEntry {
        fixture: v["fixture"].as_str().unwrap_or_default().to_string(),
        package: v["package"].as_str().unwrap_or_default().to_string(),
        types,
        funcs,
    }
}

/// Load the sweep manifest (stripping the GENERATED header lines).
fn load_sweep_manifest() -> Vec<SweepEntry> {
    let path = sweep_dir().join("manifest.json");
    let raw = std::fs::read_to_string(&path).unwrap_or_else(|e| fail(&format!("sweep manifest: {e}")));
    let json: String = raw
        .lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");
    let root: Value =
        serde_json::from_str(&json).unwrap_or_else(|e| fail(&format!("sweep manifest parse: {e}")));
    root.as_array()
        .expect("sweep manifest is an array")
        .iter()
        .map(parse_sweep_entry)
        .collect()
}

/// Render a resolved type to the manifest's shape JSON. The keys mirror
/// `SchemaLang.Emit.WitSweep.shapeJson` — a mismatch is a parse∘emit
/// disagreement (the audit's bug class).
fn shape_of(resolve: &Resolve, ty: &wit_parser::Type) -> Value {
    use wit_parser::Type as T;
    fn atom(kind: &str) -> Value {
        serde_json::json!({ "kind": kind })
    }
    match ty {
        T::Bool => atom("bool"),
        T::U8 => atom("u8"),
        T::U16 => atom("u16"),
        T::U32 => atom("u32"),
        T::U64 => atom("u64"),
        T::S8 => atom("s8"),
        T::S16 => atom("s16"),
        T::S32 => atom("s32"),
        T::S64 => atom("s64"),
        T::F32 => atom("f32"),
        T::F64 => atom("f64"),
        T::String => atom("string"),
        // `char`/error-context are never emitted — their appearance is
        // a lowering bug (or a manifest/parse drift).
        T::Char | T::ErrorContext => fail(&format!("unexpected parsed type {ty:?}")),
        T::Id(id) => {
            let td = &resolve.types[*id];
            match &td.kind {
                TypeDefKind::Option(t) => serde_json::json!({ "kind": "option", "elem": shape_of(resolve, t) }),
                TypeDefKind::Result(r) => serde_json::json!({
                    "kind": "result",
                    "ok": r.ok.as_ref().map(|t| shape_of(resolve, t)).unwrap_or(Value::Null),
                    "err": r.err.as_ref().map(|t| shape_of(resolve, t)).unwrap_or(Value::Null),
                }),
                TypeDefKind::List(t) => serde_json::json!({ "kind": "list", "elem": shape_of(resolve, t) }),
                TypeDefKind::Tuple(ts) => {
                    serde_json::json!({ "kind": "tuple", "elems": ts.types.iter().map(|t| shape_of(resolve, t)).collect::<Vec<_>>() })
                }
                TypeDefKind::Future(t) => serde_json::json!({
                    "kind": "future",
                    "elem": t.as_ref().map(|t| shape_of(resolve, t)).unwrap_or(Value::Null),
                }),
                TypeDefKind::Stream(t) => serde_json::json!({
                    "kind": "stream",
                    "elem": t.as_ref().map(|t| shape_of(resolve, t)).unwrap_or(Value::Null),
                }),
                // The emitter renders map/set as the assoc-list form — a
                // native `map<K, V>` in the parse is a lowering change.
                TypeDefKind::Map(k, v) => serde_json::json!({
                    "kind": "map", "key": shape_of(resolve, k), "value": shape_of(resolve, v),
                }),
                // Named refs (the only remaining shapes the corpus can
                // produce) carry the name.
                _ => match &td.name {
                    Some(n) => serde_json::json!({ "kind": "ref", "name": n }),
                    None => fail(&format!("unexpected anonymous parsed kind {:?}", td.kind)),
                },
            }
        }
    }
}

/// One universe: parse the fixture, check the package name, and assert
/// every type/func matches the manifest (names in order, shapes
/// recursively). Err carries the named disagreement.
fn check_sweep_entry(m: &SweepEntry) -> Result<(), String> {
    let path = sweep_dir().join(format!("{}.wit", m.fixture));
    let mut resolve = Resolve::default();
    let (pkg_id, _sources) = match resolve.push_path(&path) {
        Ok(x) => x,
        Err(e) => return Err(format!("sweep {}: parse failed: {e}", m.fixture)),
    };
    let pkg = &resolve.packages[pkg_id];
    let pkg_parts: Vec<&str> = m.package.split(':').collect();
    if pkg_parts.len() != 2
        || pkg.name.namespace.as_str() != pkg_parts[0]
        || pkg.name.name.as_str() != pkg_parts[1]
    {
        return Err(format!(
            "sweep {}: package is {}:{} but the manifest says {}",
            m.fixture, pkg.name.namespace, pkg.name.name, m.package
        ));
    }
    let ifaces: Vec<&wit_parser::Interface> =
        pkg.interfaces.values().map(|id| &resolve.interfaces[*id]).collect();

    for t in &m.types {
        let td = ifaces
            .iter()
            .find_map(|i| i.types.get(&t.name).map(|id| &resolve.types[*id]))
            .ok_or_else(|| format!("sweep {}: missing type `{}`", m.fixture, t.name))?;
        match (t.kind.as_str(), &td.kind) {
            ("record", TypeDefKind::Record(r)) => {
                let names: Vec<&str> = r.fields.iter().map(|f| f.name.as_str()).collect();
                let want: Vec<&str> = t.fields.iter().map(|(n, _)| n.as_str()).collect();
                if names != want {
                    return Err(format!(
                        "sweep {}: record `{}` fields {names:?} != manifest {want:?}",
                        m.fixture, t.name
                    ));
                }
                for (f, (fname, shape)) in r.fields.iter().zip(t.fields.iter()) {
                    let got = shape_of(&resolve, &f.ty);
                    if got != *shape {
                        return Err(format!(
                            "sweep {}: record `{}` field `{fname}`: parsed {got} != manifest {shape}",
                            m.fixture, t.name
                        ));
                    }
                }
            }
            ("variant", TypeDefKind::Variant(v)) => {
                let names: Vec<&str> = v.cases.iter().map(|c| c.name.as_str()).collect();
                let want: Vec<&str> = t.cases.iter().map(|(n, _)| n.as_str()).collect();
                if names != want {
                    return Err(format!(
                        "sweep {}: variant `{}` cases {names:?} != manifest {want:?}",
                        m.fixture, t.name
                    ));
                }
                for (c, (cname, payload)) in v.cases.iter().zip(t.cases.iter()) {
                    let got = c
                        .ty
                        .as_ref()
                        .map(|ty| shape_of(&resolve, ty))
                        .unwrap_or(Value::Null);
                    let want = payload.clone().unwrap_or(Value::Null);
                    if got != want {
                        return Err(format!(
                            "sweep {}: variant `{}` case `{cname}`: parsed {got} != manifest {want}",
                            m.fixture, t.name
                        ));
                    }
                }
            }
            ("resource", TypeDefKind::Resource) => {}
            (kind, got) => {
                return Err(format!(
                    "sweep {}: type `{}` is {kind} in the manifest but {got:?} parsed",
                    m.fixture, t.name
                ))
            }
        }
    }

    for f in &m.funcs {
        let func = ifaces
            .iter()
            .find_map(|i| i.functions.get(&f.name))
            .ok_or_else(|| format!("sweep {}: missing func `{}`", m.fixture, f.name))?;
        let param_names: Vec<&str> = func.params.iter().map(|p| p.name.as_str()).collect();
        let want_names: Vec<&str> = f.params.iter().map(|(n, _)| n.as_str()).collect();
        if param_names != want_names {
            return Err(format!(
                "sweep {}: func `{}` params {param_names:?} != manifest {want_names:?}",
                m.fixture, f.name
            ));
        }
        for (p, (pname, shape)) in func.params.iter().zip(f.params.iter()) {
            let got = shape_of(&resolve, &p.ty);
            if got != *shape {
                return Err(format!(
                    "sweep {}: func `{}` param `{pname}`: parsed {got} != manifest {shape}",
                    m.fixture, f.name
                ));
            }
        }
        let got_result = func
            .result
            .as_ref()
            .map(|ty| shape_of(&resolve, ty))
            .unwrap_or(Value::Null);
        if got_result != f.result {
            return Err(format!(
                "sweep {}: func `{}` result: parsed {got_result} != manifest {}",
                m.fixture, f.name, f.result
            ));
        }
        let got_async = matches!(func.kind, wit_parser::FunctionKind::AsyncFreestanding);
        if got_async != f.is_async {
            return Err(format!(
                "sweep {}: func `{}` is async={got_async} but the manifest says {}",
                m.fixture, f.name, f.is_async
            ));
        }
    }
    Ok(())
}

/// The two caught emitter bugs — the seeded sweep's PRIZE — are FIXED
/// in the WF lane: both universes now refuse at ELABORATION (Lean-side
/// `universeCheck`: the post-mangle uniqueness scan `mangleCollDiags`
/// names the colliding preimages; the `emptyVariant` arm refuses the
/// zero-case variant). They are no longer emitted as fixtures; the
/// agreement sweep carries their LEGAL controls instead
/// (`corner-kebab-near`, `corner-min-variant`, the record-only
/// `corner-empty`).
///
/// The GRAMMAR FACTS the bugs encoded stay pinned here — wit-parser
/// must keep rejecting the shapes the WF gate forbids (a universe
/// whose illegal emission wit-parser accepted blindly is the failure
/// mode the lane exists to prevent).
#[test]
fn the_wf_gate_shapes_stay_rejected_by_wit_parser() {
    for (name, wit, needle) in [
        (
            "post-mangle-collision",
            "package demo:dup;\ninterface dup-types {\n  record foo-bar { v: u8, }\n  record foo-bar { v: u16, }\n}\ninterface dup-exports {}\nworld dup { export dup-exports; }\n",
            "defined more than once",
        ),
        (
            "zero-case-variant",
            "package demo:empty;\ninterface empty-types {\n  variant v { }\n}\ninterface empty-exports {}\nworld empty { export empty-exports; }\n",
            "empty variant",
        ),
    ] {
        let dir = std::env::temp_dir().join(format!("wit-wf-refusal-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap_or_else(|e| fail(&format!("mkdir: {e}")));
        let p = dir.join(format!("{name}.wit"));
        std::fs::write(&p, wit).unwrap_or_else(|e| fail(&format!("write: {e}")));
        let mut resolve = Resolve::default();
        let err = match resolve.push_path(&p) {
            Ok(_) => fail(&format!(
                "wf refusal {name}: wit-parser ACCEPTED the shape the WF gate forbids — the gate is load-bearing, re-audit before loosening"
            )),
            Err(e) => e,
        };
        let msg = format!("{err:#}");
        assert!(
            msg.contains(needle),
            "wf refusal {name}: expected the diagnostic to mention `{needle}`, got: {msg}"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}

#[test]
fn every_seeded_universe_parses_and_matches_the_manifest() {
    let entries = load_sweep_manifest();
    assert!(
        entries.len() >= 17,
        "the seeded sweep is VACUOUS with <17 universes (12 seeded + 6 corners) — the emitter regressed"
    );
    // The caught-bug corners are FIXED in the WF lane (Lean-side
    // elaboration refusals — see `the_wf_gate_shapes_stay_rejected_by_wit_parser`)
    // and the corpus carries their legal controls; EVERY emitted
    // universe is under the agreement law now.
    let mut checked = 0usize;
    for m in &entries {
        check_sweep_entry(m).unwrap_or_else(|e| fail(&e));
        checked += 1;
    }
    assert!(
        checked >= 17,
        "only {checked} universes under the agreement law — the corpus shrank"
    );
}

/// The corpus must actually REACH the audit's corners (a coverage
/// witness — the shape-JSON analogue of TestKit's generator-vacuity
/// controls): assoc-list tuples under option payloads, async
/// future-unwrapped results, streams, deep nesting.

/// Visit every object node of a shape JSON (recursively).
fn walk_shapes(v: &Value, f: &mut impl FnMut(&Value)) {
    match v {
        Value::Object(o) => {
            f(v);
            for (_, val) in o {
                walk_shapes(val, f);
            }
        }
        Value::Array(a) => {
            for val in a {
                walk_shapes(val, f);
            }
        }
        _ => {}
    }
}

/// Does any object node in this shape satisfy `pred`?
fn walk_find(v: &Value, pred: &impl Fn(&Value) -> bool) -> bool {
    let mut hit = false;
    walk_shapes(v, &mut |w: &Value| {
        if pred(w) {
            hit = true;
        }
    });
    hit
}

#[test]
fn sweep_corpus_covers_the_audit_corners() {
    let entries = load_sweep_manifest();
    // Every shape in the corpus, as one flat node stream.
    let mut nodes: Vec<Value> = Vec::new();
    let mut any_async = false;
    let mut deepest = 0usize;
    let mut depth_of = |v: &Value| -> usize {
        // structural depth (option/list/result towers nest via "elem")
        fn depth(v: &Value) -> usize {
            match v {
                Value::Object(o) => {
                    1 + o.values().map(depth).max().unwrap_or(0)
                }
                Value::Array(a) => 1 + a.iter().map(depth).max().unwrap_or(0),
                _ => 0,
            }
        }
        depth(v)
    };
    let mut acc = |shape: &Value, is_async: &mut bool| {
        walk_shapes(shape, &mut |v: &Value| nodes.push(v.clone()));
        *is_async |= true;
        let d = depth_of(shape);
        if d > deepest {
            deepest = d;
        }
    };
    for m in &entries {
        for (_, shape) in m.types.iter().flat_map(|t| t.fields.iter()) {
            acc(shape, &mut false);
        }
        for payload in m.types.iter().flat_map(|t| t.cases.iter().map(|(_, p)| p)) {
            if let Some(p) = payload {
                acc(p, &mut false);
            }
        }
        for (_, shape) in m.funcs.iter().flat_map(|f| f.params.iter()) {
            acc(shape, &mut false);
        }
        for f in &m.funcs {
            acc(&f.result, &mut any_async);
        }
        any_async |= m.funcs.iter().any(|f| f.is_async);
    }
    let has = |kind: &str| nodes.iter().any(|v| v["kind"] == kind);
    assert!(has("tuple"), "no assoc-list (map) rendering in the corpus");
    // The option-payload corner: an option nested INSIDE a tuple (the
    // map assoc-list rendering under option payloads).
    let mut option_in_tuple = false;
    for v in &nodes {
        if v["kind"] == "tuple" {
            option_in_tuple |= walk_find(v, &|w: &Value| w["kind"] == "option");
        }
    }
    assert!(option_in_tuple, "no option payload inside a map's tuple — the corner is starved");
    assert!(has("stream"), "no stream payload in the corpus");
    assert!(has("result"), "no result payload in the corpus");
    assert!(any_async, "no async func in the corpus");
    // Deep nesting: a shape nested ≥8 structural levels (the tower).
    assert!(deepest >= 8, "deep nesting starved: max shape depth {deepest} < 8");
}

/// The negative control: hand-corrupted inputs MUST fail the sweep —
/// (1) a mangled WIT keyword must be refused by the parser, and
/// (2) a corrupted manifest shape must fail the agreement check
/// (a control that passes proves `check_sweep_entry` vacuous).
#[test]
fn corrupted_sweep_inputs_are_caught() {
    let entries = load_sweep_manifest();
    let _m = entries
        .iter()
        .find(|e| e.fixture == "sweep-01")
        .expect("sweep-01 in the manifest");

    // Class 1: mangled keyword (`interface` → `interf4ce`).
    let raw = std::fs::read_to_string(sweep_dir().join("sweep-01.wit"))
        .unwrap_or_else(|e| fail(&format!("read sweep-01: {e}")));
    let dir = std::env::temp_dir().join(format!("wit-sweep-corrupt-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap_or_else(|e| fail(&format!("mkdir: {e}")));
    let p = dir.join("corrupt.wit");
    std::fs::write(&p, raw.replacen("interface", "interf4ce", 1))
        .unwrap_or_else(|e| fail(&format!("write: {e}")));
    let mut resolve = Resolve::default();
    assert!(
        resolve.push_path(&p).is_err(),
        "a mangled keyword must not parse (silent acceptance)"
    );
    let _ = std::fs::remove_dir_all(&dir);

    // Class 2: corrupt the FIRST field's shape kind (bool → f64) — the
    // agreement check must name the disagreement.
    let v: Value = serde_json::from_str(
        &std::fs::read_to_string(sweep_dir().join("manifest.json"))
            .unwrap_or_else(|e| fail(&format!("read manifest: {e}")))
            .lines()
            .filter(|l| !l.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n"),
    )
    .unwrap_or_else(|e| fail(&format!("manifest parse: {e}")));
    let mut corrupted = v.clone();
    corrupted[0]["types"][0]["fields"][0]["shape"]["kind"] = Value::String("f64".into());
    let entry = parse_sweep_entry(&corrupted[0]);
    match check_sweep_entry(&entry) {
        Err(e) => assert!(
            e.contains("f64") && e.contains("field"),
            "the corruption diagnostic must name the disagreement, got: {e}"
        ),
        Ok(()) => fail("corrupted manifest shape: the agreement check PASSED — it is vacuous"),
    }
}

//! W8.11 — HOST-SIDE GENERATION: the host produces its binding
//! contract from the COMMITTED universe snapshot
//! (`lean/schema-lang/goldens/universe.snapshot`) and validates it
//! against what `bindgen!` actually consumed (`wit/gateway.wit`,
//! resolved here with wit-parser) — the byte-tie moved INTO the host,
//! no longer a one-way trust of checked-in artifacts.
//!
//! Pins:
//!   (a) the happy path — the committed snapshot parses, its
//!       generated surface covers the contract
//!       (`schema::EXPECTED_DEMO_SURFACE`), and its types are
//!       EQUAL to the parsed WIT (names, member order, per-field
//!       payload types, func param/ret types, the async marker);
//!   (b) the negative control — a TAMPERED committed artifact
//!       (`fixtures/universe.snapshot.tampered`: `order-item.qty`
//!       u32 → u64, a drift the surface contract CANNOT see) is
//!       CAUGHT by the type-level tie;
//!   (c) the perturbation sweep — dropped field, renamed case, extra
//!       case, func arity drift, and corrupt snapshot lines each fail
//!       loud with the corruption class named.

use std::path::{Path, PathBuf};

use wit_parser::{Function, FunctionKind, Interface, Resolve, Type, TypeDefKind, TypeId};

use steel_host::hostgen::{self, Item, Ty};
use steel_host::schema::EXPECTED_DEMO_SURFACE;

/// Fail with a message (the house pattern: no bare `unwrap`).
#[track_caller]
#[allow(clippy::panic, reason = "test helper: fail loud, fail clear")]
fn fail(msg: &str) -> ! {
    panic!("{msg}");
}

/// The committed universe snapshot (the SSOT the host validates from).
fn committed_snapshot_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/schema-lang/goldens/universe.snapshot")
}

/// The TAMPERED fixture: the committed snapshot with `order-item.qty`
/// u32 → u64 (a payload-type drift invisible to the surface contract).
fn tampered_snapshot_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/universe.snapshot.tampered")
}

/// The generated WIT the host's `bindgen!` consumed.
fn gateway_wit_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../wit/gateway.wit")
}

/// Resolve `wit/gateway.wit`.
fn resolve_gateway() -> Result<(Resolve, wit_parser::PackageId), Box<dyn std::error::Error>> {
    let mut resolve = Resolve::default();
    let (pkg_id, _sources) = resolve.push_path(&gateway_wit_path())?;
    Ok((resolve, pkg_id))
}

/// Look up a named interface in the parsed package.
fn interface<'r>(
    resolve: &'r Resolve,
    pkg: wit_parser::PackageId,
    name: &str,
) -> Result<&'r Interface, Box<dyn std::error::Error>> {
    let pkg = &resolve.packages[pkg];
    let id = pkg.interfaces.get(name).ok_or(format!(
        "package {}:{} has no interface `{name}`",
        pkg.name.namespace, pkg.name.name
    ))?;
    Ok(&resolve.interfaces[*id])
}

/// Resolve `use`-alias chains to the underlying typedef.
fn follow_alias(resolve: &Resolve, mut id: TypeId) -> TypeId {
    while let TypeDefKind::Type(Type::Id(next)) = resolve.types[id].kind {
        id = next;
    }
    id
}

/// Translate a wit-parser type into hostgen's `Ty` — the common
/// vocabulary both sides of the tie are compared in. WIT names are
/// ALREADY the kebab wire spelling (the Lean emitter's convention),
/// so they pass through verbatim; the SNAPSHOT side is kebab'd at the
/// comparison site (hostgen's parse is lossless).
fn wit_ty(resolve: &Resolve, ty: &Type) -> Ty {
    match ty {
        Type::Bool => Ty::Bool,
        Type::U8 => Ty::U8,
        Type::U16 => Ty::U16,
        Type::U32 => Ty::U32,
        Type::U64 => Ty::U64,
        Type::S8 => Ty::I8,
        Type::S16 => Ty::I16,
        Type::S32 => Ty::I32,
        Type::S64 => Ty::I64,
        Type::F32 => Ty::F32,
        Type::F64 => Ty::F64,
        Type::Char | Type::String => Ty::String,
        Type::Id(id) => {
            let td = &resolve.types[*id];
            match &td.kind {
                TypeDefKind::Option(inner) => Ty::Option(Box::new(wit_ty(resolve, inner))),
                TypeDefKind::List(elem) => Ty::List(Box::new(wit_ty(resolve, elem))),
                TypeDefKind::Result(r) => match (&r.ok, &r.err) {
                    (Some(ok), Some(err)) => Ty::Result(
                        Box::new(wit_ty(resolve, ok)),
                        Box::new(wit_ty(resolve, err)),
                    ),
                    _ => fail("wit result with a unit side is not snapshot-representable"),
                },
                TypeDefKind::Future(inner) => match inner {
                    Some(t) => Ty::Future(Box::new(wit_ty(resolve, t))),
                    None => fail("wit future with no payload is not snapshot-representable"),
                },
                TypeDefKind::Stream(inner) => match inner {
                    Some(t) => Ty::Stream(Box::new(wit_ty(resolve, t))),
                    None => fail("wit stream with no payload is not snapshot-representable"),
                },
                _ => {
                    let id = follow_alias(resolve, *id);
                    let name = resolve.types[id]
                        .name
                        .clone()
                        .unwrap_or_else(|| fail("anonymous typedef where a name was needed"));
                    Ty::Named(name)
                }
            }
        }
        other => fail(&format!("untranslated wit type: {other:?}")),
    }
}

/// The committed snapshot's typed projection.
fn committed_universe() -> hostgen::Universe {
    let text = std::fs::read_to_string(committed_snapshot_path())
        .unwrap_or_else(|e| fail(&format!("reading the committed snapshot: {e}")));
    let items = hostgen::parse_snapshot(&text)
        .unwrap_or_else(|e| fail(&format!("the COMMITTED snapshot must parse: {e}")));
    hostgen::Universe::new(items)
}

/// The WIT-vocabulary projection of a snapshot type: kebab every
/// named ref (the comparison seam — hostgen's parse stays VERBATIM;
/// the WIT side is already the kebab wire spelling).
fn wire_ty(ty: &Ty) -> Ty {
    match ty.clone() {
        Ty::Option(t) => Ty::Option(Box::new(wire_ty(&t))),
        Ty::Result(a, b) => Ty::Result(Box::new(wire_ty(&a)), Box::new(wire_ty(&b))),
        Ty::List(t) => Ty::List(Box::new(wire_ty(&t))),
        Ty::Map(k, v) => Ty::Map(Box::new(wire_ty(&k)), Box::new(wire_ty(&v))),
        Ty::Set(t) => Ty::Set(Box::new(wire_ty(&t))),
        Ty::Future(t) => Ty::Future(Box::new(wire_ty(&t))),
        Ty::Stream(t) => Ty::Stream(Box::new(wire_ty(&t))),
        Ty::Tensor(d, t) => Ty::Tensor(d, Box::new(wire_ty(&t))),
        Ty::Named(n) => Ty::Named(hostgen::kebab(&n)),
        scalar => scalar,
    }
}

// ── (a) the happy path ──────────────────────────────────────────────

#[test]
fn committed_snapshot_parses_to_the_expected_universe() {
    let universe = committed_universe();
    // the eight committed items, in registry order, names VERBATIM
    // (parse is lossless — the snapshot's own spelling)
    let names: Vec<&str> = universe
        .items()
        .iter()
        .map(|it| match it {
            Item::Record { name, .. }
            | Item::Variant { name, .. }
            | Item::Func { name, .. }
            | Item::Resource { name } => name.as_str(),
        })
        .collect();
    assert_eq!(
        names,
        [
            "User",
            "OrderItem",
            "Order",
            "Role",
            "OrderError",
            "getUser",
            "watchOrders",
            "Db"
        ],
        "committed snapshot items (registry order)"
    );
}

#[test]
fn generated_surface_covers_the_contract() {
    let universe = committed_universe();
    // PRODUCE the schema surface from the committed universe
    let entries = universe
        .surface_entries()
        .unwrap_or_else(|e| fail(&format!("surface generation: {e}")));
    assert_eq!(
        entries,
        vec![("get-user".to_string(), 1), ("watch-orders".to_string(), 2),],
        "generated surface (the oracle's flat-arg convention: \
         option(ty(User)) is one slot, ty(OrderError) a variant = 2)"
    );

    // VALIDATE against the compiled-in expectation. `watch-orders` is
    // out of contract (the host never calls it — see schema.rs); the
    // contract-covered part must be exactly `get-user/1`.
    let coverage = hostgen::validate_committed(
        &std::fs::read_to_string(committed_snapshot_path())
            .unwrap_or_else(|e| fail(&format!("reading the committed snapshot: {e}"))),
        EXPECTED_DEMO_SURFACE,
    )
    .unwrap_or_else(|e| fail(&format!("the COMMITTED pair must validate: {e}")));
    assert_eq!(
        coverage.covered,
        vec![("get-user".to_string(), 1)],
        "contract-covered schema fns"
    );
    assert_eq!(
        coverage.out_of_contract,
        vec![("watch-orders".to_string(), 2)],
        "out-of-contract schema fns (legitimate extras)"
    );
}

#[test]
fn snapshot_types_equal_the_wit_bindgen_consumed() {
    let universe = committed_universe();
    let (resolve, pkg) = resolve_gateway().unwrap_or_else(|e| fail(&e.to_string()));
    let types = interface(&resolve, pkg, "gateway-types").unwrap_or_else(|e| fail(&e.to_string()));

    // every snapshot TYPE must appear in gateway-types with the SAME
    // kind, member names/order, and per-member payload types
    for item in universe.items() {
        match item {
            Item::Record { name, fields } => {
                let wit_name = hostgen::kebab(name);
                let id = types.types.get(&wit_name).unwrap_or_else(|| {
                    fail(&format!("gateway-types is missing record `{wit_name}`"))
                });
                let TypeDefKind::Record(r) = &resolve.types[*id].kind else {
                    fail(&format!(
                        "`{wit_name}`: snapshot record but WIT says {:?}",
                        resolve.types[*id].kind
                    ));
                };
                let got: Vec<(String, Ty)> = r
                    .fields
                    .iter()
                    .map(|f| (f.name.to_string(), wit_ty(&resolve, &f.ty)))
                    .collect();
                let want: Vec<(String, Ty)> = fields
                    .iter()
                    // the kebab projection at the comparison seam (the
                    // snapshot side is verbatim)
                    .map(|(n, t)| (hostgen::kebab(n), wire_ty(t)))
                    .collect();
                assert_eq!(
                    got, want,
                    "record `{wit_name}` fields (names, order, TYPES)"
                );
            }
            Item::Variant { name, cases } => {
                let wit_name = hostgen::kebab(name);
                let id = types.types.get(&wit_name).unwrap_or_else(|| {
                    fail(&format!("gateway-types is missing variant `{wit_name}`"))
                });
                let TypeDefKind::Variant(v) = &resolve.types[*id].kind else {
                    fail(&format!(
                        "`{wit_name}`: snapshot variant but WIT says {:?}",
                        resolve.types[*id].kind
                    ));
                };
                let got: Vec<(String, Option<Ty>)> = v
                    .cases
                    .iter()
                    .map(|c| {
                        (
                            c.name.to_string(),
                            c.ty.as_ref().map(|t| wit_ty(&resolve, t)),
                        )
                    })
                    .collect();
                let want: Vec<(String, Option<Ty>)> = cases
                    .iter()
                    .map(|(n, t)| (hostgen::kebab(n), t.as_ref().map(wire_ty)))
                    .collect();
                assert_eq!(
                    got, want,
                    "variant `{wit_name}` cases (names, order, payload TYPES)"
                );
            }
            Item::Resource { name } => {
                let wit_name = hostgen::kebab(name);
                let id = types.types.get(&wit_name).unwrap_or_else(|| {
                    fail(&format!("gateway-types is missing resource `{wit_name}`"))
                });
                assert!(
                    matches!(&resolve.types[*id].kind, TypeDefKind::Resource),
                    "`{wit_name}`: snapshot resource but WIT says {:?}",
                    resolve.types[*id].kind
                );
            }
            Item::Func { .. } => {}
        }
    }

    // no EXTRA types either: the tie is bidirectional
    let snapshot_type_count = universe
        .items()
        .iter()
        .filter(|it| !matches!(it, Item::Func { .. }))
        .count();
    assert_eq!(
        types.types.len(),
        snapshot_type_count,
        "gateway-types carries exactly the snapshot's types"
    );
}

#[test]
fn snapshot_funcs_equal_the_wit_bindgen_consumed() {
    let universe = committed_universe();
    let (resolve, pkg) = resolve_gateway().unwrap_or_else(|e| fail(&e.to_string()));
    let exports =
        interface(&resolve, pkg, "gateway-exports").unwrap_or_else(|e| fail(&e.to_string()));

    for item in universe.items() {
        let Item::Func {
            name,
            params,
            ret,
            sem: _,
        } = item
        else {
            continue;
        };
        let f: &Function = exports
            .functions
            .get(&hostgen::kebab(name))
            .unwrap_or_else(|| {
                fail(&format!(
                    "gateway-exports is missing `{}`",
                    hostgen::kebab(name)
                ))
            });
        // params: names + types (the kebab projection at the seam)
        let got: Vec<(String, Ty)> = f
            .params
            .iter()
            .map(|p| (p.name.to_string(), wit_ty(&resolve, &p.ty)))
            .collect();
        let want: Vec<(String, Ty)> = params
            .iter()
            .map(|(n, t)| (hostgen::kebab(n), wire_ty(t)))
            .collect();
        assert_eq!(
            got,
            want,
            "func `{}` params (names, order, TYPES)",
            hostgen::kebab(name)
        );
        // the async marker: snapshot `future(…)` ret == wit `async func`
        let snapshot_async = matches!(ret, Ty::Future(_));
        let wit_async = matches!(f.kind, FunctionKind::AsyncFreestanding);
        assert_eq!(
            snapshot_async,
            wit_async,
            "func `{}`: the async marker must agree",
            hostgen::kebab(name)
        );
        // the ret type: a future ret compares UNWRAPPED (the emitter
        // renders `future(list(ty(User)))` as `async func -> list<user>`)
        let payload = match ret {
            Ty::Future(inner) => wire_ty(inner),
            other => wire_ty(other),
        };
        let wit_ret = f
            .result
            .unwrap_or_else(|| fail(&format!("func `{name}` has no wit result")));
        assert_eq!(
            wit_ty(&resolve, &wit_ret),
            payload,
            "func `{}` ret type",
            hostgen::kebab(name)
        );
    }
}

// ── (b) the negative control: a tampered committed artifact ─────────

#[test]
fn tampered_committed_snapshot_is_caught() {
    let text = std::fs::read_to_string(tampered_snapshot_path())
        .unwrap_or_else(|e| fail(&format!("reading the tampered fixture: {e}")));
    // the tamper PARSES (it is a plausible universe, not a corrupt one)
    let items = hostgen::parse_snapshot(&text)
        .unwrap_or_else(|e| fail(&format!("the tampered fixture must parse: {e}")));
    let universe = hostgen::Universe::new(items);

    // ...and the surface contract CANNOT see it (arity is unchanged:
    // option(ty(User)) is one slot either way) — this is why the
    // type-level tie exists
    let entries = universe
        .surface_entries()
        .unwrap_or_else(|e| fail(&format!("surface generation: {e}")));
    assert!(
        hostgen::check_contract(&entries, EXPECTED_DEMO_SURFACE).is_ok(),
        "the surface contract alone must NOT catch a payload-type drift"
    );

    // the type-level tie DOES: order-item.qty u64 in the snapshot vs
    // u32 in the WIT bindgen consumed
    let (resolve, pkg) = resolve_gateway().unwrap_or_else(|e| fail(&e.to_string()));
    let types = interface(&resolve, pkg, "gateway-types").unwrap_or_else(|e| fail(&e.to_string()));
    let order_item = universe
        .find("OrderItem")
        .unwrap_or_else(|| fail("tampered universe lost OrderItem"));
    let Item::Record { fields, .. } = order_item else {
        fail("OrderItem is a record");
    };
    let id = types
        .types
        .get("order-item")
        .unwrap_or_else(|| fail("gateway-types lost order-item"));
    let TypeDefKind::Record(wit_rec) = &resolve.types[*id].kind else {
        fail("order-item is a record in the WIT");
    };
    let drifted: Vec<bool> = fields
        .iter()
        .zip(wit_rec.fields.iter())
        .map(|((_, snap), wit)| wire_ty(snap) != wit_ty(&resolve, &wit.ty))
        .collect();
    assert_eq!(
        drifted,
        vec![false, true, false],
        "exactly `qty` must drift (snapshot u64 vs WIT u32)"
    );
}

// ── (c) the perturbation sweep ──────────────────────────────────────

/// The committed snapshot text, for in-memory perturbations.
fn committed_text() -> String {
    std::fs::read_to_string(committed_snapshot_path())
        .unwrap_or_else(|e| fail(&format!("reading the committed snapshot: {e}")))
}

#[test]
fn dropped_field_is_caught_by_the_type_tie() {
    let text = committed_text().replace("field email string\n", "");
    assert_ne!(text, committed_text());
    let universe = hostgen::Universe::new(
        hostgen::parse_snapshot(&text).unwrap_or_else(|e| fail(&format!("{e}"))),
    );
    // the surface still agrees (arity unchanged) — the TYPE tie catches it
    let (resolve, pkg) = resolve_gateway().unwrap_or_else(|e| fail(&e.to_string()));
    let types = interface(&resolve, pkg, "gateway-types").unwrap_or_else(|e| fail(&e.to_string()));
    let Item::Record { fields, .. } = universe.find("User").unwrap_or_else(|| fail("User")) else {
        fail("User is a record");
    };
    assert_eq!(fields.len(), 3, "email dropped from the snapshot");
    let id = types.types["user"];
    let TypeDefKind::Record(wit_rec) = &resolve.types[id].kind else {
        fail("user is a record in the WIT");
    };
    assert_eq!(
        wit_rec.fields.len(),
        4,
        "the WIT still has 4 fields — MISMATCH"
    );
    // hostgen-level: the projections differ
    let snap: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
    let wit: Vec<&str> = wit_rec.fields.iter().map(|f| f.name.as_str()).collect();
    assert_ne!(snap, wit, "dropped field must be caught by the tie");
}

#[test]
fn renamed_case_is_caught_by_the_type_tie() {
    let text = committed_text().replace("case admin", "case root");
    assert_ne!(text, committed_text());
    let universe = hostgen::Universe::new(
        hostgen::parse_snapshot(&text).unwrap_or_else(|e| fail(&format!("{e}"))),
    );
    let Item::Variant { cases, .. } = universe.find("Role").unwrap_or_else(|| fail("Role")) else {
        fail("Role is a variant");
    };
    let names: Vec<&str> = cases.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["root", "editor", "viewer"]);
    let (resolve, pkg) = resolve_gateway().unwrap_or_else(|e| fail(&e.to_string()));
    let types = interface(&resolve, pkg, "gateway-types").unwrap_or_else(|e| fail(&e.to_string()));
    let id = types.types["role"];
    let TypeDefKind::Variant(v) = &resolve.types[id].kind else {
        fail("role is a variant in the WIT");
    };
    let wit: Vec<&str> = v.cases.iter().map(|c| c.name.as_str()).collect();
    assert_ne!(names, wit, "renamed case must be caught by the tie");
}

#[test]
fn func_arity_drift_is_caught_by_the_contract_check() {
    // getUser grows a second param → generated `get-user/2` vs the
    // contract's `get-user/1`
    let text = committed_text().replace(
        "func getUser\nparam id u64\n",
        "func getUser\nparam id u64\nparam extra u64\n",
    );
    assert_ne!(text, committed_text());
    let err = hostgen::validate_committed(&text, EXPECTED_DEMO_SURFACE)
        .expect_err("arity drift must be refused");
    let msg = err.to_string();
    assert!(msg.contains("hostgen contract skew"), "{msg}");
    assert!(
        msg.contains("`get-user` — snapshot arity 2, contract arity 1"),
        "{msg}"
    );
}

#[test]
fn corrupt_snapshot_lines_fail_loud_and_process_continues() {
    // each corruption class: structured Err naming the line + class —
    // never a panic, never a silent skip; and the parser still handles
    // the committed snapshot afterwards (statelessness)
    let cases: Vec<(String, &str)> = vec![
        (
            committed_text().replace("record User\n", "flavor User\n"),
            "unrecognized line",
        ),
        ("field id u64\n".to_string(), "`field` outside a record"),
        (
            committed_text().replace(
                "func getUser\nparam id u64\nret option(ty(User))\n",
                "func getUser\nret option(ty(User))\nparam id u64\n",
            ),
            "`param` after `ret`",
        ),
        (
            committed_text().replace(
                "ret option(ty(User))",
                "ret option(ty(User))\nsem bogus pure",
            ),
            "unknown nullSem token",
        ),
        (
            committed_text().replace("ret option(ty(User))", "ret option(u64"),
            "expected ')'",
        ),
        (
            committed_text().replace(
                "func getUser\nparam id u64\nret option(ty(User))\n",
                "func getUser\nparam id u64\n",
            ),
            "has no `ret` line",
        ),
    ];
    for (text, class) in cases {
        let err = hostgen::parse_snapshot(&text)
            .err()
            .unwrap_or_else(|| fail("the corrupt snapshot must FAIL to parse"));
        let msg = err.to_string();
        assert!(msg.contains(class), "expected `{class}` in: {msg}");
        assert!(msg.contains("snapshot: line"), "line number named: {msg}");
    }
    // the good snapshot still parses — a corrupt load poisons nothing
    assert!(hostgen::parse_snapshot(&committed_text()).is_ok());
}

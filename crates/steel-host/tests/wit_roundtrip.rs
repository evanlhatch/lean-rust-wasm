//! Stage F — Rust round-trip gate.
//!
//! The Lean side proves `parse ∘ emit = id` for Substrait text
//! (Decode.lean). The Rust-side equivalent: parse the GENERATED
//! `wit/gateway.wit` back with wit-parser and assert the resolved schema
//! still matches the SSOT in `lean/schema-lang/Demo.lean`. If the Lean
//! emitter's output drifts from what the Rust host reads, this fails.
//!
//! We assert on STRUCTURE (names / kinds / payload types), never on
//! source text.

use std::path::Path;
use std::path::PathBuf;

use wit_parser::{
    Case, Function, FunctionKind, Interface, Resolve, Type, TypeDef, TypeDefKind, TypeId, WorldKey,
    WorldItem,
};

/// The generated WIT, relative to this crate.
fn gateway_wit_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../wit/gateway.wit")
}

/// Parse `wit/gateway.wit` into a fully-resolved `Resolve` and return it
/// together with the parsed package's id.
fn resolve_gateway() -> Result<(Resolve, wit_parser::PackageId), Box<dyn std::error::Error>> {
    let path = gateway_wit_path();
    let mut resolve = Resolve::default();
    let (pkg_id, _sources) = resolve.push_path(&path)?;
    Ok((resolve, pkg_id))
}

/// Look up an interface by name inside the parsed package.
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

/// Look up a named type declared in an interface.
fn typedef<'r>(
    resolve: &'r Resolve,
    iface: &Interface,
    name: &str,
) -> Result<&'r TypeDef, Box<dyn std::error::Error>> {
    let id = iface.types.get(name).ok_or(format!(
        "interface has no type `{name}` (has: {:?})",
        iface.types.keys()
    ))?;
    Ok(&resolve.types[*id])
}

/// Follow `type` aliases (a `use`d type gets its own TypeDef whose kind is
/// `Type(Type::Id(original))`) down to the underlying definition.
fn follow_alias(resolve: &Resolve, mut id: TypeId) -> TypeId {
    while let TypeDefKind::Type(Type::Id(next)) = resolve.types[id].kind {
        id = next;
    }
    id
}

/// Fail with a message without `panic!` (workspace denies `clippy::panic`).
#[track_caller]
fn fail(msg: &str) {
    assert!(false, "{msg}");
}

#[test]
fn gateway_wit_package_and_interfaces_resolve() -> Result<(), Box<dyn std::error::Error>> {
    let (resolve, pkg) = resolve_gateway()?;

    let pkg = &resolve.packages[pkg];
    assert_eq!(pkg.name.namespace, "demo", "namespace from package demo:gateway");
    assert_eq!(pkg.name.name, "gateway", "package name from package demo:gateway");
    assert_eq!(
        pkg.interfaces.keys().collect::<Vec<_>>(),
        vec!["gateway-types", "gateway-exports"],
        "package interfaces"
    );
    assert_eq!(pkg.worlds.keys().collect::<Vec<_>>(), vec!["gateway"], "package worlds");
    Ok(())
}

#[test]
fn gateway_types_interface_has_schema_types() -> Result<(), Box<dyn std::error::Error>> {
    let (resolve, pkg) = resolve_gateway()?;
    let types = interface(&resolve, pkg, "gateway-types")?;

    // All six schema declarations are present by name.
    for name in ["user", "order-item", "order", "role", "order-error", "db"] {
        assert!(types.types.contains_key(name), "gateway-types is missing type `{name}`");
    }

    // ── record user: exact fields, exact types ──
    let user = typedef(&resolve, types, "user")?;
    let TypeDefKind::Record(record) = &user.kind else {
        fail(&format!("`user` should be a record, got {:?}", user.kind));
        return Ok(());
    };
    let field_names: Vec<&str> = record.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(field_names, ["id", "name", "email", "tags"], "user record fields");
    fn field_ty<'a>(fields: &'a [wit_parser::Field], name: &str) -> Option<&'a Type> {
        fields.iter().find(|f| f.name == name).map(|f| &f.ty)
    }
    assert!(field_ty(&record.fields, "id") == Some(&Type::U64), "user.id should be u64");
    assert!(field_ty(&record.fields, "name") == Some(&Type::String), "user.name should be string");
    assert!(field_ty(&record.fields, "email") == Some(&Type::String), "user.email should be string");
    match field_ty(&record.fields, "tags") {
        Some(ty) => assert_list_of_string(&resolve, ty, "user.tags"),
        None => fail("user.tags missing"),
    }

    // ── record order-item ──
    let order_item = typedef(&resolve, types, "order-item")?;
    let TypeDefKind::Record(order_item) = &order_item.kind else {
        fail(&format!("`order-item` should be a record, got {:?}", order_item.kind));
        return Ok(());
    };
    let field_names: Vec<&str> = order_item.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(field_names, ["id", "qty", "price"], "order-item record fields");
    assert!(field_ty(&order_item.fields, "id") == Some(&Type::U64), "order-item.id should be u64");
    assert!(field_ty(&order_item.fields, "qty") == Some(&Type::U32), "order-item.qty should be u32");
    assert!(
        field_ty(&order_item.fields, "price") == Some(&Type::F64),
        "order-item.price should be f64"
    );

    // ── record order ──
    let order = typedef(&resolve, types, "order")?;
    let TypeDefKind::Record(order) = &order.kind else {
        fail(&format!("`order` should be a record, got {:?}", order.kind));
        return Ok(());
    };
    let field_names: Vec<&str> = order.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(field_names, ["id", "items", "total"], "order record fields");
    match field_ty(&order.fields, "items") {
        Some(Type::Id(items_id)) => {
            let TypeDefKind::List(elem) = &resolve.types[*items_id].kind else {
                fail(&format!(
                    "order.items: expected list<...>, got {:?}",
                    resolve.types[*items_id].kind
                ));
                return Ok(());
            };
            let Type::Id(elem_id) = elem else {
                fail("order.items: list element should be the named `order-item` type");
                return Ok(());
            };
            assert_eq!(
                resolve.types[*elem_id].name.as_deref(),
                Some("order-item"),
                "order.items should be list<order-item>"
            );
        }
        _ => fail("order.items: expected a list<order-item> type"),
    }
    assert!(field_ty(&order.fields, "total") == Some(&Type::F64), "order.total should be f64");

    // ── variant role: 3 caseless cases ──
    let role = typedef(&resolve, types, "role")?;
    let TypeDefKind::Variant(role) = &role.kind else {
        fail(&format!("`role` should be a variant, got {:?}", role.kind));
        return Ok(());
    };
    let case_names: Vec<&str> = role.cases.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(case_names, ["admin", "editor", "viewer"], "role variant cases");
    assert!(role.cases.iter().all(|c: &Case| c.ty.is_none()), "role cases should have no payloads");

    // ── variant order-error: 3 cases, 2 with payloads ──
    let order_error = typedef(&resolve, types, "order-error")?;
    let TypeDefKind::Variant(order_error) = &order_error.kind else {
        fail(&format!("`order-error` should be a variant, got {:?}", order_error.kind));
        return Ok(());
    };
    let case_names: Vec<&str> = order_error.cases.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(
        case_names,
        ["empty-cart", "invalid-item", "insufficient-funds"],
        "order-error cases"
    );
    let payload = |name: &str| -> Option<&Type> {
        order_error.cases.iter().find(|c| c.name == name).and_then(|c| c.ty.as_ref())
    };
    assert!(payload("empty-cart").is_none(), "empty-cart should be caseless");
    assert!(payload("invalid-item") == Some(&Type::U64), "invalid-item should carry u64");
    assert!(
        payload("insufficient-funds") == Some(&Type::F64),
        "insufficient-funds should carry f64"
    );

    // ── resource db ──
    let db = typedef(&resolve, types, "db")?;
    assert!(
        matches!(db.kind, TypeDefKind::Resource),
        "`db` should be a resource, got {:?}",
        db.kind
    );

    Ok(())
}

#[test]
fn gateway_exports_interface_has_schema_functions() -> Result<(), Box<dyn std::error::Error>> {
    let (resolve, pkg) = resolve_gateway()?;
    let exports = interface(&resolve, pkg, "gateway-exports")?;
    let types_iface = interface(&resolve, pkg, "gateway-types")?;

    assert_eq!(
        exports.functions.keys().collect::<Vec<_>>(),
        vec!["get-user", "watch-orders"],
        "gateway-exports functions"
    );

    // `use gateway-types.{user, order-error}` — each alias is its own TypeDef
    // wrapping the original definition; follow aliases to the shared TypeId.
    for name in ["user", "order-error"] {
        let aliased = exports
            .types
            .get(name)
            .copied()
            .ok_or(format!("gateway-exports missing alias `{name}`"))?;
        let original = types_iface
            .types
            .get(name)
            .copied()
            .ok_or(format!("gateway-types missing `{name}`"))?;
        assert_eq!(
            follow_alias(&resolve, aliased),
            original,
            "alias `{name}` should point at the gateway-types definition"
        );
    }
    let user_id = follow_alias(
        &resolve,
        *exports.types.get("user").ok_or("gateway-exports missing alias `user`")?,
    );
    let order_error_id = follow_alias(
        &resolve,
        *exports.types.get("order-error").ok_or("gateway-exports missing alias `order-error`")?,
    );

    // ── get-user: func(id: u64) -> option<user> ──
    let get_user: &Function =
        exports.functions.get("get-user").ok_or("gateway-exports missing `get-user`")?;
    assert!(
        matches!(get_user.kind, FunctionKind::Freestanding),
        "get-user should be a plain (non-async) freestanding func, got {:?}",
        get_user.kind
    );
    assert_eq!(get_user.params.len(), 1, "get-user takes one param");
    assert_eq!(get_user.params[0].name, "id", "get-user param name");
    assert!(get_user.params[0].ty == Type::U64, "get-user param should be u64");
    let result = get_user.result.ok_or("get-user should have a result")?;
    match result {
        Type::Id(id) => match &resolve.types[id].kind {
            TypeDefKind::Option(inner) => {
                let inner_id = match inner {
                    Type::Id(inner_id) => *inner_id,
                    other => {
                        fail(&format!(
                            "get-user result: expected option<user>, got option of {other:?}"
                        ));
                        return Ok(());
                    }
                };
                assert!(
                    follow_alias(&resolve, inner_id) == user_id,
                    "get-user result should be option<user>, got option of {inner:?}"
                );
            }
            kind => fail(&format!("get-user result: expected option<...>, got {kind:?}")),
        },
        ty => fail(&format!("get-user result: expected option<user>, got {ty:?}")),
    }

    // ── watch-orders: async func(into: order-error) -> list<user> ──
    let watch_orders: &Function =
        exports.functions.get("watch-orders").ok_or("gateway-exports missing `watch-orders`")?;
    assert!(
        matches!(watch_orders.kind, FunctionKind::AsyncFreestanding),
        "watch-orders should be `async func`, got {:?}",
        watch_orders.kind
    );
    assert_eq!(watch_orders.params.len(), 1, "watch-orders takes one param");
    assert_eq!(watch_orders.params[0].name, "into", "watch-orders param name");
    let into_ty = match &watch_orders.params[0].ty {
        Type::Id(id) => *id,
        ty => {
            fail(&format!("watch-orders `into` should be order-error, got {ty:?}"));
            return Ok(());
        }
    };
    assert!(
        follow_alias(&resolve, into_ty) == order_error_id,
        "watch-orders `into` should be order-error"
    );
    let result = watch_orders.result.ok_or("watch-orders should have a result")?;
    match result {
        Type::Id(id) => match &resolve.types[id].kind {
            TypeDefKind::List(elem) => {
                let elem_id = match elem {
                    Type::Id(elem_id) => *elem_id,
                    other => {
                        fail(&format!(
                            "watch-orders result: expected list<user>, got list of {other:?}"
                        ));
                        return Ok(());
                    }
                };
                assert!(
                    follow_alias(&resolve, elem_id) == user_id,
                    "watch-orders result should be list<user>, got list of {elem:?}"
                );
            }
            kind => fail(&format!("watch-orders result: expected list<...>, got {kind:?}")),
        },
        ty => fail(&format!("watch-orders result: expected list<user>, got {ty:?}")),
    }

    Ok(())
}

/// Assert a type is `list<string>`.
fn assert_list_of_string(resolve: &Resolve, ty: &Type, what: &str) {
    let Type::Id(id) = ty else {
        fail(&format!("{what}: expected list<string>, got {ty:?}"));
        return;
    };
    match &resolve.types[*id].kind {
        TypeDefKind::List(elem) => {
            assert!(*elem == Type::String, "{what}: list element should be string, got {elem:?}");
        }
        kind => fail(&format!("{what}: expected list<...>, got {kind:?}")),
    }
}

#[test]
fn gateway_world_exports_gateway_exports_interface() -> Result<(), Box<dyn std::error::Error>> {
    let (resolve, pkg) = resolve_gateway()?;

    let world_id =
        resolve.packages[pkg].worlds.get("gateway").copied().ok_or("package has no world `gateway`")?;
    let world = &resolve.worlds[world_id];
    assert_eq!(world.name, "gateway");

    let iface_id = resolve.packages[pkg]
        .interfaces
        .get("gateway-exports")
        .copied()
        .ok_or("package has no interface `gateway-exports`")?;

    let exported_interfaces: Vec<wit_parser::InterfaceId> = world
        .exports
        .iter()
        .filter_map(|(key, item)| match (key, item) {
            (WorldKey::Interface(id), WorldItem::Interface { .. }) => Some(*id),
            _ => None,
        })
        .collect();
    assert_eq!(
        exported_interfaces,
        vec![iface_id],
        "world `gateway` should export exactly the `gateway-exports` interface"
    );
    Ok(())
}

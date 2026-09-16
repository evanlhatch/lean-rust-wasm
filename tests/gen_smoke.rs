//! W6.4 phase-1 smoke: the emitted generators (src/gen_generated.rs,
//! SchemaLang/Emit/GenRust.lean) compile and produce values from fixed
//! bytes via `arbitrary::Unstructured`.
//!
//! Three pins:
//! - generation SUCCEEDS on a fixed byte supply (deterministic — same
//!   bytes, same values, so this test never flakes);
//! - the depth budget bites: at `max_depth = 0` composites force to
//!   their leaf (empty vecs), and the generated `Order.items` stay
//!   shallow at any depth;
//! - the collision pool fires: generated strings are pool members or
//!   short fresh lowercase strings, never arbitrary bytes.

#![cfg(feature = "arbitrary")]

use arbitrary::Unstructured;
use lean_rust_wasm::gen_generated::{
    STRING_POOL, gen_audit_entry, gen_flag, gen_order, gen_user,
};

/// A fixed, generous byte supply (generation returns `Err` on
/// exhaustion — 4 KiB is far past what one record consumes).
fn supply() -> Vec<u8> {
    (0u8..=255).cycle().take(4096).collect()
}

#[test]
fn gen_user_from_fixed_bytes() {
    let bytes = supply();
    let mut u = Unstructured::new(&bytes);
    let user = gen_user(&mut u, 4).expect("fixed supply generates a User");
    // Every generated string is a pool member or fresh lowercase (the
    // collision-pool discipline — no raw byte garbage).
    for s in std::iter::once(&user.name)
        .chain(std::iter::once(&user.email))
        .chain(user.tags.iter())
    {
        assert!(
            STRING_POOL.contains(&s.as_str())
                || (s.len() <= 8 && s.chars().all(|c| c.is_ascii_lowercase())),
            "string outside the pool discipline: {s:?}"
        );
    }
}

#[test]
fn gen_order_depth_zero_forces_leaves() {
    let bytes = supply();
    let mut u = Unstructured::new(&bytes);
    let order = gen_order(&mut u, 0).expect("depth 0 still generates");
    assert!(
        order.items.is_empty(),
        "forced leaf at depth 0: items must be empty"
    );
}

#[test]
fn gen_order_bounded_at_depth() {
    let bytes = supply();
    let mut u = Unstructured::new(&bytes);
    let order = gen_order(&mut u, 2).expect("fixed supply generates an Order");
    assert!(order.items.len() <= 3, "list arm's width bound");
}

#[test]
fn gen_flags_records() {
    // The FeatureFlags universe's records generate through the same fns
    // (the driver merges both registries into one artifact).
    let bytes = supply();
    let mut u = Unstructured::new(&bytes);
    let flag = gen_flag(&mut u, 3).expect("fixed supply generates a Flag");
    assert!(
        STRING_POOL.contains(&flag.key.as_str()) || flag.key.len() <= 8,
        "key obeys the pool discipline"
    );
    let mut u = Unstructured::new(&bytes);
    let entry = gen_audit_entry(&mut u, 3).expect("fixed supply generates an AuditEntry");
    for s in [&entry.flagKey, &entry.action] {
        assert!(
            STRING_POOL.contains(&s.as_str())
                || (s.len() <= 8 && s.chars().all(|c| c.is_ascii_lowercase())),
            "string outside the pool discipline: {s:?}"
        );
    }
}

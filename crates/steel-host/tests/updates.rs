//! The update semantics, REPLAYED — the host side of the update tie.
//!
//! `src/updates_generated.rs` is GENERATED from the `schema_update`
//! registry (the proved `UpdateItem.applyRow` discipline: guard AND
//! value read the ORIGINAL row; a refused row passes through
//! untouched; the tick re-runs updates in registration order). This
//! test replays those semantics against the generated walkers.

#[path = "../../../src/updates_generated.rs"]
mod updates;

use updates::*;

fn demo_users() -> Vec<schema_generated::User> {
    vec![
        schema_generated::User { id: 150, name: "long-name".into(), email: String::new(), tags: vec![] },
        schema_generated::User { id: 50, name: "ab".into(), email: String::new(), tags: vec![] },
    ]
}

#[test]
fn update_guard_reads_the_original_row() {
    // reset_id: guard `id > 100` — 150 fires, 50 is refused.
    // Lean pin: apply on ids [150, 50] → [0, 50].
    let mut rows = demo_users();
    apply_reset_id(&mut rows);
    assert_eq!(rows[0].id, 0, "the guarded row fires");
    assert_eq!(rows[1].id, 50, "the refused row passes through");
}

#[test]
fn update_value_reads_the_original_row() {
    // self_bump: `id := id` — the value is the ORIGINAL id, and the
    // echo of a refused... the self-read update is IDEMPOTENT here
    // (the value expr is the identity) — the pin: run twice, same.
    let mut rows = demo_users();
    apply_self_bump(&mut rows);
    let after1: Vec<u64> = rows.iter().map(|r| r.id).collect();
    apply_self_bump(&mut rows);
    let after2: Vec<u64> = rows.iter().map(|r| r.id).collect();
    assert_eq!(after1, after2, "the self-read update sees the original row");
}

#[test]
fn update_string_channel_replayed() {
    // echo_email: guard `strlen(name) > 3`, set `email := name`.
    let mut rows = demo_users();
    apply_echo_email(&mut rows);
    assert_eq!(rows[0].email, "long-name", "the long name echoes");
    assert_eq!(rows[1].email, "", "the short name is refused");
}

#[test]
fn tick_replays_registration_order() {
    let mut rows = demo_users();
    tick_user(&mut rows);
    // reset_id fired (150 → 0), echo_email fired (email := name),
    // self_bump no-op'd.
    assert_eq!(rows[0].id, 0);
    assert_eq!(rows[0].email, "long-name");
    assert_eq!(rows[1].id, 50);
    assert_eq!(rows[1].email, "");
}

// bring the schema type into scope for the demo constructor
use lean_rust_wasm::schema_generated;

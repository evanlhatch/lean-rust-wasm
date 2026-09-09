//! The guestlang change algebra — the Rust mirror of `Dbsp.ChangeSpec`.
//!
//! The trait itself is GENERATED (`dbsp_change_generated.rs`, emitted
//! from schema-lang's `changeSpecEmitter`; spec source: the Lean
//! `Dbsp.ChangeSpec` class — `patch`/`valid` are the class fields).
//! This module re-exports it under the historical path: generated delta
//! enums (`delta_generated.rs`) impl `dbsp::Change<Row>`; the
//! certified-delta tests execute the patch/validity shape on concrete
//! values (Stage E: the `ChangeSpec` laws, executed).
//!
//! This is the CONCEPTUAL framework's trait — NOT the Feldera `dbsp`
//! crate.

pub use crate::dbsp_change_generated::Change;

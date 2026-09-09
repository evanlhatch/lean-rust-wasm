//! The guestlang change algebra — the Rust mirror of `Dbsp.ChangeSpec`
//! (Lean's kernel-checked class: `Change (α Δα)` with `patch : α → Δα → α`,
//! `valid : α → Δα → Prop`, and the diff/invert laws).
//!
//! This is the CONCEPTUAL framework's trait — NOT the Feldera `dbsp`
//! crate. Generated delta enums (`delta_generated.rs`) impl this trait;
//! the certified-delta tests execute the patch/validity shape on concrete
//! values (Stage E: the ChangeSpec laws, executed).
//!
//! Generality note: `patch : Row → Δ → Row` with `valid` keeping the base
//! mirrors the Lean class exactly — a change is only meaningful against a
//! base (Remove's `patch` keeps it; deletion is the key join's signal).

pub trait Change<Row> {
    /// Apply the change to a base row.
    fn patch(&self, base: &Row) -> Row;

    /// Validity: can this change patch rows of this shape at all?
    /// `Prop` in Lean — decidable to `bool` at the boundary.
    fn valid(&self, base: &Row) -> bool;
}

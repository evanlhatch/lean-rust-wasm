/-
# Faults — the faults lane (the failure-mode registry + the E-code allocation + the Rust face)

The lane's umbrella. Mining source: `legacy/lean/faults/Faults/` (the item +
registry + emitter shapes) RETARGETED onto the v3 doctrine:

- the E-codes ALLOCATE from the PERSISTED registry (kit/Kit/CodeRegistry.lean
  + notes/code-registry.txt — the coverage tooth's spec of record; the legacy
  `CodedRegistry.start` position discipline died: codes never derive from
  enumeration position or import order, notes/v3/05 §4);
- the registration rides Kit.Lane's substrate (`register_lane` — the mount
  mechanized once, 12 §2's steps 1–2);
- the payload types ride SchemaCore's CLOSED `Ty` (READ-ONLY — one type
  authority, no second universe);
- the Rust face renders through the Kit.Emit spine (the generated typed-error
  enum in fast-observe's `error!` MACRO syntax — the E-codes onto `#[code]`
  verbatim, the category↔policy axis by construction, ONE registry two
  faces; the nightly pin `crates/rust-toolchain.toml`; the causal-tree
  crossing is the named follow-up, notes/v3/12 §8 + design-faults §2.3).

Module graph (cone-ordered): Item (pure data) → Registry (the lane mount) →
Alloc (the persisted-registry allocation, pure + the IO loader) → Emit (the
Rust rendering + the emitter row) → Spec (the `@[fault]` rows) → Regen (the
env replay — the writer exe's and gen-check's ONE regen).
-/

import Faults.Item
import Faults.Registry
import Faults.Alloc
import Faults.Emit
import Faults.Spec
import Faults.Regen

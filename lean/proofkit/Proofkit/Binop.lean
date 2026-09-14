/-
# Proofkit.Binop — the binop contracts, `bv_decide`-proven (TOOLKIT 4)

The wasm-backend's `binop?` lowers `UInt64.add` to the WASM `i64.add`
instruction — TWO'S-COMPLEMENT WRAPPING, no overflow check. The
emitted-Rust/wasm consumer relies on that semantics silently; the
contract here states it Lean-side and closes it with `bv_decide`
(the fixed-width tactic — the flatland overflow/alignment rung), so the
semantics is a KERNEL-CHECKED FACT, not a comment.

Scope (v1): the add contracts, the demonstration site (the audit's
item: the binop lane had zero uses). More binops = more theorems here,
same shape.

Deliberately absent: an alignment contract — `i32.load8_u` (the tag
read) is byte-granular, no alignment obligation exists to state. The
first aligned load (`i32.load offset` with `align > 1`) adds its theorem
here.
-/

import Std.Tactic.BVDecide

namespace Proofkit

/-- THE CONTRACT: the emitted `i64.add` is wrapping — a wrapped add
    composes with the wrapped sub to recover the operand EXACTLY (the
    journal's revert path relies on the round-trip: the overflow is
    round-trip-safe). -/
theorem u64add_sub (a b : BitVec 64) : a + b - b = a := by
  bv_decide

/-- The reassociation license: wrapping add is associative — the
    backend's instruction reassociation is semantics-preserving. -/
theorem u64add_assoc (a b c : BitVec 64) :
    a + b + c = a + (b + c) := by
  bv_decide

end Proofkit

/-
# Guest.Std.ListOps — the guest-compilable list/numeric utilities

The std's SECOND surface: the utilities whose bodies are IN the guest's
CURRENT fragment (the object tag dispatch over `List`, the self-
recursive fap, the `binop?` scalar ops — the proven lowering shapes,
`GuestTests`' list/call lanes). Each function carries `@[guest_std]` —
the elaboration-time gate checks the ban closure at the decl
(pattern #13) — and its body is BOTH the native semantics (the
differential oracle) and a lowering TARGET (this slice's end-to-end
compiles + executes them; the agreement is pinned in GuestStdTests).

The honest boundary: `Nat` arithmetic is GMP-banned at the std level
(the ban), so the counters/sums ride `UInt64` — the guest's
fixed-width integer. Strings ride the lists UNOPENED (the cons cells'
heads are never read — no string op compiles yet, the StrOps
boundary).

The five questions (notes/v3/01-core.md):
- root: none — the guest std's list surface (Universe content).
- carrier grade: none — plain defs over core types.
- spine reading: the same dual face as StrOps (native oracle +
  lowering target).
- ladder rung: the spec theorems (below) are rung-1/2 hand proofs —
  the `rfl`/induction family, no obligations.
- gate row: `GuestStd`'s row in Gates.Packages.
-/

import LintKit.GuestGate

namespace GuestStd

/-- The u64 COUNT of a string list. Guest-legal length: core's
    `List.length` returns Nat — GMP, banned in the guest; the counter
    rides the raw u64 scalars (the cons/nil tag dispatch's walk — the
    backend's proven list-walk target). The heads ride UNOPENED (the
    honest boundary: reading a string field is the StrOps lane). -/
@[guest_std]
def listLenU64 : List String → UInt64
  | [] => 0
  | _ :: t => 1 + listLenU64 t

/-- The u64 SUM of a u64 list (the scalar fold — the binop surface's
    `UInt64.add` row at the cons arm). The dual face: the native
    oracle AND this slice's compiled end-to-end target. -/
@[guest_std]
def sumU64 : List UInt64 → UInt64
  | [] => 0
  | h :: t => h + sumU64 t

/-! ## The spec theorems (the property pins) -/

/-- The definitional face: nil pins. -/
theorem listLenU64_nil : listLenU64 [] = 0 := rfl

theorem sumU64_nil : sumU64 [] = 0 := rfl

/-- The definitional face: cons pins (the equation lemmas the tests'
    native evals and future consumers reduce by). -/
theorem listLenU64_cons (h : String) (t : List String) :
    listLenU64 (h :: t) = 1 + listLenU64 t := rfl

theorem sumU64_cons (h t : UInt64) (ts : List UInt64) :
    sumU64 (h :: t :: ts) = h + sumU64 (t :: ts) := rfl

/-- The u64 face of the succ cast (the wrap is exact — mod-2⁶⁴
    arithmetic on both sides; core has no `Nat.toUInt64_succ`). -/
theorem natToUInt64_succ (n : Nat) : (n + 1).toUInt64 = n.toUInt64 + 1 :=
  UInt64.toNat.inj (by
    have h : ((n + 1 : Nat).toUInt64 : UInt64).toNat
        = ((n.toUInt64 : UInt64) + 1).toNat := by simp
    exact h)

theorem listLenU64_eq_length (l : List String) :
    listLenU64 l = l.length.toUInt64 := by
  induction l with
  | nil => rfl
  | cons h t ih =>
      rw [listLenU64_cons, ih, List.length_cons, natToUInt64_succ,
        UInt64.add_comm]

/-- The sum IS the fold (the oracle tie over the ONE right fold). -/
theorem sumU64_eq_foldr (l : List UInt64) :
    sumU64 l = l.foldr (· + ·) 0 := by
  induction l with
  | nil => rfl
  | cons h t ih => rw [sumU64, List.foldr_cons, ih]

end GuestStd

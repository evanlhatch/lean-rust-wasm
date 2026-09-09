import WasmBackend
import WasmBackend.Check

/-!
# WasmBackend tests — the `@[guest]` gate's pure predicate

Positive + negative controls: the rejection path is OBSERVED, not
assumed. `checkExpr` is pure — no elaboration needed to test it.
Leaves are `.bvar 0` (a de Bruijn leaf — no constant-lookup coupling).
-/

open WasmBackend.Check Lean

def leaf : Expr := .bvar 0

-- Positive control: clean scalar code → no violations.
#guard (checkExpr (Expr.const ``UInt64 [])) == []

-- Negative control: the app of a banned const (Nat.add) → surfaces.
#guard (checkExpr (mkApp2 (.const ``Nat.add []) leaf leaf)) == ["Nat"]

-- String root → the violation.
#guard (checkExpr (.const ``String.length [])) == ["String"]

-- IO root → the violation.
#guard (checkExpr (.const ``IO.println [])) == ["IO"]

-- Dedup: two Nat uses → ONE violation (deduped by root).
#guard ((checkExpr (mkApp2 (.const ``Nat.add []) leaf leaf)).count "Nat") == 1

-- Mixed: Nat + IO → both, in scan order.
#guard (checkExpr (mkApp2 (.const ``IO.println []) (.const ``Nat.add []) leaf)) == ["Nat", "IO"]

-- Non-banned consts: clean.
#guard (checkExpr (mkApp2 (.const ``UInt64.add []) leaf leaf)) == []

-- The rejection path is OBSERVED: a banned root can't slip through —
-- every `@[guest]` def's failure mode is a listed violation (the elab
-- error renders `reasons`), and the backend's `unsupported` throw backs
-- the scan up for LCNF-only shapes.

-- The STD surface: match-only Nat is LEGAL (a Nat.zero/succ app is
-- ctor-shaped — the backend handles it via cases); arithmetic stays banned.
#guard (checkExprAt .std (mkApp2 (.const ``Nat.succ []) leaf leaf)) == []
#guard (checkExprAt .std (mkApp2 (.const ``Nat.add []) leaf leaf)) == ["Nat"]
#guard (checkExprAt .std (.const ``String.length [])) == []
#guard (checkExprAt .std (.const ``IO.println [])) == ["IO"]
-- The STRICT surface still bans everything the std surface allows.
#guard (checkExprAt .strict (mkApp2 (.const ``Nat.succ []) leaf leaf)) == ["Nat"]
#guard (checkExprAt .strict (.const ``String.length [])) == ["String"]

-- Bug 0.5: `reasons` renders at the attribute's OWN ban level. A
-- std-level Nat violation is ARITHMETIC (match-only Nat is std-legal),
-- so the std error must not show the strict bignum reason.
#guard (reasons .strict ["Nat"]) ==
  "- `Nat` — Nat is bignum (GMP) — the guest has fixed-width integers only (use UInt64/Int64)"
#guard (reasons .std ["Nat"]) ==
  "- `Nat` — Nat arithmetic is GMP — std code may only MATCH on Nat (zero/succ patterns)"
-- IO is banned at BOTH levels; the std render keeps the host-capability reason.
#guard (reasons .std ["IO"]) ==
  "- `IO` — IO is a host capability — guest functions must be pure over guestlang-std's WASI layer"

-- #guard-driven (elab-time); the exe entry point exists so the lakefile's
-- testDriver has a runnable target.
def main : IO UInt32 := pure 0

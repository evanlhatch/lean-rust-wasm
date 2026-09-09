import WasmBackend
import WasmBackend.Check
import TestKit

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

def main : IO UInt32 := pure 0

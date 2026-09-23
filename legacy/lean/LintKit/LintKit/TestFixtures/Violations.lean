/-
LintKit.TestFixtures.Violations — PLANTED violations for the LintKit
self-tests. This module is built (it is legal Lean) but is never imported by
the `LintKit` umbrella, so the `just lean-lint` gate never sees it;
`Tests/Main.lean` importModules it and asserts every linter fires exactly
where planted (positive controls) and nowhere else (negative controls are
the Clean fixture + the nolint/set_option opt-outs below).
-/
import LintKit.AxiomAllowlist

namespace LintKit.TestFixtures.Violations

/-- Planted: bare axiom outside the allowlist. -/
axiom evil : False

/-- Planted: depends on the planted axiom. -/
theorem usesEvil : False := evil

/-- Control: `native_decide`'s disclosed trust base is allowlisted. -/
theorem nativeOk : 100 < 200 := by native_decide

/-- Control: the `@[nolint]` opt-out silences the axiom linter here. -/
@[nolint linter.guestlang.axiomAllowlist "planted: exercises the nolint opt-out path"]
axiom evilNolint : 0 = 1

-- Control: the `set_option ... in` snapshot opt-out silences the linter.
set_option linter.guestlang.axiomAllowlist false in
axiom evilSnap : 0 = 1

/-- Planted: recursive def whose equation lemmas are not `@[simp]`. -/
def recNoSimp : Nat → Nat
  | 0 => 0
  | n + 1 => recNoSimp n

/-- Planted: duplicate body (binder name differs from `dupTwo` on purpose —
alpha-equivalence, not text equality, is what clusters). -/
def dupOne (n : Nat) : Nat := n + 41

/-- Planted: duplicate body. -/
def dupTwo (m : Nat) : Nat := m + 41

/-- Planted: cross-module duplicate of `LintKit.TestFixtures.Cross.dupCrossB`
(both root at `LintKit` but live in different modules). -/
def dupCrossA (y : Nat) : Nat := y + 99

/-- Planted (guestBan): IO is a host capability — banned at BOTH ban
levels. NOT `@[guest]`-marked: the attribute is the GATE mount (it would
hard-fail this fixture's build); the linter is the REPORT mount over the
same `guestBanCheck`. -/
def evilIo : IO Unit := IO.println "planted"

/-- Planted (guestBan): direct Nat ARITHMETIC — GMP, banned even at the
std level (match-only Nat is std-legal; `Nat.add` is not a match). -/
def evilNatArith : Nat := Nat.add 40 2

/-- Planted (upstreamDup): alpha-equivalent to core `Prod.swap` (non-trivial
body — the node count clears the filter). -/
def swapPlanted.{u, v} {α : Type u} {β : Type v} (p : α × β) : β × α := (p.snd, p.fst)

/-- Planted (bareChecker): a Bool check* def with NO companion bridge
theorem in this module. -/
def checkNoBridge (x : Nat) : Bool := x > 0

end LintKit.TestFixtures.Violations

/-- Planted (packageNamespace): helper parked in a CORE namespace —
the `Fin.ofList?` hazard (foreignRoots). -/
def List.badNs : Nat := 1

/-- Planted (packageNamespace): helper parked in ANOTHER WORKSPACE
PACKAGE's namespace. -/
def Substrait.strayFromLintKit : Nat := 2

/-
LintKit.TestFixtures.Clean — the negative-control fixture: well-formed code
on which NO guestlang linter may fire. If a linter fires here, the linter
(regression) is broken, not the fixture.
-/
import LintKit.Basic

namespace LintKit.TestFixtures.Clean

/-- Clean: no axioms at all. -/
theorem twoEqTwo : 2 = 2 := rfl

/-- Clean: `funext` uses only `Quot.sound` (allowlisted). -/
theorem extOk {α : Type} (f g : α → α) (h : ∀ x, f x = g x) : f = g := funext h

/-- Clean: recursive def carrying `@[simp]` (its equation lemmas are
registered with the default simp set via `toUnfoldThms`). -/
@[simp]
def recSimp : Nat → Nat
  | 0 => 0
  | n + 1 => recSimp n

/-- Clean: a structure — projections are unique bodies, no dup cluster. -/
structure Pair where
  fst : Nat
  snd : Nat

/-- Clean: distinct bodies, no dup cluster. -/
def addFortyOne (n : Nat) : Nat := n + 41
def addFortyTwo (n : Nat) : Nat := n + 42

end LintKit.TestFixtures.Clean

/-- Clean (packageNamespace, foreign rule): an unprefixed module-local name
is ordinary organization, not drift. -/
def unprefixedLocal : Nat := 7

/- Clean (packageNamespace, foreign rule): a module-LOCAL namespace —
neither a core root nor another workspace package. -/
namespace LocalMarker

def marker : Nat := 8

end LocalMarker

/- Clean (packageNamespace, foreign rule): a root owned by a constant of
the SAME module — projections of a locally declared structure live under
the structure's name without being foreign parking (core's `Order`
namespace is not the owner here; the local `structure Order` is). -/
structure Order where
  id : Nat

def Order.doubleId (o : Order) : Nat := o.id * 2

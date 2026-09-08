/-
# Dbsp.ChangeSpec — the change-structure specification layer (D18)

Adopts the autoinc-lean axiomatization as SPEC SHAPE (lean-v3 Part 3 /
D18 — pattern-match, not a dependency: their fork is better-quot-based and
grind-heavy; the classes are ~40 lines). This is the formal spec of
flatland's delta/Patches laws and the bridge between Dbsp's group deltas
and the engine's old-values-carrying `Change`.

Contents:

1. The change-structure classes: `Change` (patch + validity),
   `Difference` (compute a change between two values),
   `ChangeInversion` (every change inverts — rollback),
   `Noc`/`LawfulNoChange` (the identity change).
2. The **canonical group change structure**: every `AddCommGroup` is a
   change structure over itself with `patch = +`, `invert = -`,
   `diff new old = new - old`, all laws proved. This covers `ZSet A` and
   `Stream a` uniformly — the D/I inverse pair and the revert law are
   instances of `correct_invert`/`diff_correct`, not separate facts.
3. `PartialDerivSpec` — one-sided derivatives for binary operators (the
   join/binary-kernel spec template): `correct₁` says the δ₁-produced delta
   patches the output to the patched input's output. Proved: every
   `Bilinear` map yields one, with the one-sided deltas reading the OTHER
   side's current state — the spec-level content of the
   `Linearity.bilinear` classification (lean-v3 Part 4.1).

Deliberately not adopted from autoinc: `ChangeMonad`/`MonadRollback` (we
are pure; rollback is `ChangeInversion` + the overlay's segment rewind),
their `Operator`/`ΔRun.correct` monadic runner (our end-to-end shape is
`Flatland.Cascade` + the oracle conformance relation).
-/

import Dbsp.Relational

namespace Dbsp

/-- A change structure: changes patch values, with a validity predicate
    (which changes are meaningful for which values). -/
class Change (α Δα : Type) where
  patch : α → Δα → α
  valid : α → Δα → Prop

/-- Computing the change between two values. -/
class Difference (α Δα : Type) [Change α Δα] where
  /-- `diff new old`. -/
  diff : α → α → Δα
  diff_valid : ∀ old new, Change.valid old (diff new old)
  diff_correct : ∀ old new, Change.patch old (diff new old) = new

/-- Every change has an inverse: rollback. -/
class ChangeInversion (α Δα : Type) extends Change α Δα where
  invert : Δα → Δα
  valid_invert : ∀ (t : α) (Δt : Δα), Change.valid t Δt →
    Change.valid (Change.patch t Δt) (invert Δt)
  correct_invert : ∀ (t : α) (Δt : Δα), Change.valid t Δt →
    Change.patch (Change.patch t Δt) (invert Δt) = t

/-- The no-op change. -/
class Noc (Δα : Type) where
  noc : Δα

class LawfulNoChange (α Δα : Type) [Noc Δα] [Change α Δα] where
  valid_noc : ∀ t : α, Change.valid t (Noc.noc (Δα := Δα))
  correct_noc : ∀ t : α, Change.patch t (Noc.noc (Δα := Δα)) = t

/-! ## The canonical group change structure -/

/-- Every additive commutative group is a change structure over itself:
    patch by addition, every change valid. Covers `ZSet A` (multiplicity
    deltas) and `Stream a` (stream deltas) with one instance. -/
instance Change.groupSelf (α : Type) [AddCommGroup α] : Change α α where
  patch := (· + ·)
  valid := fun _ _ => True

instance Difference.groupSelf (α : Type) [AddCommGroup α] : Difference α α where
  diff new old := new - old
  diff_valid := fun _ _ => trivial
  diff_correct := fun old new => by
    show old + (new - old) = new
    abel

instance ChangeInversion.groupSelf (α : Type) [AddCommGroup α] : ChangeInversion α α where
  invert := Neg.neg
  valid_invert := fun _ _ _ => trivial
  correct_invert := fun t Δt _ => by
    show t + Δt + -Δt = t
    abel

instance Noc.groupSelf (α : Type) [AddCommGroup α] : Noc α where
  noc := 0

instance LawfulNoChange.groupSelf (α : Type) [AddCommGroup α] : LawfulNoChange α α where
  valid_noc := fun _ => trivial
  correct_noc := fun t => by
    show t + 0 = t
    rw [add_zero]

/-- Rollback of a group delta restores the value — the revert law,
    restated. This is the spec the engine's overlay-segment rewind
    satisfies. -/
theorem group_rollback {α : Type} [AddCommGroup α] (t Δt : α) :
    Change.patch (Change.patch t Δt) (-Δt) = t :=
  ChangeInversion.correct_invert t Δt trivial

/-! ## One-sided derivatives: the join/binary-kernel spec template -/

/-- The spec of a binary operator's one-sided derivatives. `δ₁` reads the
    OTHER side's current value (the maintained state); `correct₁` is the
    statement that the produced delta patches the output to the patched
    input's output. For linear f, `δ₁` ignores the other side (the
    `Linearity.linear` case); for bilinear f it needs it (the
    `Linearity.bilinear` case) — the type makes the dependency explicit. -/
structure PartialDerivSpec (α β γ Δα Δβ Δγ : Type)
    [Change α Δα] [Change β Δβ] [Change γ Δγ] where
  f : α → β → γ
  /-- Left-input derivative, reading the right side's current value. -/
  δ₁ : β → Δα → Δγ
  /-- Right-input derivative, reading the left side's current value. -/
  δ₂ : α → Δβ → Δγ
  valid₁ : ∀ x y dx, Change.valid x dx → Change.valid (f x y) (δ₁ y dx)
  valid₂ : ∀ x y dy, Change.valid y dy → Change.valid (f x y) (δ₂ x dy)
  correct₁ : ∀ x y dx, Change.valid x dx →
    Change.patch (f x y) (δ₁ y dx) = f (Change.patch x dx) y
  correct₂ : ∀ x y dy, Change.valid y dy →
    Change.patch (f x y) (δ₂ x dy) = f x (Change.patch y dy)

/-- **Every bilinear map is a partial-derivative spec over the group
    change structure.** The one-sided deltas are `f dx y` and `f x dy`:
    the delta flows against the other side's current state. This is the
    spec-level content of `bilinear_incremental`'s first two terms. -/
def Bilinear.toPartialDerivSpec {a b c : Type} [AddCommGroup a] [AddCommGroup b]
    [AddCommGroup c] {f : a → b → c} (hb : Bilinear f) :
    PartialDerivSpec a b c a b c where
  f := f
  δ₁ := fun y dx => f dx y
  δ₂ := fun x dy => f x dy
  valid₁ := fun _ _ _ _ => trivial
  valid₂ := fun _ _ _ _ => trivial
  correct₁ := fun x y dx _ => by
    show f x y + f dx y = f (x + dx) y
    exact (hb.1 x dx y).symm
  correct₂ := fun x y dy _ => by
    show f x y + f x dy = f x (y + dy)
    exact (hb.2 x y dy).symm

/-- The equi-join's one-sided-derivative spec: `equiJoin` is bilinear
    (`ZSet.equiJoin_bilinear`), so its delta form is certified by the
    group change structure + this construction. The full three-term
    stream-level form is `equiJoin_incremental`. -/
noncomputable def equiJoinDerivSpec {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (π1 : A → C) (π2 : B → C) :
    PartialDerivSpec (ZSet A) (ZSet B) (ZSet (A × B)) (ZSet A) (ZSet B) (ZSet (A × B)) :=
  (ZSet.equiJoin_bilinear π1 π2).toPartialDerivSpec

end Dbsp

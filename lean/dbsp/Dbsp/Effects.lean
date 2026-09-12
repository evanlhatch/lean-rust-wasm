/-
# Dbsp.Effects — the DeltaSystem influence algebra (refactor-guide 5.5.4)

Ported from flatland `Flatland/Effects.lean` (provenance: Core ECS Lemma
4.6 + Thm 4.5; Tasnim–Zhao read/write effects; DBSP operator
independence). A **delta system** is anything with a state type, a
location universe, and mutations carrying a STATIC WRITE SET, sound in one
way only — **write-disjoint mutations commute**. Everything downstream
(adjacent swap, bubble, permutation invariance of conflict-free batches)
is derived ONCE over the interface.

Different claim from `Dbsp.Replicas` (group-commutes vs
disjoint-write-commutes): this one works for NON-commutative mutations
whose write sets are statically disjoint.

Port adjustments vs flatland:
- flatland's hand-rolled `pairwise_perm` induction is REPLACED by core's
  `List.Perm.pairwise` (verified present in toolchain v4.33.0,
  `Init/Data/List/Perm.lean`).
- `LocDisjoint` is mathlib's `List.Disjoint` (an abbrev — the standard
  name for the same ∀x, x∈l₁→x∈l₂→False notion; the local alias stays
  because the interface speaks `List Loc` write sets directly).
- The demo instance is generic (flatland's `changeAtomSystem` was
  game-shaped): point deltas on `Nat →₀ Int` finsupport maps, write set =
  support of the delta.

Deliberately absent: what a location is, how mutations are encoded, where
batches come from. Those are instance/emitter concerns.
-/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Single
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring

namespace Dbsp

/-! ### Location disjointness -/

/-- Two lists share no element. (Mathlib's `List.Disjoint`, under the
    interface's local name — the deltas' write sets are `List Loc`, so
    disjointness is stated directly on lists.) -/
abbrev LocDisjoint {α : Type} (l₁ l₂ : List α) : Prop := List.Disjoint l₁ l₂

theorem LocDisjoint.symm {α : Type} {l₁ l₂ : List α}
    (h : LocDisjoint l₁ l₂) : LocDisjoint l₂ l₁ :=
  fun _ ha₁ ha₂ => h ha₂ ha₁

/-! ### The interface -/

/-- A delta system: mutations over state `S` with static write sets over
    locations `Loc`, sound in one way — disjoint influence commutes. -/
class DeltaSystem (S Loc : Type) where
  /-- The mutation representation (ZSet entry, patch tuple…). -/
  Mut : Type
  /-- Deterministic transition. -/
  applyM : Mut → S → S
  /-- Static influence: locations possibly written. -/
  writesOf : Mut → List Loc
  /-- THE contract (Core ECS Lemma 4.6 shape). Each instance proves it
      once against its own semantics. -/
  disjoint_commutes :
    ∀ (m₁ m₂ : Mut), LocDisjoint (writesOf m₁) (writesOf m₂) →
      ∀ s, applyM m₁ (applyM m₂ s) = applyM m₂ (applyM m₁ s)

variable {S Loc : Type} {sys : DeltaSystem S Loc}

/-! ### Derived laws -/

/-- Staged application: fold a batch in order. -/
def applySeq (ms : List sys.Mut) (s : S) : S :=
  ms.foldl (fun acc m => sys.applyM m acc) s

theorem applySeq_cons (m : sys.Mut) (ms : List sys.Mut) (s : S) :
    applySeq (m :: ms) s = applySeq ms (sys.applyM m s) := rfl

theorem applySeq_append (a b : List sys.Mut) (s : S) :
    applySeq (a ++ b) s = applySeq b (applySeq a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons x _ ih => exact ih (sys.applyM x s)

/-- **Adjacent transposition** at any position. -/
theorem applySeq_swap_at (l₁ : List sys.Mut) (f g : sys.Mut)
    (l₂ : List sys.Mut)
    (hd : LocDisjoint (sys.writesOf f) (sys.writesOf g)) :
    applySeq (l₁ ++ f :: g :: l₂) = applySeq (l₁ ++ g :: f :: l₂) := by
  funext s
  rw [applySeq_append, applySeq_append, applySeq_cons, applySeq_cons]
  exact congrArg (applySeq l₂)
    (sys.disjoint_commutes f g hd (applySeq l₁ s)).symm

/-- **Bubble**: a mutation moves past an entire conflict-free block. -/
theorem applySeq_bubble (m : sys.Mut) (blk : List sys.Mut)
    (hdis : ∀ z ∈ blk, LocDisjoint (sys.writesOf m) (sys.writesOf z)) :
    applySeq (m :: blk) = applySeq (blk ++ [m]) := by
  induction blk with
  | nil => rfl
  | cons y rest ih =>
      funext s
      calc
        applySeq (m :: y :: rest) s
            = applySeq (y :: m :: rest) s := by
                simpa using congrFun
                  (applySeq_swap_at [] m y rest (hdis y (List.mem_cons_self ..))) s
        _ = applySeq (m :: rest) (sys.applyM y s) := rfl
        _ = applySeq (rest ++ [m]) (sys.applyM y s) := congrFun
            (ih (fun z hz => hdis z (List.mem_cons_of_mem _ hz))) (sys.applyM y s)

/-- Bubble with an arbitrary prefix (the usable form). -/
theorem applySeq_bubble_prefix (l₁ : List sys.Mut) (m : sys.Mut)
    (blk : List sys.Mut)
    (hdis : ∀ z ∈ blk, LocDisjoint (sys.writesOf m) (sys.writesOf z)) :
    applySeq (l₁ ++ m :: blk) = applySeq (l₁ ++ blk ++ [m]) := by
  funext s
  have hb := applySeq_bubble m blk hdis
  rw [applySeq_append, List.append_assoc, applySeq_append]
  exact congrFun hb (applySeq l₁ s)

/-! ### The payoff -/

/-- **Permutation invariance of conflict-free batches**: a pairwise
    write-disjoint batch computes the same final state under ANY ordering.
    Batch ≡ sequential. Fire-once-per-stage, parallel maps, unordered
    accumulation: all this theorem wearing different hats.

    The pairwise-transfers-along-Perm step is core's `List.Perm.pairwise`
    (flatland proved it by hand as `pairwise_perm`; core has it). -/
theorem applySeq_perm {ms₁ ms₂ : List sys.Mut} (hp : ms₁.Perm ms₂)
    (hpair : ms₁.Pairwise
      (fun a b => LocDisjoint (sys.writesOf a) (sys.writesOf b)))
    (s : S) : applySeq ms₁ s = applySeq ms₂ s := by
  induction hp generalizing s with
  | nil => rfl
  | @cons x l _ _ ih =>
      rw [applySeq_cons, applySeq_cons]
      exact ih hpair.tail (sys.applyM x s)
  | @swap x y l =>
      -- core `Perm.swap`: ms₁ = y :: x :: l, so hpair's head is y
      have hxy : LocDisjoint (sys.writesOf x) (sys.writesOf y) :=
        (List.rel_of_pairwise_cons hpair (List.mem_cons_self ..)).symm
      rw [applySeq_cons, applySeq_cons, applySeq_cons, applySeq_cons]
      exact congrArg (applySeq l) (sys.disjoint_commutes x y hxy s)
  | trans h₁ _ ih₁ ih₂ =>
      rw [ih₁ hpair s]
      exact ih₂ (h₁.pairwise hpair (fun hd => hd.symm)) s

/-! ### Demo instance: point deltas on finsupport maps

Adaptation of flatland's `changeAtomSystem` to a generic storage model:
state is a `Nat →₀ Int` value map, a delta is itself a finitely supported
map applied by addition, and its write set is its support. Disjoint
supports commute pointwise on `Int`. -/

-- the `warn.classDefReducibility` warning is silenced to say so.
set_option warn.classDefReducibility false in
/-- Point-update deltas on `Nat →₀ Int`. The ONE `disjoint_commutes`
    proof reduces to case-splitting on support membership and `ring`.
    Semireducible on purpose: the system is passed explicitly
    (`self := …`), never found by instance search. -/
noncomputable def pointDeltaSystem : DeltaSystem (Nat →₀ Int) Nat where
  Mut := Nat →₀ Int
  applyM d s := d + s
  writesOf d := d.support.toList
  disjoint_commutes d₁ d₂ hd s := by
    ext n
    simp only [Finsupp.add_apply]
    by_cases h₁ : n ∈ d₁.support <;> by_cases h₂ : n ∈ d₂.support
    · exact (hd (Finset.mem_toList.mpr h₁) (Finset.mem_toList.mpr h₂)).elim
    · rw [Finsupp.notMem_support_iff.mp h₂]; ring
    · rw [Finsupp.notMem_support_iff.mp h₁]; ring
    · rw [Finsupp.notMem_support_iff.mp h₁, Finsupp.notMem_support_iff.mp h₂]

/-- Compile-time witness (exercised on every build): two point deltas
    with disjoint singleton supports commute — `applySeq_perm`
    instantiated with `Perm.swap`, the pairwise proof discharged against
    the concrete supports. -/
example :
    applySeq (sys := pointDeltaSystem)
        [Finsupp.single 1 (7 : Int), Finsupp.single 0 (9 : Int)] 0 =
      applySeq (sys := pointDeltaSystem)
        [Finsupp.single 0 (9 : Int), Finsupp.single 1 (7 : Int)] 0 := by
  refine applySeq_perm (List.Perm.swap (Finsupp.single 0 (9 : Int))
    (Finsupp.single 1 (7 : Int)) []) ?_ 0
  refine List.pairwise_cons.mpr ⟨?_, ?_⟩
  · intro y hy
    obtain rfl := List.mem_singleton.mp hy
    intro x hx₁ hx₂
    rw [show DeltaSystem.writesOf (self := pointDeltaSystem)
          (Finsupp.single 1 (7 : Int))
        = (Finsupp.single 1 (7 : Int)).support.toList from rfl,
        Finset.mem_toList, Finsupp.mem_support_single] at hx₁
    rw [show DeltaSystem.writesOf (self := pointDeltaSystem)
          (Finsupp.single 0 (9 : Int))
        = (Finsupp.single 0 (9 : Int)).support.toList from rfl,
        Finset.mem_toList, Finsupp.mem_support_single] at hx₂
    exact absurd (hx₁.1.symm.trans hx₂.1) (by decide)
  · exact List.pairwise_cons.mpr
      ⟨fun y hy => (List.not_mem_nil hy).elim, List.Pairwise.nil⟩

end Dbsp

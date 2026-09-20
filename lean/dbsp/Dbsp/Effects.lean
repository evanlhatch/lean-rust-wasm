/-
# Dbsp.Effects — the DeltaSystem influence algebra (refactor-guide 5.5.4)

Ported from flatland `Flatland/Effects.lean` (provenance: Core ECS Lemma
4.6 + Thm 4.5; Tasnim–Zhao read/write effects; DBSP operator
independence). A **delta system** is anything with a state type, a
location universe, and mutations carrying a STATIC WRITE SET, sound in one
way only — **write-disjoint mutations commute**. Everything downstream
(adjacent swap, bubble, permutation invariance of conflict-free batches)
is derived ONCE over the interface.

W4.3: `Mut` is a PARAMETER and `DeltaSystem` EXTENDS `Change S Mut` —
application IS patching — so a delta system is a change structure with a
disjoint-commutes law, and the `ChangeSpec` vocabulary (validity,
inversion, noc) composes with it.

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

module

public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Ring
public import Dbsp.ChangeSpec

-- The shared delta/lens law shape (`DisjointCommute`): the instance
-- below cites it. Kit is core-only — no mathlib leak (W5.4 constraint
-- 14), so the public import is safe for dbsp's downstream.
public import CodegenCore.Kit

-- W5.4 module discipline: all declarations public; bodies exposed
-- (defs/abbrevs/instances must reduce across module boundaries).
@[expose] public section

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
class DeltaSystem (S Loc Mut : Type) extends Change S Mut where
  /-- Static influence: locations possibly written. -/
  writesOf : Mut → List Loc
  /-- THE contract (Core ECS Lemma 4.6 shape). Each instance proves it
      once against its own semantics. -/
  disjoint_commutes :
    ∀ (m₁ m₂ : Mut), LocDisjoint (writesOf m₁) (writesOf m₂) →
      ∀ (s : S), Change.patch (Change.patch s m₂) m₁ = Change.patch (Change.patch s m₁) m₂

variable {S Loc Mut : Type} {sys : DeltaSystem S Loc Mut}

/-- THE unification (the lens/delta law family, one shape): a delta
    system IS a `CodegenCore.DisjointCommute` at `L := List Loc` — a
    mutation's location IS its static write set, `Disjoint` =
    `LocDisjoint`, and the law field CITES `disjoint_commutes` (the
    `.symm` aligns the two shapes' side order; no re-proof). -/
instance instDisjointCommuteOfDeltaSystem {S Loc Mut : Type}
    [sys : DeltaSystem S Loc Mut] :
    CodegenCore.DisjointCommute S (List Loc) Mut where
  apply := sys.patch
  loc := sys.writesOf
  Disjoint := LocDisjoint
  disjoint_commutes m₁ m₂ hd s := (sys.disjoint_commutes m₁ m₂ hd s).symm

/-! ### Derived laws -/

/-- Staged application: fold a batch in order. `sys` is EXPLICIT: `Loc`
    appears only in the system, so instance/implicit search cannot
    determine it from the batch or the state. -/
def applySeq (sys : DeltaSystem S Loc Mut) (ms : List Mut) (s : S) : S :=
  ms.foldl (fun acc m => sys.patch acc m) s

theorem applySeq_cons (m : Mut) (ms : List Mut) (s : S) :
    applySeq sys (m :: ms) s = applySeq sys ms (sys.patch s m) := rfl

theorem applySeq_append (a b : List Mut) (s : S) :
    applySeq sys (a ++ b) s = applySeq sys b (applySeq sys a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons x _ ih => exact ih (sys.patch s x)

/-- **Adjacent transposition** at any position. -/
theorem applySeq_swap_at (l₁ : List Mut) (f g : Mut)
    (l₂ : List Mut)
    (hd : LocDisjoint (sys.writesOf f) (sys.writesOf g)) :
    applySeq sys (l₁ ++ f :: g :: l₂) = applySeq sys (l₁ ++ g :: f :: l₂) := by
  funext s
  rw [applySeq_append, applySeq_append, applySeq_cons, applySeq_cons]
  exact congrArg (applySeq sys l₂)
    (sys.disjoint_commutes f g hd (applySeq sys l₁ s)).symm

/-- **Bubble**: a mutation moves past an entire conflict-free block. -/
theorem applySeq_bubble (m : Mut) (blk : List Mut)
    (hdis : ∀ z ∈ blk, LocDisjoint (sys.writesOf m) (sys.writesOf z)) :
    applySeq sys (m :: blk) = applySeq sys (blk ++ [m]) := by
  induction blk with
  | nil => rfl
  | cons y rest ih =>
      funext s
      calc
        applySeq sys (m :: y :: rest) s
            = applySeq sys (y :: m :: rest) s := by
                simpa using congrFun
                  (applySeq_swap_at [] m y rest (hdis y (List.mem_cons_self ..))) s
        _ = applySeq sys (m :: rest) (sys.patch s y) := rfl
        _ = applySeq sys (rest ++ [m]) (sys.patch s y) := congrFun
            (ih (fun z hz => hdis z (List.mem_cons_of_mem _ hz))) (sys.patch s y)

/-- Bubble with an arbitrary prefix (the usable form). -/
theorem applySeq_bubble_prefix (l₁ : List Mut) (m : Mut)
    (blk : List Mut)
    (hdis : ∀ z ∈ blk, LocDisjoint (sys.writesOf m) (sys.writesOf z)) :
    applySeq sys (l₁ ++ m :: blk) = applySeq sys (l₁ ++ blk ++ [m]) := by
  funext s
  have hb := applySeq_bubble m blk hdis
  rw [applySeq_append, List.append_assoc, applySeq_append]
  exact congrFun hb (applySeq sys l₁ s)

/-! ### The payoff -/

/-- **Permutation invariance of conflict-free batches**: a pairwise
    write-disjoint batch computes the same final state under ANY ordering.
    Batch ≡ sequential. Fire-once-per-stage, parallel maps, unordered
    accumulation: all this theorem wearing different hats.

    The pairwise-transfers-along-Perm step is core's `List.Perm.pairwise`
    (flatland proved it by hand as `pairwise_perm`; core has it). -/
theorem applySeq_perm {ms₁ ms₂ : List Mut} (hp : ms₁.Perm ms₂)
    (hpair : ms₁.Pairwise
      (fun a b => LocDisjoint (sys.writesOf a) (sys.writesOf b)))
    (s : S) : applySeq sys ms₁ s = applySeq sys ms₂ s := by
  induction hp generalizing s with
  | nil => rfl
  | @cons x l _ _ ih =>
      rw [applySeq_cons, applySeq_cons]
      exact ih hpair.tail (sys.patch s x)
  | @swap x y l =>
      -- core `Perm.swap`: ms₁ = y :: x :: l, so hpair's head is y
      have hxy : LocDisjoint (sys.writesOf x) (sys.writesOf y) :=
        (List.rel_of_pairwise_cons hpair (List.mem_cons_self ..)).symm
      rw [applySeq_cons, applySeq_cons, applySeq_cons, applySeq_cons]
      exact congrArg (applySeq sys l) (sys.disjoint_commutes x y hxy s)
  | trans h₁ _ ih₁ ih₂ =>
      rw [ih₁ hpair s]
      exact ih₂ (h₁.pairwise hpair (fun hd => hd.symm)) s

end Dbsp

end -- @[expose] public section

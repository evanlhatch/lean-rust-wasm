/-
# Effects.Basic — the closed effect lattice + the annotation discipline

The effects lane's foundation (notes/v3/08-capabilities.md §8): the
CLOSED effect lattice (read/write/guestCap/fail/consume/clock/hostIO/
observe — eight atoms, closed like the Ty universe, pattern #15: a new
atom breaks every exhaustive fold), the effect ROWS as finite sets with
the lattice laws, and the effect-annotated computation shape.

**The split (D7, the review's correction):** effects are UPPER BOUNDS
(set union); resources are USAGE ACCOUNTING with context splitting —
union cannot enforce linearity (`{consume h} ∪ {consume h}` loses the
double-spend). This module owns the upper-bound half; the resource
discipline is `Effects.Resource`'s, and the two NEVER collapse (the
pin: `Effects.row_blind_to_double_spend`).

Honest minimal — this is an ANNOTATION discipline, not an interpreter:

- a computation carries its row as a TYPE INDEX; composition (`bind`)
  computes the join; the sub-effect discipline is the honest partial
  order (`Row.le`, ⊆ over membership);
- the check boundary (`Comp.check`) carries the allowance as a PROOF
  argument — an over-permissive composition has no proof of
  `Row.le row allowed`, and the declaration FAILS TO ELABORATE (the
  teeth: `#guard_msgs` pins in EffectsTests);
- the rows' SEMANTICS is membership: two rows with the same members
  are the same row (the finite-set reading), so the lattice laws are
  stated over `Row.sameMembers`, never over list syntax. Duplicates are
  representable but semantically inert — every law and the order read
  membership only. The canonical-rep upgrade (06 §7c) lands with the
  first consumer that needs syntactic canonicity (a row byte-tie, say);
  none exists here (the leftover rule).

Named exclusions (each lands with its first consumer + its named law):
effect HANDLERS/interpreters (the row is never executed here), the
wp-composition of contracted lanes (08 §36 — the contracts wave's),
row polymorphism/quantification (the closed-row discipline first),
the registry-driven row DERIVATION (08 §8's "rows derive from registry
items" — the registry lane's mount, not the lattice's).

Doctrine slots (notes/v3/01-core.md, the five questions):
- **Root**: Universe (finite data: the closed atom enum + the row sets)
  — effects are annotation data, NOT a root; the `consume` atom's
  accounting lives in `Effects.Resource` (01 §1: resources are not a
  root — a Change instance).
- **Carrier grade**: the type-level annotation (the row as index) —
  same program, plus the declared upper bound (01 §4's discipline:
  annotation, never control).
- **Spine reading**: none yet — the registry-derived rows are the
  spine reading when the registry lane mounts.
- **Ladder rung**: hand theorems of the small generic kind (01 §7) —
  the lattice laws + the order's facts, proved once, membership-level,
  all constructive.
- **Gate rows**: EffectsTests' axiom self-check + the cone table row
  (`Effects` = C1-adjacent machinery: substrate for the domain lanes'
  composition joins, imports Kit only).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Effects

/-! ## The closed atoms -/

/-- The closed effect lattice's atoms (08 §8). CLOSED: a new atom is a
    doctrine act (pattern #15), never a local extension. -/
inductive Effect where
  | read     -- reads the shared state
  | write    -- writes the shared state
  | guestCap -- exercises a guest capability
  | fail     -- may report a typed failure
  | consume  -- consumes a resource (the ACCOUNTING is Resource's — D7)
  | clock    -- reads the logical/global clock
  | hostIO   -- crosses the host boundary
  | observe  -- emits an observation (04 §4's observer surface)
  deriving DecidableEq, Repr, Inhabited

/-! ## The set-union discipline (shared with the footprint's key join) -/

/-- The dedup union for finite enumerated sets — THE set-union
    discipline, one mechanism, two instances: the effect rows
    (`Effects.Row`) and the footprint key sets (`Effects.Footprint`).
    Equation-lemma-friendly (pattern #12): recursion on the second
    list, membership-checked cons. -/
def unionMem {α : Type} [DecidableEq α] : List α → List α → List α
  | a, [] => a
  | a, e :: b => unionMem (if e ∈ a then a else e :: a) b

/-- One union step: membership through the membership-checked cons.
    (The helper keeps `mem_unionMem` free of mixed unfolded forms.) -/
@[nolint linter.guestlang.zeroCitation "load-bearing: this module's helper — consumed by `mem_unionMem`'s proof (THE membership law the rows and the footprint key join cite)"]
theorem mem_step {α : Type} [DecidableEq α] (x e : α) (a : List α) :
    x ∈ (if e ∈ a then a else e :: a) ↔ x ∈ a ∨ x = e := by
  by_cases h : e ∈ a
  · rw [if_pos h]
    constructor
    · exact fun hx => Or.inl hx
    · intro hx
      cases hx with
      | inl hx' => exact hx'
      | inr he => rw [he]; exact h
  · rw [if_neg h, List.mem_cons]
    constructor
    · intro hx
      cases hx with
      | inl he => exact Or.inr he
      | inr hm => exact Or.inl hm
    · intro hx
      cases hx with
      | inl hm => exact Or.inr hm
      | inr he => exact Or.inl he

/-- THE membership law of the union: membership in the join is
    membership in either side. Everything lattice-shaped follows. -/
theorem mem_unionMem {α : Type} [DecidableEq α] (x : α) (a b : List α) :
    x ∈ unionMem a b ↔ x ∈ a ∨ x ∈ b := by
  induction b generalizing a with
  | nil => simp [unionMem]
  | cons e b ih =>
    show x ∈ unionMem (if e ∈ a then a else e :: a) b
      ↔ x ∈ a ∨ x ∈ e :: b
    rw [ih (if e ∈ a then a else e :: a), mem_step x e a, List.mem_cons]
    constructor
    · intro hx
      cases hx with
      | inl h' => cases h' with
        | inl h'' => exact Or.inl h''
        | inr h'' => exact Or.inr (Or.inl h'')
      | inr h' => exact Or.inr (Or.inr h')
    · intro hx
      cases hx with
      | inl h' => exact Or.inl (Or.inl h')
      | inr h' => cases h' with
        | inl h'' => exact Or.inl (Or.inr h'')
        | inr h'' => exact Or.inr h''

/-! ## The rows (finite effect sets) -/

/-- An effect row: a finite set of atoms, as a list. The SEMANTICS is
    membership (`Row.le`, the laws); the list is a representation —
    see the header's honest-minimal note. -/
abbrev Row := List Effect

namespace Row

/-- The order: the sub-effect discipline. `Row.le a b` — the row `b`
    permits everything `a` does (⊆ over membership). -/
def le (a b : Row) : Prop := ∀ e, e ∈ a → e ∈ b

/-- Membership decision for the order's decidability. -/
def memB (e : Effect) : Row → Bool
  | [] => false
  | g :: r => if g = e then true else memB e r

@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `Row.sub_iff_le`'s proof in this module (the decidability behind the check boundary's elaboration-time teeth)"]
theorem memB_iff (e : Effect) (r : Row) : memB e r = true ↔ e ∈ r := by
  cases r with
  | nil => simp [memB]
  | cons g r =>
    simp only [memB]
    split
    · next h => simp [h]
    · next h =>
      constructor
      · exact fun hx => List.mem_cons_of_mem g ((memB_iff e r).mp hx)
      · intro hx
        cases List.mem_cons.mp hx with
        | inl he => exact absurd he.symm h
        | inr hm => exact (memB_iff e r).mpr hm

/-- The decidable subset check backing the order's elaboration-time
    proofs (`by decide` over `Row.le a b`). -/
def sub (a b : Row) : Bool :=
  match a with
  | [] => true
  | e :: r => memB e b && sub r b

@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's `Decidable (Row.le)` instance (the check boundary's teeth) + pinned by EffectsTests.Axioms (#print axioms)"]
theorem sub_iff_le (a b : Row) : sub a b = true ↔ le a b := by
  cases a with
  | nil => simp [sub, le, List.not_mem_nil]
  | cons e r =>
    simp only [sub, Bool.and_eq_true, memB_iff, List.mem_cons, le]
    constructor
    · intro h x hx
      cases hx with
      | inl he => exact by rw [he]; exact h.1
      | inr hr => exact (sub_iff_le r b).mp h.2 x hr
    · intro h
      exact ⟨h e (Or.inl rfl),
        (sub_iff_le r b).mpr (fun x hx => h x (Or.inr hx))⟩

/-- The order decides — the check boundary's proof obligations
    elaborate by `decide` (and REFUSE when false: the teeth). -/
instance (a b : Row) : Decidable (le a b) :=
  if h : sub a b = true then
    .isTrue ((sub_iff_le a b).mp h)
  else
    .isFalse (fun hn => h ((sub_iff_le a b).mpr hn))

/-- The join: the set union (the composition's lattice operation —
    `Effects.unionMem`, cited). -/
def join (a b : Row) : Row := unionMem a b

@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests (mem_join_both/mem_join_absent cite it); THE membership law of the rows' join — the semantics every lattice law reads"]
theorem mem_join (x : Effect) (a b : Row) :
    x ∈ join a b ↔ x ∈ a ∨ x ∈ b := mem_unionMem x a b

/-- Row equality as the finite-set reading: same members, same row. -/
def sameMembers (a b : Row) : Prop := ∀ e, e ∈ a ↔ e ∈ b

/-! ### The lattice laws (stated over the semantics, never the syntax) -/

/-- The empty row permits nothing — the pure discipline. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by this module's proofs of `Row.join_nil_right`/`Row.join_nil_left` (the lattice's law set)"]
theorem mem_nil (x : Effect) : x ∈ ([] : Row) ↔ False := by
  simp

@[nolint linter.guestlang.zeroCitation "public API: the lattice's law set (the seed's API — the empty-row law of the pure discipline; the row-handler/interpreter layer is the header's named first consumer)"]
theorem join_nil_right (a : Row) : sameMembers (join a []) a := by
  intro x
  rw [mem_join, mem_nil]
  constructor
  · intro hx
    cases hx with
    | inl hx' => exact hx'
    | inr hf => exact hf.elim
  · exact fun hx => Or.inl hx

@[nolint linter.guestlang.zeroCitation "public API: the lattice's law set (the seed's API — the empty-row law of the pure discipline; the row-handler/interpreter layer is the header's named first consumer)"]
theorem join_nil_left (a : Row) : sameMembers (join [] a) a := by
  intro x
  rw [mem_join, mem_nil]
  constructor
  · intro hx
    cases hx with
    | inl hf => exact hf.elim
    | inr hx' => exact hx'
  · exact fun hx => Or.inr hx

/-- Idempotence: joining a row with itself changes nothing. THE D7 pin's
    engine — see `Effects.row_blind_to_double_spend`. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests.Axioms (#print axioms); THE D7 pin's engine — `Effects.row_blind_to_double_spend` consumes it in this module"]
theorem join_idem (a : Row) : sameMembers (join a a) a := by
  intro x
  rw [mem_join]
  exact ⟨fun hx => hx.elim id id, fun hx => Or.inl hx⟩

/-- Commutativity: the join is the union, order-free. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests.Axioms (#print axioms); the join's commutativity law (the row is a finite set — order-free)"]
theorem join_comm (a b : Row) : sameMembers (join a b) (join b a) := by
  intro x
  rw [mem_join, mem_join]
  exact ⟨Or.symm, Or.symm⟩

/-- Associativity: the join composes in either nesting — the
    composition discipline's law (nested programs' rows join either
    way). -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests.Axioms (#print axioms); the nested-composition law (a nested program's rows join either way)"]
theorem join_assoc (a b c : Row) :
    sameMembers (join (join a b) c) (join a (join b c)) := by
  intro x
  simp only [mem_join]
  constructor
  · intro hx
    cases hx with
    | inl h => cases h with
      | inl h' => exact Or.inl h'
      | inr h' => exact Or.inr (Or.inl h')
    | inr h => exact Or.inr (Or.inr h)
  · intro hx
    cases hx with
    | inl h => exact Or.inl (Or.inl h)
    | inr h => cases h with
      | inl h' => exact Or.inl (Or.inr h')
      | inr h' => exact Or.inr h'

/-! ### The order's facts -/

@[nolint linter.guestlang.zeroCitation "public API: the order's facts (the seed's law set — the sub-effect discipline's reflexivity; the row-polymorphism follow-up is the header's named exclusion)"]
theorem le_refl (a : Row) : le a a := fun _ hx => hx

@[nolint linter.guestlang.zeroCitation "public API: the order's facts (the seed's law set — the transitivity the registry-driven row derivation composes through, 08 §8's named follow-up)"]
theorem le_trans {a b c : Row} (h₁ : le a b) (h₂ : le b c) : le a c :=
  fun _ hx => h₂ _ (h₁ _ hx)

/-- The join's parts sit below the join. -/
@[nolint linter.guestlang.zeroCitation "public API: the order's facts (the join's upper-bound laws — the composition discipline's seed API; the tests' sweep pins them at the data level via `decide`)"]
theorem le_join_left (a b : Row) : le a (join a b) :=
  fun e hx => (mem_join e a b).mpr (Or.inl hx)

@[nolint linter.guestlang.zeroCitation "public API: the order's facts (the join's upper-bound laws — the composition discipline's seed API; the tests' sweep pins them at the data level via `decide`)"]
theorem le_join_right (a b : Row) : le b (join a b) :=
  fun e hx => (mem_join e a b).mpr (Or.inr hx)

/-- THE least-upper-bound law: a composition joins its parts' rows, and
    the join permits exactly what the union of the allowances does — an
    over-permissive allowance is detectable, an under-permissive one
    refuses (the check boundary's teeth). -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests.Axioms (#print axioms); THE least-upper-bound law (the check boundary's over/under-permissive teeth)"]
theorem join_le {a b c : Row} (h₁ : le a c) (h₂ : le b c) : le (join a b) c := by
  intro x hx
  rcases (mem_join x a b).mp hx with hx | hx
  · exact h₁ _ hx
  · exact h₂ _ hx

end Row

/-! ## The effect-annotated computation -/

/-- The effect-annotated computation: the row is an INDEX — the type
    carries the declared upper bound alongside the value. The honest
    minimal annotation discipline: the row never executes, filters, or
    controls the value (annotation, never control — an interpreter or
    handler layer is a named exclusion; the wp-composition is the
    contracts wave's). The enforcement surface is `Comp.check`: a
    forged row passes review-by-construction only, and every check
    boundary demands the sub-effect proof. -/
structure Comp (r : Row) (α : Type) : Type where
  /-- The value: the computation's result, untouched by the row. -/
  val : α

namespace Comp

/-- The pure step: the empty row permits nothing. -/
def pure {α : Type} (a : α) : Comp [] α := ⟨a⟩

/-- The composition: the value threads; the rows JOIN (the lattice's
    operation, computed at the type level — the composition discipline:
    a nested program's row is the union of its parts', never a silent
    widening). -/
def bind {r₁ r₂ : Row} {α β : Type} (c : Comp r₁ α)
    (f : α → Comp r₂ β) : Comp (Row.join r₁ r₂) β :=
  ⟨(f c.val).val⟩

/-- THE check boundary: a computation is used where its declared row is
    a sub-effect of the allowance. The proof is an ELABORATION-TIME
    obligation (`Row.le` decides) — an over-permissive composition has
    no proof, and the declaration fails to elaborate (the teeth:
    EffectsTests' `#guard_msgs` pins). -/
def check {r allowed : Row} {α : Type} (c : Comp r α)
    (_h : Row.le r allowed) : Comp allowed α := ⟨c.val⟩

end Comp

/-! ## The split, pinned at the lattice (D7) -/

/-- THE D7 pin: the effect row is BLIND to the double-spend. Joining a
    consume row with itself is the same consume row (union idempotent
    at the atom) — the lost usage accounting is exactly what the row
    CANNOT express, and why `Effects.Resource` exists as a separate
    structure. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests (d7_theorem_pin) + EffectsTests.Axioms (#print axioms); THE D7 split pin — why Resource exists as a separate structure"]
theorem row_blind_to_double_spend :
    Row.sameMembers
      (Row.join [Effect.consume] [Effect.consume])
      [Effect.consume] :=
  Row.join_idem _

end Effects
